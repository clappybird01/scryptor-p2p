'use strict';
// ═══════════════════════════════════════════════════════════
//  GLOBALS & CONSTANTS
// ═══════════════════════════════════════════════════════════
const te = new TextEncoder();
const td = new TextDecoder();

const AAD_MESSAGE = te.encode("ScryptorP2P-MSG-v2");
const AAD_FILE    = te.encode("ScryptorP2P-FILE-v2");
const AAD_SYS     = te.encode("ScryptorP2P-SYS-v2"); // silent ratchet-priming envelope, never shown/stored
const DB_NAME     = 'ScryptorDB';
const DB_VERSION  = 1;
const SIGNALING_TOPIC = "scryptor-p2p-v2/signal/";
const CHUNK_SIZE  = 12000;
const MAX_MESSAGE_AGE_MS    = 5 * 60 * 1000;
const MAX_FUTURE_TOLERANCE_MS = 60 * 1000;
const MAX_RECONNECT_ATTEMPTS = 60;
const MAX_ATTACHMENTS_PER_MESSAGE = 10; // cap on photos/videos/files bundled into one message

// ── Voice calls ──
const AAD_CALL_FRAME  = te.encode("ScryptorP2P-CALLFRAME-v1");
const CALL_KEY_CONTEXT = te.encode("ScryptorP2P-CALL-v1");
const CALL_RING_TIMEOUT_MS = 45000;

const ID_ALPHABET = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'; // 32 chars, no 0/O/1/I

const EMOJIS = ["🐶","🐱","🐭","🐹","🐰","🦊","🐻","🐼","🐨","🐯","🦁","🐮",
                "🐷","🐸","🐵","🐔","🐧","🐦","🐤","🦄","🦋","🐢","🐠","🐙",
                "🐬","🦑","🐝","🦀","🐺","🦉","🐳","🦓"];

const NICKNAME_ADJECTIVES = ['Silent','Golden','Swift','Brave','Calm','Bright','Wild','Cool','Quick','Wise','Bold','Rapid','Keen','Dark'];
const NICKNAME_NOUNS      = ['Fox','Wolf','Bear','Eagle','Hawk','Tiger','Raven','Storm','River','Stone','Shadow','Flame','Cloud','Pixel'];

const SAFE_MEDIA_TYPES = {
    'image/png':'image','image/jpeg':'image','image/gif':'image','image/webp':'image','image/bmp':'image',
    'video/mp4':'video','video/webm':'video','video/ogg':'video',
    'audio/mpeg':'audio','audio/ogg':'audio','audio/wav':'audio','audio/webm':'audio','audio/mp4':'audio'
};

const RTC_CONFIG = {
    iceServers: [
        { urls: 'stun:stun.l.google.com:19302' },
        { urls: 'stun:stun.cloudflare.com:3478' },
        { urls: 'turn:openrelay.metered.ca:80',  username: 'openrelayproject', credential: 'openrelayproject' },
        { urls: 'turn:openrelay.metered.ca:443', username: 'openrelayproject', credential: 'openrelayproject' },
        { urls: 'turns:openrelay.metered.ca:443?transport=tcp', username: 'openrelayproject', credential: 'openrelayproject' }
    ],
    iceCandidatePoolSize: 10
};

// ── App state ──
let db = null;                        
let myIdentity = null;                
let appLockKey  = null;               

let contacts = new Map();             
let activeContactId = null;           

// ── Signaling ──
let mqttClient    = null;
//let pendingOfferData   = null;

let currentRequest = null;       // текущий обрабатываемый запрос
let pendingRequests = [];        // очередь входящих запросов
let isRequestModalOpen = false;  // флаг открытого модального окна

// ── Per-peer connection/crypto sessions ──
// Each contact you can be connected to gets its own PeerSession. This is what
// used to be a single set of "the one active connection" globals
// (peerConnection, dataChannel, ratchet state, handshake material, reconnect
// timers, ...). Keeping them per-peer instead of global is what lets you have
// several chats connected — and able to send/receive — at the same time,
// instead of connecting to/accepting a new contact tearing down whichever
// connection happened to exist before.
class PeerSession {
    constructor(peerId) {
        this.peerId = peerId;

        // Transport
        this.peerConnection = null;
        this.dataChannel = null;
        this.connectionTimeout = null;
        this.iceCandidateBuffer = [];

        // Hybrid handshake / crypto session
        this.currentSymmetricKey = null;
        this.isMlKemReady = false;
        this.isInitiatorRole = null;
        this.sessionFingerprint = null;
        this.myEphKxKeyPair = null;
        this.myEphMlKemPair = null;
        this.tempFriendEphX25519 = null;
        this.pendingDH = null; // {dh1, termA, termB, dh4} while awaiting HANDSHAKE_CT (responder side)

        // Double Ratchet state — see RatchetOps below
        this.ratchetState = { RK:null, CKs:null, CKr:null, DHs:null, DHr:null, Ns:0, Nr:0, PN:0, skipped:{} };

        // Reconnect / heartbeat (per peer, not global)
        this.heartbeatInterval = null;
        this.heartbeatTimeout  = null;
        this.heartbeatSuspended = false; // true while a large chunked transfer is in flight — see suspendHeartbeat()
        this.transferInFlight   = 0;     // count of concurrent chunked send/receive ops for this peer
        this.isReconnecting    = false;
        this.reconnectAttempts = 0;
        this.reconnectTimer    = null;
        this.connectionLostNotified = false;

        // Voice call — null when idle. See newCallState() in the VOICE CALLS section.
        this.call = null;
        this.audioSender = null;
    }

    wipeCryptoMaterial() {
        secureZero(this.currentSymmetricKey);
        if (this.myEphKxKeyPair?.privateKey) secureZero(this.myEphKxKeyPair.privateKey);
        if (this.myEphMlKemPair?.secretKey)  secureZero(this.myEphMlKemPair.secretKey);
        if (this.ratchetState.RK)  secureZero(this.ratchetState.RK);
        if (this.ratchetState.CKs) secureZero(this.ratchetState.CKs);
        if (this.ratchetState.CKr) secureZero(this.ratchetState.CKr);
        if (this.ratchetState.DHs?.privateKey) secureZero(this.ratchetState.DHs.privateKey);
        for (const k in this.ratchetState.skipped) secureZero(this.ratchetState.skipped[k]);
        if (this.call?.callTxKey) secureZero(this.call.callTxKey);
        if (this.call?.callRxKey) secureZero(this.call.callRxKey);
    }
}

const sessions = new Map(); // peerId (shortId) -> PeerSession

function getOrCreateSession(peerId) {
    let s = sessions.get(peerId);
    if (!s) { s = new PeerSession(peerId); sessions.set(peerId, s); }
    return s;
}
function getActiveSession() { return activeContactId ? (sessions.get(activeContactId) || null) : null; }

function destroySession(peerId) {
    const s = sessions.get(peerId);
    if (!s) return;
    if (s.call) endCall(peerId, null);
    stopHeartbeat(s);
    clearTimeout(s.reconnectTimer);
    clearTimeout(s.connectionTimeout);
    if (s.dataChannel) { try { s.dataChannel.onopen = s.dataChannel.onclose = s.dataChannel.onmessage = null; } catch {} }
    if (s.peerConnection) { try { s.peerConnection.close(); } catch {} }
    s.wipeCryptoMaterial();
    sessions.delete(peerId);
}

// ── UI/chat state ──
let chatMessageCounter = 0;
let chatAttachedFiles  = []; // [{file, data}] — one or more photos/videos/files queued for the next message
let attachmentPreviewUrls = []; // objectURLs for the attachment preview strip, revoked on re-render
let replyToGlobalId    = null;
const globalToLocalMap = new Map();
const replyInfoCache   = new Map();
let mediaObjectUrls    = [];
const messageStatusMap = new Map();
const ackedMessages    = new Set();
const chunkBuffer      = new Map();

let isTypingSent  = false;
let typingTimer   = null;

let passwordModalResolve = null;
let msgIdToDelete = null;

// ── Voice call UI state (global — only one call can be active at a time) ──
let activeCallPeerId       = null; // peerId of the call currently live/ringing on screen
let pendingIncomingCallPeer = null; // peerId of an incoming call awaiting accept/reject
let ringtoneInterval        = null;

const themeNames = { cream:'Кремовая', dark:'Тёмная', rose:'Розовая', ocean:'Океан', forest:'Лесная', midnight:'Полночь' };

// ═══════════════════════════════════════════════════════════
//  UTILITIES
// ═══════════════════════════════════════════════════════════
function showNextRequest() {
    if (pendingRequests.length === 0) {
        isRequestModalOpen = false;
        closeModal('reqModalOverlay');
        return;
    }
    currentRequest = pendingRequests.shift();
    isRequestModalOpen = true;
    document.getElementById('reqModalNickname').textContent = currentRequest.senderNick || currentRequest.sender;
    document.getElementById('reqModalPeerId').textContent = 'ID: ' + currentRequest.sender;
    openModal('reqModalOverlay');
}

function secureZero(obj) {
    if (!obj) return;
    try { if (sodium?.memzero) { sodium.memzero(obj); return; } } catch {}
    try {
        if (obj instanceof Uint8Array) obj.fill(0);
        else if (ArrayBuffer.isView(obj)) new Uint8Array(obj.buffer, obj.byteOffset, obj.byteLength).fill(0);
        else if (obj instanceof ArrayBuffer) new Uint8Array(obj).fill(0);
    } catch {}
}

function arrayBufferToBase64(buffer) {
    const bytes = new Uint8Array(buffer);
    const CHUNK = 0x8000;
    let binary = '';
    for (let i = 0; i < bytes.length; i += CHUNK)
        binary += String.fromCharCode.apply(null, bytes.subarray(i, Math.min(i + CHUNK, bytes.length)));
    return btoa(binary);
}

function base64ToArrayBuffer(b64) {
    const bin = atob(b64); const bytes = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
    return bytes.buffer;
}

function readFileAsArrayBuffer(file) {
    return new Promise((res, rej) => { const r = new FileReader(); r.onload = () => res(r.result); r.onerror = rej; r.readAsArrayBuffer(file); });
}

function writeTimestamp(ts) {
    const b = new Uint8Array(8); const big = BigInt(ts);
    for (let i = 0; i < 8; i++) b[i] = Number((big >> BigInt(i*8)) & BigInt(0xff));
    return b;
}

function extractTimestamp(b) {
    let ts = BigInt(0);
    for (let i = 0; i < 8; i++) ts += BigInt(b[i]) << BigInt(i*8);
    return Number(ts);
}

function validateMessageTime(ts) {
    const now = Date.now(), age = now - ts;
    if (ts > now + MAX_FUTURE_TOLERANCE_MS) return { warning:true, message:'⚠️ Из будущего' };
    if (age > MAX_MESSAGE_AGE_MS) return { warning:true, message:'⚠️ Старое' };
    return { warning:false };
}

function formatTime(d) { return d.getHours().toString().padStart(2,'0') + ':' + d.getMinutes().toString().padStart(2,'0'); }

function formatFileSize(bytes) {
    if (bytes < 1024) return bytes + ' Б';
    if (bytes < 1024*1024) return (bytes/1024).toFixed(1) + ' КБ';
    return (bytes/(1024*1024)).toFixed(1) + ' МБ';
}

function escapeHtml(str) { const d = document.createElement('div'); d.textContent = str; return d.innerHTML; }

function generateDefaultNickname() {
    const adj  = NICKNAME_ADJECTIVES[Math.floor(Math.random() * NICKNAME_ADJECTIVES.length)];
    const noun = NICKNAME_NOUNS[Math.floor(Math.random() * NICKNAME_NOUNS.length)];
    const num  = Math.floor(100 + Math.random() * 900);
    return adj + noun + num;
}

function getFileIconEmoji(type) {
    if (!type) return '📄';
    if (type.startsWith('image/')) return '🖼️';
    if (type.startsWith('video/')) return '🎬';
    if (type.startsWith('audio/')) return '🎵';
    if (type.includes('pdf')) return '📕';
    if (type.includes('zip')||type.includes('rar')||type.includes('7z')) return '📦';
    return '📄';
}

function getVerifiedMediaType(buf) {
    const a = new Uint8Array(buf); if (a.length < 4) return null;
    if (a.length>=8&&a[0]===0x89&&a[1]===0x50&&a[2]===0x4E&&a[3]===0x47) return 'image/png';
    if (a[0]===0xFF&&a[1]===0xD8&&a[2]===0xFF) return 'image/jpeg';
    if (a[0]===0x47&&a[1]===0x49&&a[2]===0x46) return 'image/gif';
    if (a.length>=12&&a[0]===0x52&&a[1]===0x49&&a[2]===0x46&&a[3]===0x46&&a[8]===0x57&&a[9]===0x45&&a[10]===0x52&&a[11]===0x50) return 'image/webp';
    if (a[0]===0x42&&a[1]===0x4D) return 'image/bmp';
    if (a.length>=8&&a[4]===0x66&&a[5]===0x74&&a[6]===0x79&&a[7]===0x70) return 'video/mp4';
    if (a[0]===0x1A&&a[1]===0x45&&a[2]===0xDF&&a[3]===0xA3) return 'video/webm';
    if (a[0]===0x4F&&a[1]===0x67&&a[2]===0x67&&a[3]===0x53) return 'audio/ogg';
    if (a.length>=12&&a[0]===0x52&&a[1]===0x49&&a[2]===0x46&&a[3]===0x46&&a[8]===0x57&&a[9]===0x45&&a[10]===0x56&&a[11]===0x55) return 'audio/wav';
    if ((a[0]===0xFF&&(a[1]===0xFB||a[1]===0xF3||a[1]===0xF2))||(a[0]===0x49&&a[1]===0x44&&a[2]===0x33)) return 'audio/mpeg';
    return null;
}

function containsScriptContent(buf) {
    const txt = new TextDecoder('ascii',{fatal:false}).decode(new Uint8Array(buf).slice(0,1024)).toLowerCase();
    return ['<script','javascript:','onerror=','onload=','<svg','<html','<iframe','<object','<embed'].some(p=>txt.includes(p));
}

async function getNobleMlKem() {
    if (window.noblePqc?.ml_kem768) return window.noblePqc;
    throw new Error('noble-pqc.js не загружена');
}

function avatarLetter(nickname) {
    return (nickname||'?')[0].toUpperCase();
}

function avatarColor(shortId) {
    let h = 0;
    for (let i = 0; i < (shortId||'').length; i++) h = (h * 31 + shortId.charCodeAt(i)) & 0xFFFFFF;
    return `hsl(${h % 360}, 55%, 45%)`;
}

function getDisplayName(contact) {
    if (!contact) return 'Собеседник';
    if (!contact.nickname || contact.nickname === contact.shortId) return 'Новый контакт';
    return contact.nickname;
}

function showStatus(type, message) {
    const d = document.createElement('div');
    d.className = 'status-pill ' + type;
    d.textContent = message;
    Object.assign(d.style, {
        position:'fixed', top:'18px', left:'50%', transform:'translateX(-50%)',
        zIndex:'3000', minWidth:'260px', maxWidth:'90%', textAlign:'center',
        animation:'fadeIn 0.3s ease', boxShadow:'0 4px 18px rgba(0,0,0,0.2)'
    });
    document.body.appendChild(d);
    setTimeout(() => { d.style.transition='opacity 0.3s'; d.style.opacity='0'; setTimeout(()=>d.remove(),320); }, 3500);
}

function closeModal(id) { document.getElementById(id).classList.remove('show'); }
function openModal(id)  { document.getElementById(id).classList.add('show'); }

function updateLog(msg, type='info') {
    const el = document.getElementById('connectionLog');
    if (!el) return;
    el.innerHTML = `<div class="status-pill ${type}" style="margin:4px 0;">${msg}</div>`;
}

// ═══════════════════════════════════════════════════════════
//  INDEXEDDB
// ═══════════════════════════════════════════════════════════
function openDB() {
    return new Promise((resolve, reject) => {
        const req = indexedDB.open(DB_NAME, DB_VERSION);
        req.onupgradeneeded = e => {
            const db = e.target.result;
            if (!db.objectStoreNames.contains('identity'))
                db.createObjectStore('identity', { keyPath: 'id' });
            if (!db.objectStoreNames.contains('contacts'))
                db.createObjectStore('contacts', { keyPath: 'shortId' });
            if (!db.objectStoreNames.contains('messages')) {
                const ms = db.createObjectStore('messages', { keyPath: 'id', autoIncrement: true });
                ms.createIndex('byContact', 'contactId', { unique: false });
                ms.createIndex('byGId', 'gId', { unique: false });
            }
            if (!db.objectStoreNames.contains('settings'))
                db.createObjectStore('settings', { keyPath: 'key' });
        };
        req.onsuccess = e => resolve(e.target.result);
        req.onerror   = e => reject(e.target.error);
    });
}

function dbGet(storeName, key) {
    return new Promise((res, rej) => {
        const tx = db.transaction(storeName, 'readonly');
        const req = tx.objectStore(storeName).get(key);
        req.onsuccess = e => res(e.target.result);
        req.onerror   = e => rej(e.target.error);
    });
}

function dbPut(storeName, value) {
    return new Promise((res, rej) => {
        const tx = db.transaction(storeName, 'readwrite');
        const req = tx.objectStore(storeName).put(value);
        req.onsuccess = e => res(e.target.result);
        req.onerror   = e => rej(e.target.error);
    });
}

function dbDelete(storeName, key) {
    return new Promise((res, rej) => {
        const tx = db.transaction(storeName, 'readwrite');
        const req = tx.objectStore(storeName).delete(key);
        req.onsuccess = () => res();
        req.onerror   = e => rej(e.target.error);
    });
}

function dbGetAll(storeName) {
    return new Promise((res, rej) => {
        const tx = db.transaction(storeName, 'readonly');
        const req = tx.objectStore(storeName).getAll();
        req.onsuccess = e => res(e.target.result);
        req.onerror   = e => rej(e.target.error);
    });
}

function dbGetAllByIndex(storeName, indexName, value) {
    return new Promise((res, rej) => {
        const tx  = db.transaction(storeName, 'readonly');
        const idx = tx.objectStore(storeName).index(indexName);
        const req = idx.getAll(value);
        req.onsuccess = e => res(e.target.result);
        req.onerror   = e => rej(e.target.error);
    });
}

async function dbClearMessages(contactId) {
    const msgs = await dbGetAllByIndex('messages', 'byContact', contactId);
    const tx = db.transaction('messages', 'readwrite');
    const store = tx.objectStore('messages');
    for (const m of msgs) store.delete(m.id);
    return new Promise((res, rej) => { tx.oncomplete = res; tx.onerror = e => rej(e.target.error); });
}

async function dbClearAll() {
    const stores = ['identity','contacts','messages','settings'];
    for (const s of stores) {
        await new Promise((res, rej) => {
            const tx = db.transaction(s, 'readwrite');
            tx.objectStore(s).clear();
            tx.oncomplete = res; tx.onerror = e => rej(e.target.error);
        });
    }
}

// ═══════════════════════════════════════════════════════════
//  SHORT ID GENERATION
// ═══════════════════════════════════════════════════════════
async function deriveShortId(ikPubBytes) {
    const hash = new Uint8Array(await crypto.subtle.digest('SHA-256', ikPubBytes));
    let id = '';
    for (let i = 0; i < 12; i++) id += ID_ALPHABET[hash[i] % 32];
    return id;
}

// ═══════════════════════════════════════════════════════════
//  IDENTITY
// ═══════════════════════════════════════════════════════════
async function loadOrCreateIdentity() {
    const stored = await dbGet('identity', 'self');
    if (stored) {
        if (stored.appLockEnabled) {
            await unlockWithPassword(stored);
        }
        myIdentity = {
            shortId:        stored.shortId,
            ikPub:          new Uint8Array(base64ToArrayBuffer(stored.ikPub)),
            ikSec:          new Uint8Array(base64ToArrayBuffer(stored.ikSec)),
            nickname:       stored.nickname,
            appLockEnabled: stored.appLockEnabled || false
        };
        return false;
    }
    await sodium.ready;
    const kp = sodium.crypto_kx_keypair();
    const shortId = await deriveShortId(kp.publicKey);
    const nickname = generateDefaultNickname();

    myIdentity = {
        shortId,
        ikPub: kp.publicKey,
        ikSec: kp.privateKey,
        nickname,
        appLockEnabled: false
    };
    await persistIdentity();
    return true;
}

async function persistIdentity() {
    await dbPut('identity', {
        id:             'self',
        shortId:        myIdentity.shortId,
        ikPub:          arrayBufferToBase64(myIdentity.ikPub.buffer),
        ikSec:          arrayBufferToBase64(myIdentity.ikSec.buffer),
        nickname:       myIdentity.nickname,
        appLockEnabled: myIdentity.appLockEnabled
    });
}

async function unlockWithPassword(stored) {
    return new Promise((resolve) => {
        openPasswordModal('unlock', async (pwd) => {
            try {
                const vaultMeta = await dbGet('settings', 'vaultMeta');
                if (!vaultMeta) { closeModal('passwordOverlay'); resolve(); return; }
                const salt = new Uint8Array(base64ToArrayBuffer(vaultMeta.salt));
                await sodium.ready;
                const rawKey = sodium.crypto_pwhash(
                    32, te.encode(pwd), salt,
                    vaultMeta.opslimit, vaultMeta.memlimit,
                    sodium.crypto_pwhash_ALG_ARGON2ID13
                );
                const encBuf = new Uint8Array(base64ToArrayBuffer(stored.ikSec));
                const NONCE_LEN = sodium.crypto_aead_xchacha20poly1305_ietf_NPUBBYTES;
                const nonce = encBuf.slice(0, NONCE_LEN);
                const ct    = encBuf.slice(NONCE_LEN);
                const plain = sodium.crypto_aead_xchacha20poly1305_ietf_decrypt(null, ct, null, nonce, rawKey);
                stored.ikSec = arrayBufferToBase64(plain.buffer);
                appLockKey = rawKey;
                closeModal('passwordOverlay');
                resolve();
            } catch(e) {
                document.getElementById('passwordError').textContent = 'Неверный пароль';
                document.getElementById('passwordError').style.display = 'block';
            }
        }, false);
    });
}

// ═══════════════════════════════════════════════════════════
//  CONTACTS
// ═══════════════════════════════════════════════════════════
async function loadContacts() {
    const all = await dbGetAll('contacts');
    contacts.clear();
    for (const c of all) contacts.set(c.shortId, c);
}

async function saveContact(contact) {
    contacts.set(contact.shortId, contact);
    await dbPut('contacts', contact);
}

async function deleteContact(shortId) {
    contacts.delete(shortId);
    await dbDelete('contacts', shortId);
    await dbClearMessages(shortId);
}

async function tofuContact(shortId, ikPubB64, nickname) {
    const existing = contacts.get(shortId);
    const isPlaceholderNickname = !nickname;

    if (existing) {
        if (existing.ikPub && existing.ikPub !== ikPubB64) {
            return 'mismatch';
        }
        if (!isPlaceholderNickname) existing.nickname = nickname;
        existing.lastSeenAt = Date.now();
        if (!existing.ikPub) existing.ikPub = ikPubB64;
        await saveContact(existing);
        renderContactsList();
        return existing.ikPub ? 'match' : 'new';
    } else {
        const finalNickname = isPlaceholderNickname ? null : nickname;
        await saveContact({
            shortId, ikPub: ikPubB64, nickname: finalNickname,
            verified: false, addedAt: Date.now(), lastSeenAt: Date.now()
        });
        showStatus('info', `✅ Контакт ${getDisplayName({shortId, nickname: finalNickname})} сохранён`);
        renderContactsList();
        return 'new';
    }
}

// ═══════════════════════════════════════════════════════════
//  MESSAGES
// ═══════════════════════════════════════════════════════════
async function persistMessage(contactId, msg) {
    return dbPut('messages', { ...msg, contactId });
}

async function updateMsgStatus(gId, status) {
    const msgs = await dbGetAllByIndex('messages', 'byGId', gId);
    for (const m of msgs) {
        m.status = status;
        await dbPut('messages', m);
    }
}

async function deleteMsgFromDB(gId) {
    const msgs = await dbGetAllByIndex('messages', 'byGId', gId);
    for (const m of msgs) await dbDelete('messages', m.id);
}

async function loadHistory(contactId) {
    const msgs = await dbGetAllByIndex('messages', 'byContact', contactId);
    msgs.sort((a,b) => (a.ts||0) - (b.ts||0));
    return msgs;
}

// ═══════════════════════════════════════════════════════════
//  DOUBLE RATCHET
// ═══════════════════════════════════════════════════════════
// Same Double Ratchet math as before — the only change is that state now
// lives on the calling PeerSession (state passed in explicitly) instead of
// a single `this.state` shared by the whole app, so each peer ratchets
// independently.
const RatchetOps = {
    MAX_SKIP: 100,

    KDF_RK(rk, dh_out) {
        const out = sodium.crypto_generichash(64, dh_out, rk);
        return { RK: out.slice(0,32), CK: out.slice(32,64) };
    },

    KDF_CK(ck) {
        const mk      = sodium.crypto_generichash(32, new Uint8Array([0x01]), ck);
        const next_ck = sodium.crypto_generichash(32, new Uint8Array([0x02]), ck);
        return { CK: next_ck, MK: mk };
    },

    initState(sharedSecret, isAlice, friendEphX25519Pub, myEphX25519KeyPair) {
        const state = { RK: sharedSecret, CKs:null, CKr:null, DHs:null, DHr:null, Ns:0, Nr:0, PN:0, skipped:{} };
        if (isAlice) {
            state.DHs = sodium.crypto_kx_keypair();
            state.DHr = friendEphX25519Pub;
            const dh_out = sodium.crypto_scalarmult(state.DHs.privateKey, state.DHr);
            const kdf    = RatchetOps.KDF_RK(state.RK, dh_out);
            secureZero(state.RK); secureZero(dh_out);
            state.RK  = kdf.RK;
            state.CKs = kdf.CK;
        } else {
            state.DHs = myEphX25519KeyPair;
        }
        return state;
    },

    ratchetEncrypt(state) {
        if (!state.CKs) throw new Error("Дождитесь первого сообщения от собеседника.");
        const kdf    = RatchetOps.KDF_CK(state.CKs);
        secureZero(state.CKs);
        state.CKs = kdf.CK;
        const header   = { dh: arrayBufferToBase64(state.DHs.publicKey), n: state.Ns, pn: state.PN };
        state.Ns++;
        return { mk: kdf.MK, header };
    },

    ratchetDecryptTentative(state, header) {
        const skipKey = header.dh + '_' + header.n;
        if (state.skipped[skipKey])
            return { mk: state.skipped[skipKey], tentativeState: null, skipKeyToRemove: skipKey };

        let ts = {
            RK:  new Uint8Array(state.RK),
            CKs: state.CKs ? new Uint8Array(state.CKs) : null,
            CKr: state.CKr ? new Uint8Array(state.CKr) : null,
            DHs: { publicKey: new Uint8Array(state.DHs.publicKey), privateKey: new Uint8Array(state.DHs.privateKey) },
            DHr: state.DHr ? new Uint8Array(state.DHr) : null,
            Ns: state.Ns, Nr: state.Nr, PN: state.PN,
            skipped: { ...state.skipped }
        };

        const dh_pub = new Uint8Array(base64ToArrayBuffer(header.dh));
        if (!ts.DHr || arrayBufferToBase64(ts.DHr) !== header.dh) {
            RatchetOps._skipMessageKeys(ts, header.pn);
            RatchetOps._DHRatchetStep(ts, dh_pub);
        }
        RatchetOps._skipMessageKeys(ts, header.n);
        const kdf = RatchetOps.KDF_CK(ts.CKr);
        secureZero(ts.CKr); ts.CKr = kdf.CK; ts.Nr++;
        return { mk: kdf.MK, tentativeState: ts, skipKeyToRemove: null };
    },

    // Commits the tentative state produced by ratchetDecryptTentative onto the session.
    commitState(session, ts, skipKeyToRemove) {
        if (skipKeyToRemove) { secureZero(session.ratchetState.skipped[skipKeyToRemove]); delete session.ratchetState.skipped[skipKeyToRemove]; }
        if (ts) session.ratchetState = ts;
    },

    _DHRatchetStep(state, dh_pub) {
        state.PN = state.Ns; state.Ns = 0; state.Nr = 0; state.DHr = dh_pub;
        let dh_out = sodium.crypto_scalarmult(state.DHs.privateKey, state.DHr);
        let kdf    = RatchetOps.KDF_RK(state.RK, dh_out);
        secureZero(dh_out); secureZero(state.RK);
        state.RK = kdf.RK; state.CKr = kdf.CK;
        state.DHs  = sodium.crypto_kx_keypair();
        dh_out = sodium.crypto_scalarmult(state.DHs.privateKey, state.DHr);
        kdf    = RatchetOps.KDF_RK(state.RK, dh_out);
        secureZero(dh_out); secureZero(state.RK);
        state.RK = kdf.RK; state.CKs = kdf.CK;
    },

    _skipMessageKeys(state, until_n) {
        if (state.Nr + RatchetOps.MAX_SKIP < until_n) throw new Error("Превышен лимит пропуска.");
        if (state.CKr != null) {
            while (state.Nr < until_n) {
                const kdf = RatchetOps.KDF_CK(state.CKr);
                secureZero(state.CKr); state.CKr = kdf.CK;
                state.skipped[arrayBufferToBase64(state.DHr) + '_' + state.Nr] = kdf.MK;
                state.Nr++;
            }
        }
    }
};

// ═══════════════════════════════════════════════════════════
//  CRYPTO
// ═══════════════════════════════════════════════════════════
async function encryptPayload(plainBytes, aadPrefix, messageKey) {
    await sodium.ready;
    const nonce     = sodium.randombytes_buf(sodium.crypto_aead_xchacha20poly1305_ietf_NPUBBYTES);
    const timestamp = writeTimestamp(Date.now());
    const withFlag  = new Uint8Array(1 + plainBytes.length);
    withFlag[0] = 0x00; withFlag.set(plainBytes, 1);
    const aad = new Uint8Array(aadPrefix.length + timestamp.length);
    aad.set(aadPrefix, 0); aad.set(timestamp, aadPrefix.length);
    const encrypted = sodium.crypto_aead_xchacha20poly1305_ietf_encrypt(withFlag, aad, null, nonce, messageKey);
    const out = new Uint8Array(nonce.length + timestamp.length + encrypted.length);
    out.set(nonce, 0); out.set(timestamp, nonce.length); out.set(encrypted, nonce.length + timestamp.length);
    return arrayBufferToBase64(out);
}

async function decryptPayload(ctB64, aadPrefix, messageKey) {
    await sodium.ready;
    const combined  = new Uint8Array(base64ToArrayBuffer(ctB64));
    const NONCE_LEN = sodium.crypto_aead_xchacha20poly1305_ietf_NPUBBYTES;
    const TS_LEN    = 8;
    if (combined.length < NONCE_LEN + TS_LEN) throw new Error("Слишком короткий шифротекст.");
    const nonce     = combined.slice(0, NONCE_LEN);
    const timestamp = combined.slice(NONCE_LEN, NONCE_LEN + TS_LEN);
    const encrypted = combined.slice(NONCE_LEN + TS_LEN);
    const aad = new Uint8Array(aadPrefix.length + timestamp.length);
    aad.set(aadPrefix, 0); aad.set(timestamp, aadPrefix.length);
    let decrypted;
    try {
        decrypted = sodium.crypto_aead_xchacha20poly1305_ietf_decrypt(null, encrypted, aad, nonce, messageKey);
    } catch {
        throw new Error("Неверный MAC. Сообщение повреждено или скомпрометировано.");
    }
    if (!decrypted || decrypted.length === 0) throw new Error("Пустые расшифрованные данные.");
    const timeCheck = validateMessageTime(extractTimestamp(timestamp));
    return { data: decrypted.slice(1), timeCheck };
}

function packPayload(metadata, binaryData = null) {
    const metaBytes = te.encode(JSON.stringify(metadata));
    const out = new Uint8Array(4 + metaBytes.length + (binaryData ? binaryData.byteLength : 0));
    new DataView(out.buffer).setUint32(0, metaBytes.length, true);
    out.set(metaBytes, 4);
    if (binaryData) out.set(new Uint8Array(binaryData), 4 + metaBytes.length);
    return out;
}

function unpackPayload(bytes) {
    if (!bytes || bytes.byteLength < 4) throw new Error("Неверный бинарный пакет.");
    const metaLen = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength).getUint32(0, true);
    if (bytes.byteLength < 4 + metaLen) throw new Error("Повреждённая мета-информация.");
    const metadata   = JSON.parse(td.decode(bytes.subarray(4, 4 + metaLen)));
    const binaryData = bytes.byteLength > 4 + metaLen ? bytes.subarray(4 + metaLen) : null;
    return { metadata, binaryData };
}

// Multi-attachment variant of packPayload/unpackPayload: one JSON metadata
// header (with metadata.files describing each attachment) followed by each
// attachment's raw bytes, each prefixed with its own 4-byte length. Used for
// messages carrying one or more photos/videos/files bundled together. Since
// this whole blob is encrypted and sent as a single atomic envelope (chunked
// at the transport level only, reassembled before decryption — see
// handleChunk), the recipient only ever sees it once every attachment has
// fully arrived; there's no separate per-attachment delivery to race against.
function packMultiPayload(metadata, buffers) {
    const metaBytes = te.encode(JSON.stringify(metadata));
    let total = 4 + metaBytes.length;
    for (const b of buffers) total += 4 + (b ? b.byteLength : 0);
    const out = new Uint8Array(total);
    const dv  = new DataView(out.buffer);
    let off = 0;
    dv.setUint32(off, metaBytes.length, true); off += 4;
    out.set(metaBytes, off); off += metaBytes.length;
    for (const b of buffers) {
        const bytes = b ? new Uint8Array(b) : new Uint8Array(0);
        dv.setUint32(off, bytes.length, true); off += 4;
        out.set(bytes, off); off += bytes.length;
    }
    return out;
}

function unpackMultiPayload(bytes) {
    if (!bytes || bytes.byteLength < 4) throw new Error("Неверный бинарный пакет.");
    const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    let off = 0;
    const metaLen = dv.getUint32(off, true); off += 4;
    if (bytes.byteLength < off + metaLen) throw new Error("Повреждённая мета-информация.");
    const metadata = JSON.parse(td.decode(bytes.subarray(off, off + metaLen))); off += metaLen;
    const buffers = [];
    const count = metadata.files ? metadata.files.length : 0;
    for (let i = 0; i < count; i++) {
        if (bytes.byteLength < off + 4) throw new Error("Повреждённый пакет вложений.");
        const len = dv.getUint32(off, true); off += 4;
        if (bytes.byteLength < off + len) throw new Error("Повреждённый пакет вложений.");
        buffers.push(bytes.subarray(off, off + len)); off += len;
    }
    return { metadata, buffers };
}

function buildEnvelope(type, ctB64, ratchetHeader) {
    return btoa(unescape(encodeURIComponent(JSON.stringify({ v:5, type, ct: ctB64, rh: ratchetHeader }))));
}

function parseEnvelope(text) {
    try {
        const json = JSON.parse(decodeURIComponent(escape(atob(text.replace(/\s+/g,'')))));
        if (json.v >= 2 && json.ct) return json;
    } catch {}
    return null;
}

// ═══════════════════════════════════════════════════════════
//  SESSION FINGERPRINT
// ═══════════════════════════════════════════════════════════
async function computeSessionFingerprint(keyBytes) {
    const hash = new Uint8Array(await crypto.subtle.digest('SHA-512', keyBytes));
    const CHARS = ['2','3','4','5','6','7','8','9','B','C','D','F','G','H','J','K',
                   'L','M','N','P','Q','R','S','T','V','W','X','Y','Z','2','3','4'];
    const groups = [];
    for (let g = 0; g < 4; g++) {
        let part = '';
        for (let c = 0; c < 6; c++) part += CHARS[hash[g*6+c] % 32];
        groups.push(part);
    }
    let emojis = '';
    for (let i = 24; i < 28; i++) emojis += EMOJIS[hash[i] % EMOJIS.length];
    return { code: groups.join('-'), emojis };
}

function showFingerprintModal() {
    const session = getActiveSession();
    if (!session?.sessionFingerprint) return;
    document.getElementById('fpCodeDisplay').textContent   = session.sessionFingerprint.code;
    document.getElementById('fpEmojisDisplay').textContent = session.sessionFingerprint.emojis;
    openModal('fpModalOverlay');
}

// ═══════════════════════════════════════════════════════════
//  SIGNALING (MQTT)
// ═══════════════════════════════════════════════════════════
async function initSignalling() {
    return new Promise((resolve, reject) => {
        if (mqttClient?.connected) {
            resolve();
            return;
        }
        if (mqttClient) {
            if (!mqttClient.connected) {
                mqttClient.once('connect', resolve);
                mqttClient.once('error', reject);
                return;
            }
        }
        mqttClient = mqtt.connect('wss://broker.emqx.io:8084/mqtt', {
            clientId: 'scryptor_' + myIdentity.shortId + '_' + Math.random().toString(16).slice(2,10),
            keepalive: 60,
            reconnectPeriod: 2000,
            clean: true
        });

        mqttClient.on('connect', () => {
            updateLog("Сигнальный канал активен", "success");
            mqttClient.subscribe(SIGNALING_TOPIC + myIdentity.shortId, err => {
                if (err) updateLog("Ошибка подписки MQTT", "error");
            });
            resolve();
        });

        mqttClient.on('error', (e) => {
            updateLog("Ошибка сигнального сервера", "error");
            reject(e);
        });

        mqttClient.on('message', async (topic, message) => {
            try {
                const data = JSON.parse(message.toString());
                if (data.sender === myIdentity.shortId) return;
                await handleSignalMessage(data);
            } catch (e) {
                console.error("MQTT parse error:", e);
            }
        });
    });
}

function ensureSignalling() {
    return initSignalling();
}

function sendSignal(targetId, data) {
    if (!mqttClient?.connected) return;
    data.sender   = myIdentity.shortId;
    data.senderNick = myIdentity.nickname;
    data.senderIkPub = arrayBufferToBase64(myIdentity.ikPub.buffer);
    mqttClient.publish(SIGNALING_TOPIC + targetId, JSON.stringify(data));
}

async function handleIncomingOffer(data) {
    const senderId = data.sender;
    const nickname = data.senderNick || null;
    const ikPub = data.senderIkPub;

    const existing = contacts.get(senderId);
    if (!existing) {
        await saveContact({
            shortId: senderId, ikPub: ikPub || '', nickname, verified: false, addedAt: Date.now(), lastSeenAt: Date.now()
        });
        renderContactsList();
    } else if (data.senderNick && existing.nickname !== data.senderNick) {
        existing.nickname   = data.senderNick;
        existing.lastSeenAt = Date.now();
        await saveContact(existing);
        renderContactsList();
    }

    // Note: this used to force-switch the open chat to whichever contact just
    // sent an offer/reconnect. That's exactly what broke "other" chats when
    // this fired in the background — removed so background connections don't
    // disturb whatever chat you're currently reading.
    await handleOffer(data.offer, senderId);
}

function acceptConnectionRequest() {
    if (!currentRequest) return;
    closeModal('reqModalOverlay');
    const data = currentRequest;
    currentRequest = null;
    isRequestModalOpen = false;
    handleIncomingOffer(data); // асинхронно, но не ждём
    showNextRequest();
}

function rejectConnectionRequest() {
    if (!currentRequest) return;
    closeModal('reqModalOverlay');
    const data = currentRequest;
    currentRequest = null;
    isRequestModalOpen = false;
    sendSignal(data.sender, { type: 'request_rejected' });
    showNextRequest();
}

function removePendingRequestsFrom(senderId) {
    pendingRequests = pendingRequests.filter(req => req.sender !== senderId);
    if (currentRequest && currentRequest.sender === senderId) {
        closeModal('reqModalOverlay');
        currentRequest = null;
        isRequestModalOpen = false;
        showNextRequest();
    }
}

async function handleSignalMessage(data) {
    if (data.type === 'connection_request') {
            // Реконнект – обрабатываем сразу, не показывая модалку
            if (data.isReconnect && sessions.has(data.sender)) {
                await handleIncomingOffer(data);
                return;
            }
            // Добавляем запрос в очередь
            pendingRequests.push(data);
            if (!isRequestModalOpen) {
                showNextRequest();
            }
            return;
    } else if (data.type === 'request_rejected') {
        if (activeContactId === data.sender) { updateLog("Запрос отклонён собеседником", "error"); resetConnectButton(); }
        const session = sessions.get(data.sender);
        if (session) {
            clearTimeout(session.connectionTimeout);
            if (session.peerConnection) { try { session.peerConnection.close(); } catch {} session.peerConnection = null; }
        }
    } else if (data.type === 'answer') {
        const session = sessions.get(data.sender);
        if (!session?.peerConnection) {
            console.warn("Получен 'answer', но peerConnection отсутствует — игнорируем.");
            return;
        }
        if (session.peerConnection.signalingState !== 'have-local-offer') {
            console.warn("Получен 'answer', не соответствующий текущему состоянию согласования — игнорируем.");
            return;
        }

        if (activeContactId === data.sender) updateLog("Ответ получен, устанавливаем P2P...", "info");
        if (data.senderNick) {
            const c = contacts.get(data.sender);
            if (c && c.nickname !== data.senderNick) { c.nickname = data.senderNick; await saveContact(c); }
        }
        try {
            await session.peerConnection.setRemoteDescription(new RTCSessionDescription(data.answer));
            await flushBufferedCandidates(data.sender);
        } catch (e) {
            if (activeContactId === data.sender) updateLog("Ошибка применения ответа: " + e.message, "error");
        }
    } else if (data.type === 'candidate') {
        const session = getOrCreateSession(data.sender);
        if (session.peerConnection?.remoteDescription?.type) {
            try { await session.peerConnection.addIceCandidate(new RTCIceCandidate(data.candidate)); } catch {}
        } else {
            session.iceCandidateBuffer.push(data.candidate);
        }
    }
}

async function flushBufferedCandidates(senderId) {
    const session = sessions.get(senderId);
    if (!session?.peerConnection?.remoteDescription?.type) return;
    const buffered = session.iceCandidateBuffer;
    if (!buffered.length) return;
    for (const c of buffered) try { await session.peerConnection.addIceCandidate(new RTCIceCandidate(c)); } catch {}
    session.iceCandidateBuffer = [];
}

// ═══════════════════════════════════════════════════════════
//  WEBRTC
// ═══════════════════════════════════════════════════════════
function createPeerConnection(targetId) {
    const session = getOrCreateSession(targetId);
    if (session.peerConnection) { try { session.peerConnection.close(); } catch {} }
    session.peerConnection = new RTCPeerConnection(RTC_CONFIG);

    session.peerConnection.onicecandidate = e => {
        if (e.candidate) sendSignal(targetId, { type:'candidate', candidate: e.candidate });
    };

    session.peerConnection.oniceconnectionstatechange = () => {
        const state = session.peerConnection.iceConnectionState;
        if (state === 'connected' || state === 'completed') {
            if (activeContactId === targetId) updateLog("P2P соединение установлено!", "success");
            clearTimeout(session.connectionTimeout);
        } else if (state === 'disconnected' || state === 'failed') {
            if (activeContactId === targetId) updateLog("P2P соединение разорвано", "error");

            // 'failed' means the ICE agent gave up entirely — no candidate pair
            // worked (this is what's behind Firefox's "your TURN server appears
            // to be broken"). If this happened before the data channel ever
            // opened, its 'onclose' handler may never fire (it never opened to
            // begin with), so the existing 90s connect-timeout / 30s reconnect
            // timeout would otherwise be the only thing to notice — leaving the
            // user staring at a spinner for up to a minute and a half for
            // nothing. React immediately instead, but only for that "never
            // actually connected yet" case — a session whose data channel DID
            // open already has a working recovery path via
            // handleConnectionLost() triggered from onclose, and we don't want
            // to race with that here.
            if (state === 'failed' && !session.isMlKemReady) {
                clearTimeout(session.connectionTimeout);
                try { session.peerConnection.close(); } catch {}
                session.peerConnection = null;
                if (session.isReconnecting) {
                    clearTimeout(session.reconnectTimer);
                    session.reconnectTimer = setTimeout(() => attemptReconnect(targetId), 1500);
                } else if (activeContactId === targetId) {
                    updateLog("Не удалось установить P2P-соединение (ICE/TURN). Попробуйте ещё раз.", "error");
                    resetConnectButton();
                }
            }
        }
    };

    // Fires when the remote party's audio (later: video) track arrives during
    // a call renegotiation. Not related to the data channel at all.
    session.peerConnection.ontrack = e => {
        const s = sessions.get(targetId);
        if (!s?.call) return;
        s.call.remoteStream  = e.streams[0] || new MediaStream([e.track]);
        s.call.audioReceiver = e.receiver;
        if (activeCallPeerId === targetId) {
            document.getElementById('remoteCallAudio').srcObject = s.call.remoteStream;
        }
        attachCallEncryption(s);
        beginActiveCallState(targetId);
    };

    const dc = session.peerConnection.createDataChannel('secureChat', { negotiated: true, id: 0 });
    setupDataChannel(session, dc, targetId);
    return session;
}

async function initiateConnection() {
    const targetId = activeContactId;
    if (!targetId) { showStatus('error','Сначала выберите контакт'); return; }
    if (targetId === myIdentity.shortId) { showStatus('error','Нельзя подключиться к себе'); return; }

    const already = sessions.get(targetId);
    if (already?.isMlKemReady) { showStatus('info','Уже подключено'); return; }

    const btn = document.getElementById('btnConnect');
    btn.disabled = true;
    btn.innerHTML = '<span class="spinner"></span> Подключение...';

    try {
        await sodium.ready;
        const session = createPeerConnection(targetId);

        clearTimeout(session.connectionTimeout);
        session.connectionTimeout = setTimeout(() => {
            if (activeContactId === targetId) { updateLog("Таймаут подключения. Проверьте ID и сеть.", "error"); resetConnectButton(); }
            if (session.peerConnection) { try { session.peerConnection.close(); } catch {} session.peerConnection = null; }
        }, 90000);

        const offer = await session.peerConnection.createOffer();
        await session.peerConnection.setLocalDescription(offer);
        sendSignal(targetId, { type: 'connection_request', offer });
        if (activeContactId === targetId) updateLog("Запрос отправлен. Ожидаем ответа...", "info");
    } catch(e) {
        if (activeContactId === targetId) updateLog("Ошибка WebRTC: " + e.message, "error");
        resetConnectButton();
        const session = sessions.get(targetId);
        if (session) clearTimeout(session.connectionTimeout);
    }
}



async function handleOffer(offer, senderId) {
    try {
        await sodium.ready;
        const session = createPeerConnection(senderId);

        clearTimeout(session.connectionTimeout);
        session.connectionTimeout = setTimeout(() => {
            if (activeContactId === senderId) { updateLog("Таймаут входящего соединения.", "error"); resetConnectButton(); }
        }, 90000);

        await session.peerConnection.setRemoteDescription(new RTCSessionDescription(offer));
        await flushBufferedCandidates(senderId);
        const answer = await session.peerConnection.createAnswer();
        await session.peerConnection.setLocalDescription(answer);
        sendSignal(senderId, { type: 'answer', answer });
        if (activeContactId === senderId) updateLog("Ожидаем установки прямого канала...", "info");
    } catch(e) {
        if (activeContactId === senderId) updateLog("Ошибка при обработке запроса: " + e.message, "error");
        resetConnectButton();
        const session = sessions.get(senderId);
        if (session) clearTimeout(session.connectionTimeout);
    }
}

function setupDataChannel(session, channel, targetId) {
    session.dataChannel = channel;
    channel.binaryType = "arraybuffer";

    channel.onopen = () => {
        clearTimeout(session.connectionTimeout);
        clearTimeout(session.reconnectTimer);
        session.isReconnecting = false; session.reconnectAttempts = 0; session.connectionLostNotified = false;
        if (activeContactId === targetId) updateLog("Канал открыт. Рукопожатие...", "success");
        // NOTE: previously ended the MQTT signaling client here once a P2P
        // channel opened. That's fine with only one possible connection, but
        // it breaks multi-chat: MQTT is still needed to signal/accept
        // connections to *other* contacts. Signaling now just stays up.
        startHeartbeat(session, targetId);
        startCryptoHandshake(session);
    };

    channel.onclose = () => handleConnectionLost(targetId);
    channel.onmessage = e => handleIncomingP2PData(session, targetId, e.data);
}

// ═══════════════════════════════════════════════════════════
//  RECONNECT & HEARTBEAT
// ═══════════════════════════════════════════════════════════
function handleConnectionLost(targetId) {
    const session = sessions.get(targetId);
    if (!session) return;
    if (session.call) { showStatus('error', '📴 Звонок прерван — соединение потеряно'); endCall(targetId, null); }
    session.isMlKemReady = false;
    if (activeContactId === targetId) updateChatHeader();
    renderContactsList();
    if (!session.connectionLostNotified) {
        session.connectionLostNotified = true;
        showStatus('error', `⚠️ Соединение с ${getDisplayName(contacts.get(targetId))} разорвано...`);
    }
    stopHeartbeat(session);

    // Anything still sitting in "sent" (i.e. not yet delivered/read) for this
    // peer is now genuinely in doubt — flag it so the person can retry it,
    // instead of the old approach of guessing after a fixed timer (which is
    // exactly what used to misfire on slow file transfers).
    for (const [gId, entry] of messageStatusMap) {
        if (entry.peerId === targetId && entry.status === 'sent') markMessageFailed(gId);
    }

    if (!session.isReconnecting) startReconnection(targetId);
}

// Pausing the heartbeat while suspend=true stops us from sending a PING that
// would otherwise queue up behind a large in-flight transfer on this same
// ordered, reliable data channel — and, symmetrically, stops us from acting
// on a PONG that never arrives in time for the same reason. A dropped
// connection is still caught immediately via dataChannel.onclose /
// oniceconnectionstatechange either way, so nothing is lost by pausing this
// secondary liveness check while we already know why the peer is quiet.
function suspendHeartbeat(session, suspend) {
    if (!session) return;
    session.heartbeatSuspended = suspend;
    if (suspend) { clearTimeout(session.heartbeatTimeout); session.heartbeatTimeout = null; }
}

function startHeartbeat(session, targetId) {
    stopHeartbeat(session);
    session.heartbeatInterval = setInterval(() => {
        if (session.heartbeatSuspended) return; // large transfer in progress — see sendEnvelope()/handleChunk()
        if (session.dataChannel?.readyState === 'open') {
            try {
                session.dataChannel.send(JSON.stringify({ type: 'PING' }));
                session.heartbeatTimeout = setTimeout(() => {
                    if (session.heartbeatSuspended) return;
                    if (session.dataChannel?.readyState === 'open') handleConnectionLost(targetId);
                }, 30000);
            } catch { if (!session.heartbeatSuspended) handleConnectionLost(targetId); }
        } else { handleConnectionLost(targetId); }
    }, 10000);
}

function stopHeartbeat(session) {
    if (!session) return;
    clearInterval(session.heartbeatInterval); clearTimeout(session.heartbeatTimeout);
    session.heartbeatInterval = null; session.heartbeatTimeout = null;
    session.heartbeatSuspended = false; session.transferInFlight = 0;
}

function startReconnection(targetId) {
    const session = sessions.get(targetId);
    if (!session || session.isReconnecting) return;
    session.isReconnecting = true; session.reconnectAttempts = 0;
    if (activeContactId === targetId) showPeerStatus('reconnecting');
    attemptReconnect(targetId);
}

function isReconnectInitiator(peerShortId) {
    return myIdentity.shortId < peerShortId;
}

async function attemptReconnect(targetId) {
    const session = sessions.get(targetId);
    if (!session) return;
    session.reconnectAttempts++;
    if (session.reconnectAttempts > MAX_RECONNECT_ATTEMPTS) {
        session.isReconnecting = false;
        if (activeContactId === targetId) showPeerStatus('lost');
        showStatus('error', `❌ Не удалось переподключиться к ${getDisplayName(contacts.get(targetId))}.`);
        return;
    }

    try {
        await ensureSignalling();
    } catch (e) {
        session.reconnectTimer = setTimeout(() => attemptReconnect(targetId), 2000);
        return;
    }

    session.isMlKemReady = false;
    session.currentSymmetricKey = null;
    session.sessionFingerprint = null;
    if (activeContactId === targetId) document.getElementById('btnFingerprint').disabled = true;
    renderContactsList();

    if (session.peerConnection) {
        try { session.peerConnection.close(); } catch {}
        session.peerConnection = null;
    }

    clearTimeout(session.connectionTimeout);
    if (isReconnectInitiator(targetId)) {
        sendReconnectOffer(targetId);
    } else {
        if (activeContactId === targetId) updateLog("Ожидаем переподключения от собеседника...", "info");
        session.connectionTimeout = setTimeout(() => {
            if (!session.isReconnecting || session.isMlKemReady) return;
            if (activeContactId === targetId) updateLog("Собеседник не инициировал переподключение, пробуем сами...", "info");
            sendReconnectOffer(targetId);
        }, 8000);
    }
}

function sendReconnectOffer(targetId) {
    const session = createPeerConnection(targetId);

    (async () => {
        try {
            const offer = await session.peerConnection.createOffer();
            await session.peerConnection.setLocalDescription(offer);
            sendSignal(targetId, { type: 'connection_request', offer, isReconnect: true });

            clearTimeout(session.connectionTimeout);
            session.connectionTimeout = setTimeout(() => {
                if (activeContactId === targetId) { updateLog("Таймаут переподключения.", "error"); resetConnectButton(); }
                if (session.peerConnection) {
                    try { session.peerConnection.close(); } catch {}
                    session.peerConnection = null;
                }
                session.reconnectTimer = setTimeout(() => attemptReconnect(targetId), 3000);
            }, 30000);
        } catch (e) {
            session.reconnectTimer = setTimeout(() => attemptReconnect(targetId), 2000);
        }
    })();
}

function resetConnectButton() {
    const btn = document.getElementById('btnConnect');
    if (btn) { btn.disabled = false; btn.innerHTML = '🔗 Подключиться'; }
}

// ═══════════════════════════════════════════════════════════
//  HYBRID HANDSHAKE
// ═══════════════════════════════════════════════════════════
async function startCryptoHandshake(session) {
    try {
        const { ml_kem768 } = await getNobleMlKem();
        session.myEphKxKeyPair = sodium.crypto_kx_keypair();
        session.myEphMlKemPair = ml_kem768.keygen();

        const combined = new Uint8Array(32 + 32 + 1184);
        combined.set(myIdentity.ikPub, 0);
        combined.set(session.myEphKxKeyPair.publicKey, 32);
        combined.set(session.myEphMlKemPair.publicKey, 64);

        session.dataChannel.send(JSON.stringify({ type: 'HANDSHAKE_PK', pk: arrayBufferToBase64(combined.buffer) }));
    } catch(e) {
        if (activeContactId === session.peerId) updateLog("Ошибка рукопожатия: " + e.message, "error");
    }
}

async function handleIncomingP2PData(session, peerId, data) {
    if (typeof data !== 'string') return;
    try {
        const msg = JSON.parse(data);

        if (msg.type === 'PING') {
            if (session.dataChannel?.readyState === 'open') session.dataChannel.send(JSON.stringify({ type:'PONG' }));
            return;
        }
        if (msg.type === 'PONG') {
            clearTimeout(session.heartbeatTimeout);
            if (session.connectionLostNotified) {
                session.connectionLostNotified = false;
                if (activeContactId === peerId) { showStatus('success', '🔗 Соединение восстановлено!'); showPeerStatus('idle'); }
            }
            return;
        }
        if (msg.type === 'MSG_ACK') {
            const entry = messageStatusMap.get(msg.msgId);
            if (entry?.status === 'sent') updateMessageStatus(msg.msgId, 'delivered');
            return;
        }
        if (msg.type === 'MSG_READ') {
            const entry = messageStatusMap.get(msg.msgId);
            if (entry && (entry.status === 'sent' || entry.status === 'delivered')) updateMessageStatus(msg.msgId, 'read');
            return;
        }
        if (msg.type === 'PEER_STATUS') {
            if (activeContactId === peerId) showPeerStatus(msg.status);
            return;
        }
        if (msg.type === 'CHAT_MSG_DELETE') {
            await deleteMessageLocally(msg.payload, true);
            return;
        }
        if (msg.type === 'CHAT_MSG') { receiveMessage(session, peerId, msg.payload); return; }
        if (msg.type === 'CHAT_CHUNK') { handleChunk(session, peerId, msg); return; }

        // ── Voice call signaling — all riding the already-connected, already
        // TOFU-verified data channel instead of raw MQTT, so nothing here
        // needs its own authentication: it inherits the peer identity check
        // already performed in HANDSHAKE_PK below. ──
        if (msg.type === 'CALL_OFFER') {
            if (activeCallPeerId || session.call) {
                if (session.dataChannel?.readyState === 'open')
                    session.dataChannel.send(JSON.stringify({ type:'CALL_REJECT', callId: msg.callId, reason:'busy' }));
                return;
            }
            session.call = newCallState(msg.callId, false);
            session.call.state = 'ringing_in';
            showIncomingCallUI(peerId);
            return;
        }
        if (msg.type === 'CALL_ACCEPT') {
            if (session.call?.callId !== msg.callId || !session.call.isCallInitiator) return;
            clearTimeout(session.call.ringTimeout);
            await onCallAccepted(session, peerId);
            return;
        }
        if (msg.type === 'CALL_REJECT') {
            if (session.call?.callId !== msg.callId) return;
            showStatus('info', msg.reason === 'busy' ? '📵 Собеседник уже в другом звонке' : '📵 Звонок отклонён');
            endCall(peerId, null);
            return;
        }
        if (msg.type === 'CALL_CANCEL') {
            if (session.call?.callId !== msg.callId) return;
            showStatus('info', '📵 Собеседник отменил звонок');
            endCall(peerId, null);
            return;
        }
        if (msg.type === 'CALL_HANGUP') {
            if (session.call?.callId !== msg.callId) return;
            showStatus('info', '📴 Звонок завершён собеседником');
            endCall(peerId, null);
            return;
        }
        if (msg.type === 'CALL_SDP') {
            if (session.call?.callId !== msg.callId) return;
            await handleCallSdp(session, peerId, msg.sdp);
            return;
        }

        if (msg.type === 'HANDSHAKE_PK') {
            const buf = new Uint8Array(base64ToArrayBuffer(msg.pk));
            if (buf.byteLength !== 1248) throw new Error("Неверная длина пакета рукопожатия");

            const friendIkPub      = buf.slice(0, 32);
            const friendEphX25519  = buf.slice(32, 64);
            const friendEphMlKemPk = buf.slice(64, 1248);
            session.tempFriendEphX25519 = friendEphX25519;

            const friendShortId  = await deriveShortId(friendIkPub);
            const friendIkPubB64 = arrayBufferToBase64(friendIkPub.buffer);
            const tofuResult = await tofuContact(friendShortId, friendIkPubB64);

            const identityMismatch = tofuResult === 'mismatch' || friendShortId !== peerId;

            if (identityMismatch) {
                console.error('Identity key verification failed for', friendShortId, 'expected', peerId);

                const label = tofuResult === 'mismatch'
                    ? '⚠️ Ключ безопасности собеседника изменился с прошлого раза!'
                    : '⚠️ Полученный ключ не соответствует ожидаемому собеседнику!';

                showStatus('error', label + ' Соединение заблокировано.');
                if (activeContactId === peerId) {
                    updateLog(label + ' Возможна атака "человек посередине". Соединение прервано.', 'error');
                    const warnEl = document.getElementById('fpTofuWarn');
                    if (warnEl) {
                        warnEl.textContent = label + ' Если это ожидаемо, удалите контакт и добавьте заново.';
                        warnEl.style.display = 'block';
                    }
                }

                destroySession(peerId);
                if (activeContactId === peerId) { resetConnectButton(); updateChatHeader(); }
                renderContactsList();
                return;
            }

            const myIkPub = myIdentity.ikPub;
            let cmp = 0;
            for (let i = 0; i < 32 && cmp === 0; i++) {
                if (myIkPub[i] < friendIkPub[i]) cmp = -1;
                else if (myIkPub[i] > friendIkPub[i]) cmp = 1;
            }
            session.isInitiatorRole = cmp < 0;

            const dh1 = sodium.crypto_scalarmult(myIdentity.ikSec, friendIkPub);
            const dh4 = sodium.crypto_scalarmult(session.myEphKxKeyPair.privateKey, friendEphX25519);

            let termA, termB;
            if (session.isInitiatorRole) {
                termA = sodium.crypto_scalarmult(myIdentity.ikSec, friendEphX25519);
                termB = sodium.crypto_scalarmult(session.myEphKxKeyPair.privateKey, friendIkPub);
            } else {
                termA = sodium.crypto_scalarmult(session.myEphKxKeyPair.privateKey, friendIkPub);
                termB = sodium.crypto_scalarmult(myIdentity.ikSec, friendEphX25519);
            }

            const { ml_kem768 } = await getNobleMlKem();

            if (session.isInitiatorRole) {
                const { sharedSecret: pqSS, cipherText: pqCT } = ml_kem768.encapsulate(friendEphMlKemPk);
                const root = mixRoot(dh1, termA, termB, dh4, pqSS);
                secureZero(dh1); secureZero(termA); secureZero(termB); secureZero(dh4); secureZero(pqSS);
                finalizeHandshake(session, peerId, root, friendEphX25519);
                session.dataChannel.send(JSON.stringify({ type:'HANDSHAKE_CT', ct: arrayBufferToBase64(pqCT.buffer) }));
            } else {
                session.pendingDH = { dh1, termA, termB, dh4 };
            }
        }
        else if (msg.type === 'HANDSHAKE_CT') {
            const pending = session.pendingDH;
            if (!pending) throw new Error("Нет ожидающего рукопожатия");
            const { dh1, termA, termB, dh4 } = pending;
            session.pendingDH = null;

            const ctBuf = new Uint8Array(base64ToArrayBuffer(msg.ct));
            const { ml_kem768 } = await getNobleMlKem();
            const pqSS = ml_kem768.decapsulate(ctBuf, session.myEphMlKemPair.secretKey);
            const root = mixRoot(dh1, termA, termB, dh4, pqSS);
            secureZero(dh1); secureZero(termA); secureZero(termB); secureZero(dh4); secureZero(pqSS);
            finalizeHandshake(session, peerId, root, session.tempFriendEphX25519);
            session.dataChannel.send(JSON.stringify({ type:'HANDSHAKE_DONE' }));
            switchToChat(peerId);
        }
        else if (msg.type === 'HANDSHAKE_DONE') {
            switchToChat(peerId);
            // Bob has confirmed he already finalized his ratchet state (he sent
            // HANDSHAKE_DONE right after doing so), so it's safe to prime him now.
            sendRatchetPrimer(session);
        }
    } catch(e) {
        console.error("P2P data error:", e);
    }
}

function mixRoot(dh1, dh2, dh3, dh4, pq) {
    const combined = new Uint8Array(dh1.length + dh2.length + dh3.length + dh4.length + pq.length);
    let off = 0;
    for (const b of [dh1, dh2, dh3, dh4, pq]) { combined.set(b, off); off += b.length; }
    return sodium.crypto_generichash(sodium.crypto_aead_xchacha20poly1305_ietf_KEYBYTES, combined);
}

function finalizeHandshake(session, peerId, rootKey, friendEphX25519Pub) {
    session.currentSymmetricKey = rootKey;
    computeSessionFingerprint(rootKey).then(fp => {
        session.sessionFingerprint = fp;
        if (activeContactId === peerId) {
            const btn = document.getElementById('btnFingerprint');
            if (btn) btn.disabled = false;
        }
    });
    session.ratchetState = RatchetOps.initState(rootKey, session.isInitiatorRole, friendEphX25519Pub, session.myEphKxKeyPair);
    session.isMlKemReady = true;
    if (activeContactId === peerId) updateChatHeader();
    renderContactsList();

    if (session.myEphMlKemPair?.secretKey) secureZero(session.myEphMlKemPair.secretKey);
    session.myEphMlKemPair = null;
    session.tempFriendEphX25519 = null;
}

// ═══════════════════════════════════════════════════════════
//  RATCHET AUTO-PRIMING
// ═══════════════════════════════════════════════════════════
// Which side is Double-Ratchet "Alice" (session.isInitiatorRole) is decided
// purely by comparing the two identity keys — it has nothing to do with who
// actually clicked "Подключиться" in the UI, and it never changes for a
// given contact pair. That means, without this, "Alice" always gets a ready
// CKs from RatchetOps.initState() and can type immediately, while "Bob" is
// stuck with CKs === null until Alice's first real message arrives and runs
// a DH ratchet step — i.e. on every fresh connection *and every reconnect*,
// the same person for a given pair is forced to "write first" just to
// unlock the other person's send button. Over long-term use (especially
// with the frequent reconnects the app already does) that's annoying.
//
// Fix: right after a handshake finishes, whichever side is "Alice" fires
// one throwaway ratchet-encrypted packet at "Bob" automatically. It carries
// no text, is never rendered as a bubble, never persisted to IndexedDB,
// never acked/read-receipted, and doesn't touch unread counts or
// lastSeenAt — its only job is to run the DH ratchet step on Bob's side so
// his CKs is populated and he can send immediately too. Envelope type 'sys'
// keeps it fully out of the normal message pipeline.
async function sendRatchetPrimer(session) {
    if (!session?.isInitiatorRole) return;          // only "Alice" needs to prime the other side
    if (!session.ratchetState?.CKs) return;          // ratchet not initialized yet — nothing to send
    if (!session.dataChannel || session.dataChannel.readyState !== 'open') return;
    try {
        const rData      = RatchetOps.ratchetEncrypt(session.ratchetState);
        const plainBytes = packPayload({});
        const ctB64      = await encryptPayload(plainBytes, AAD_SYS, rData.mk);
        const envelope   = buildEnvelope('sys', ctB64, rData.header);
        session.dataChannel.send(JSON.stringify({ type: 'CHAT_MSG', payload: envelope }));
    } catch (e) {
        console.error("Ratchet primer send error:", e);
    }
}

function switchToChat(peerId) {
    const session = sessions.get(peerId);
    if (session) session.isMlKemReady = true;
    renderContactsList();

    if (activeContactId === peerId) {
        updateChatHeader();
        document.getElementById('connectPanel').style.display = 'none';
        showStatus('success', '🔐 P2P шифрованный канал установлен!');
        resendPendingAcknowledgements(peerId);
    } else {
        showStatus('success', `🔐 Защищённый канал с ${getDisplayName(contacts.get(peerId))} установлен!`);
    }
}

function resendPendingAcknowledgements(peerId) {
    const session = sessions.get(peerId);
    if (!session?.dataChannel || session.dataChannel.readyState !== 'open') return;
    if (activeContactId !== peerId) return; // bubbles for this peer only exist in the DOM when its chat is open
    document.querySelectorAll('.msg-bubble.msg-friend').forEach(bubble => {
        const msgId = bubble.dataset.msgId;
        if (msgId && !ackedMessages.has(msgId)) {
            session.dataChannel.send(JSON.stringify({ type:'MSG_ACK', msgId }));
            setTimeout(() => {
                if (session.dataChannel?.readyState === 'open')
                    session.dataChannel.send(JSON.stringify({ type:'MSG_READ', msgId }));
            }, 500);
            ackedMessages.add(msgId);
        }
    });
}

// ═══════════════════════════════════════════════════════════
//  VOICE CALLS
//
//  Design notes (see also chat with Wolf that produced this section):
//
//  - Call *signaling* (offer/accept/reject/cancel/hangup + the renegotiated
//    SDP for the audio track) rides the already-open, already TOFU-verified
//    data channel — not raw MQTT. That channel only exists once HANDSHAKE_PK
//    has already pinned the peer's identity key, so nothing here needs its
//    own authentication step. New ICE candidates thrown up by adding the
//    audio track (rare — same bundled transport as the data channel) reuse
//    the existing MQTT 'candidate' relay in handleSignalMessage(), so no new
//    signaling path was needed for that either.
//
//  - Call keys are derived from the *current* Double Ratchet root key
//    (session.ratchetState.RK), which — thanks to mixRoot()/finalizeHandshake()
//    — is itself seeded from the hybrid X25519 + ML-KEM-768 handshake. So
//    call audio inherits the same post-quantum-protected root of trust as
//    text messages, fresh per call, without touching or advancing the
//    messaging ratchet at all (we only *read* RK, never mutate it here).
//
//  - We deliberately do NOT run a full per-frame Double Ratchet (DH step per
//    audio frame) here. Two reasons: (1) audio frames arrive ~50/sec and a
//    scalar-mult per frame is wasteful for no real benefit; (2) real-time
//    media over SRTP is lossy/unordered by design (no retransmission), so a
//    strict "advance the ratchet by one for every frame" scheme desyncs the
//    instant a single packet is dropped — recovering from that needs either
//    per-frame ratchet metadata (bigger packets, more complexity) or a
//    fast-forwardable skipped-key cache like the text ratchet already has.
//    That's real, solvable engineering (Signal/MLS-style call encryption
//    does it), but it's a project on its own. What we do instead — a single
//    AEAD key derived fresh per call, discarded at hangup, with a random
//    192-bit nonce per frame — gives every call forward secrecy *between*
//    calls (compromise one call's key, older/future calls are unaffected)
//    and full post-quantum-derived confidentiality of the actual audio
//    content, which is what was asked for. What it does NOT give is
//    moment-to-moment forward secrecy *within* one live call (a key
//    compromised mid-call exposes that whole call). Flagging that honestly
//    rather than pretending otherwise.
//
//  - The extra AEAD layer runs over WebRTC's Insertable Streams API, which
//    encrypts/decrypts the actual encoded audio frames before/after SRTP —
//    so audio content is protected independently of (on top of) WebRTC's
//    own DTLS-SRTP transport encryption. Insertable Streams support is not
//    universal (solid in Chromium-based browsers, patchier elsewhere), so
//    this is feature-detected: if unavailable, the call still works and is
//    still protected by standard WebRTC DTLS-SRTP — whose handshake
//    fingerprint is itself exchanged over our authenticated data channel,
//    which rules out a MITM on the call — it just won't carry the extra
//    post-quantum layer. The in-call bar shows which mode is active.
// ═══════════════════════════════════════════════════════════

function newCallState(callId, isCallInitiator) {
    return {
        callId,
        isCallInitiator,
        state: 'ringing_out',   // ringing_out | ringing_in | connecting | active
        localStream: null,
        remoteStream: null,
        audioReceiver: null,
        isMuted: false,
        startTime: null,
        timerInterval: null,
        ringTimeout: null,
        callTxKey: null,
        callRxKey: null,
        insertableActive: false
    };
}

function isInsertableStreamsSupported() {
    return typeof RTCRtpSender !== 'undefined' && 'createEncodedStreams' in RTCRtpSender.prototype &&
           typeof RTCRtpReceiver !== 'undefined' && 'createEncodedStreams' in RTCRtpReceiver.prototype;
}

// Derives this call's symmetric keys from the session's current ratchet root
// key + the call's random id. Both peers compute the same values independently
// (no extra round trip needed) since both already share RK and both saw the
// callId in the plaintext CALL_OFFER. isInitiatorRole is the stable A/B label
// already agreed during the text handshake — reused here purely as a label so
// each side's "tx" key equals the other side's "rx" key, nothing more.
function deriveCallKeys(session, callId) {
    const material = new Uint8Array(CALL_KEY_CONTEXT.length + callId.length);
    material.set(CALL_KEY_CONTEXT, 0);
    material.set(te.encode(callId), CALL_KEY_CONTEXT.length);
    const callRoot = sodium.crypto_generichash(32, material, session.ratchetState.RK);
    const isA = session.isInitiatorRole;
    const callTxKey = sodium.crypto_generichash(32, te.encode(isA ? 'A2B' : 'B2A'), callRoot);
    const callRxKey = sodium.crypto_generichash(32, te.encode(isA ? 'B2A' : 'A2B'), callRoot);
    secureZero(callRoot);
    return { callTxKey, callRxKey };
}

function attachCallEncryption(session) {
    if (!session.call || session.call.insertableActive) return;
    if (!session.audioSender || !session.call.audioReceiver) return;
    if (!session.call.callTxKey || !session.call.callRxKey) return;
    if (!isInsertableStreamsSupported()) return;

    try {
        const senderStreams = session.audioSender.createEncodedStreams();
        const encryptTf = new TransformStream({ transform: (chunk, controller) => encryptCallFrame(session, chunk, controller) });
        senderStreams.readable.pipeThrough(encryptTf).pipeTo(senderStreams.writable);

        const receiverStreams = session.call.audioReceiver.createEncodedStreams();
        const decryptTf = new TransformStream({ transform: (chunk, controller) => decryptCallFrame(session, chunk, controller) });
        receiverStreams.readable.pipeThrough(decryptTf).pipeTo(receiverStreams.writable);

        session.call.insertableActive = true;
    } catch (e) {
        console.warn('Insertable Streams недоступны — звонок защищён только стандартным WebRTC SRTP:', e);
        session.call.insertableActive = false;
    }
}

function encryptCallFrame(session, chunk, controller) {
    try {
        const nonce = sodium.randombytes_buf(sodium.crypto_aead_xchacha20poly1305_ietf_NPUBBYTES);
        const ct    = sodium.crypto_aead_xchacha20poly1305_ietf_encrypt(new Uint8Array(chunk.data), AAD_CALL_FRAME, null, nonce, session.call.callTxKey);
        const out   = new Uint8Array(nonce.length + ct.length);
        out.set(nonce, 0); out.set(ct, nonce.length);
        chunk.data = out.buffer;
        controller.enqueue(chunk);
    } catch { /* drop rather than send a frame we failed to encrypt */ }
}

function decryptCallFrame(session, chunk, controller) {
    try {
        const buf = new Uint8Array(chunk.data);
        const NONCE_LEN = sodium.crypto_aead_xchacha20poly1305_ietf_NPUBBYTES;
        const plain = sodium.crypto_aead_xchacha20poly1305_ietf_decrypt(null, buf.slice(NONCE_LEN), AAD_CALL_FRAME, buf.slice(0, NONCE_LEN), session.call.callRxKey);
        chunk.data = plain.buffer;
        controller.enqueue(chunk);
    } catch { /* corrupted/foreign frame — drop silently rather than play garbage audio */ }
}

// ── Call lifecycle ──
async function startCall(peerId) {
    if (activeCallPeerId) { showStatus('error', 'Вы уже в другом звонке'); return; }
    const session = sessions.get(peerId);
    if (!session?.isMlKemReady || session.dataChannel?.readyState !== 'open') {
        showStatus('error', 'Нужен установленный защищённый канал для звонка'); return;
    }

    let localStream;
    try {
        localStream = await navigator.mediaDevices.getUserMedia({ audio: true });
    } catch {
        showStatus('error', 'Доступ к микрофону запрещён или недоступен'); return;
    }

    const callId = crypto.randomUUID();
    session.call = newCallState(callId, true);
    session.call.localStream = localStream;
    activeCallPeerId = peerId;

    session.dataChannel.send(JSON.stringify({ type: 'CALL_OFFER', callId }));
    showOutgoingCallUI(peerId);

    session.call.ringTimeout = setTimeout(() => {
        if (session.call?.state === 'ringing_out') {
            showStatus('error', 'Собеседник не ответил');
            endCall(peerId, 'CALL_CANCEL');
        }
    }, CALL_RING_TIMEOUT_MS);
}

async function onCallAccepted(session, peerId) {
    try {
        session.call.state = 'connecting';
        showActiveCallUI(peerId);

        const track = session.call.localStream.getAudioTracks()[0];
        session.audioSender = session.peerConnection.addTrack(track, session.call.localStream);

        const { callTxKey, callRxKey } = deriveCallKeys(session, session.call.callId);
        session.call.callTxKey = callTxKey;
        session.call.callRxKey = callRxKey;

        const offer = await session.peerConnection.createOffer();
        await session.peerConnection.setLocalDescription(offer);
        session.dataChannel.send(JSON.stringify({ type: 'CALL_SDP', callId: session.call.callId, sdp: offer }));
    } catch (e) {
        showStatus('error', 'Ошибка запуска звонка: ' + e.message);
        endCall(peerId, 'CALL_HANGUP');
    }
}

// Handles both legs of the renegotiation: the callee gets an 'offer' (from
// the caller, sent right after CALL_ACCEPT) and answers it; the caller gets
// the resulting 'answer' back.
async function handleCallSdp(session, peerId, sdp) {
    try {
        if (sdp.type === 'offer') {
            await session.peerConnection.setRemoteDescription(new RTCSessionDescription(sdp));

            const track = session.call.localStream.getAudioTracks()[0];
            session.audioSender = session.peerConnection.addTrack(track, session.call.localStream);

            const { callTxKey, callRxKey } = deriveCallKeys(session, session.call.callId);
            session.call.callTxKey = callTxKey;
            session.call.callRxKey = callRxKey;

            const answer = await session.peerConnection.createAnswer();
            await session.peerConnection.setLocalDescription(answer);
            session.dataChannel.send(JSON.stringify({ type: 'CALL_SDP', callId: session.call.callId, sdp: answer }));
        } else if (sdp.type === 'answer') {
            await session.peerConnection.setRemoteDescription(new RTCSessionDescription(sdp));
        }
    } catch (e) {
        showStatus('error', 'Ошибка согласования звонка: ' + e.message);
        endCall(peerId, 'CALL_HANGUP');
    }
}

// Browsers don't universally expose the negotiated DTLS version as a plain
// field — this is a best-effort read of the WebRTC 'transport' stats report.
// Some newer browsers report `tlsVersion` directly; otherwise we infer it
// from the cipher suite name (the TLS 1.3 suites all start with
// TLS_AES_*/TLS_CHACHA20_*, per RFC 8446 — anything else negotiated by
// WebRTC's DTLS stack is DTLS 1.2). If neither is available we just show
// "DTLS" with no version rather than guessing.
async function detectDtlsVersion(peerConnection) {
    try {
        const stats = await peerConnection.getStats();
        for (const report of stats.values()) {
            if (report.type === 'transport') {
                if (report.tlsVersion) return report.tlsVersion;
                const cipher = report.dtlsCipher || '';
                if (/^TLS_(AES|CHACHA20)/i.test(cipher)) return '1.3';
                if (cipher) return '1.2';
            }
        }
    } catch {}
    return null;
}

// The data channel's own hybrid handshake (X25519 + ML-KEM-768, see
// startCryptoHandshake/finalizeHandshake) always happens for this app — but
// that's irrelevant to whether *this call's audio* is actually PQ-protected.
// That only holds when the extra Insertable Streams layer is active
// (session.call.insertableActive): its key is derived from the ratchet root,
// which is itself seeded from the ML-KEM-768 shared secret (see
// deriveCallKeys/mixRoot). When Insertable Streams isn't supported, the call
// falls back to plain WebRTC DTLS-SRTP — always present, but not PQ.
async function updateCallCryptoLabel(peerId) {
    const session = sessions.get(peerId);
    if (!session?.call || !session.peerConnection) return;
    const version = await detectDtlsVersion(session.peerConnection);
    if (activeCallPeerId !== peerId || !session.call) return; // call may have ended while stats were pending
    const dtlsLabel = 'DTLS' + (version ? ' ' + version : '');
    const icon = session.call.insertableActive ? '🔐' : '🔒';
    const pqLabel = session.call.insertableActive ? ' + ML-KEM-768 (постквант)' : ' (без постквантового слоя)';
    document.getElementById('callStatusText').textContent = `${icon} ${dtlsLabel}${pqLabel}`;
}

function beginActiveCallState(peerId) {
    const session = sessions.get(peerId);
    if (!session?.call || session.call.state === 'active') return;
    session.call.state = 'active';
    session.call.startTime = Date.now();
    if (activeCallPeerId === peerId) {
        document.getElementById('callStatusText').textContent = '🔒 DTLS…';
        updateCallCryptoLabel(peerId);
        session.call.timerInterval = setInterval(() => updateCallTimer(peerId), 1000);
    }
    renderContactsList();
}

function updateCallTimer(peerId) {
    if (activeCallPeerId !== peerId) return;
    const session = sessions.get(peerId);
    if (!session?.call?.startTime) return;
    const secs = Math.floor((Date.now() - session.call.startTime) / 1000);
    const m = String(Math.floor(secs / 60)).padStart(2, '0');
    const s = String(secs % 60).padStart(2, '0');
    document.getElementById('callTimer').textContent = `${m}:${s}`;
}

function acceptIncomingCall() {
    const peerId = pendingIncomingCallPeer;
    closeModal('callIncomingOverlay');
    stopRingtone();
    if (!peerId) return;
    const session = sessions.get(peerId);
    if (!session?.call) return;

    (async () => {
        let localStream;
        try {
            localStream = await navigator.mediaDevices.getUserMedia({ audio: true });
        } catch {
            showStatus('error', 'Доступ к микрофону запрещён');
            if (session.dataChannel?.readyState === 'open')
                session.dataChannel.send(JSON.stringify({ type: 'CALL_REJECT', callId: session.call.callId, reason: 'no_mic' }));
            session.call = null;
            pendingIncomingCallPeer = null;
            return;
        }
        session.call.localStream = localStream;
        session.call.state = 'connecting';
        activeCallPeerId = peerId;
        session.dataChannel.send(JSON.stringify({ type: 'CALL_ACCEPT', callId: session.call.callId }));
        showActiveCallUI(peerId);
        // The caller sends the renegotiated SDP offer next — handled in handleCallSdp().
    })();
}

function rejectIncomingCall() {
    const peerId = pendingIncomingCallPeer;
    closeModal('callIncomingOverlay');
    stopRingtone();
    pendingIncomingCallPeer = null;
    if (!peerId) return;
    const session = sessions.get(peerId);
    if (session?.call) {
        if (session.dataChannel?.readyState === 'open')
            session.dataChannel.send(JSON.stringify({ type: 'CALL_REJECT', callId: session.call.callId, reason: 'declined' }));
        session.call = null;
    }
}

function cancelOutgoingCall() {
    if (activeCallPeerId) endCall(activeCallPeerId, 'CALL_CANCEL');
}

function hangupActiveCall() {
    if (activeCallPeerId) endCall(activeCallPeerId, 'CALL_HANGUP');
}

function toggleCallMute() {
    const session = sessions.get(activeCallPeerId);
    if (!session?.call?.localStream) return;
    session.call.isMuted = !session.call.isMuted;
    session.call.localStream.getAudioTracks().forEach(t => t.enabled = !session.call.isMuted);
    const btn = document.getElementById('btnToggleMute');
    btn.classList.toggle('muted', session.call.isMuted);
    btn.textContent = session.call.isMuted ? '🔇' : '🎤';
}

function setCallVolume(value) {
    document.getElementById('remoteCallAudio').volume = Math.max(0, Math.min(100, Number(value))) / 100;
}

function endCall(peerId, notifyType) {
    stopRingtone();
    const session = sessions.get(peerId);
    if (session?.call) {
        if (notifyType && session.dataChannel?.readyState === 'open') {
            try { session.dataChannel.send(JSON.stringify({ type: notifyType, callId: session.call.callId })); } catch {}
        }
        clearTimeout(session.call.ringTimeout);
        clearInterval(session.call.timerInterval);
        session.call.localStream?.getTracks().forEach(t => t.stop());
        if (session.audioSender) {
            try { session.peerConnection.removeTrack(session.audioSender); } catch {}
            session.audioSender = null;
        }
        if (session.call.callTxKey) secureZero(session.call.callTxKey);
        if (session.call.callRxKey) secureZero(session.call.callRxKey);
        session.call = null;
    }
    if (activeCallPeerId === peerId) {
        activeCallPeerId = null;
        closeModal('callOutgoingOverlay');
        closeModal('callIncomingOverlay');
        document.getElementById('callActiveBar').style.display = 'none';
        document.getElementById('remoteCallAudio').srcObject = null;
    }
    if (pendingIncomingCallPeer === peerId) pendingIncomingCallPeer = null;
    updateCallButtonState();
    renderContactsList();
}

// ── Call UI ──
function showOutgoingCallUI(peerId) {
    const c = contacts.get(peerId);
    document.getElementById('callOutAvatar').textContent = avatarLetter((c?.nickname && c.nickname !== c.shortId) ? c.nickname : null);
    document.getElementById('callOutAvatar').style.background = avatarColor(peerId);
    document.getElementById('callOutName').textContent = getDisplayName(c);
    openModal('callOutgoingOverlay');
    updateCallButtonState();
}

function showIncomingCallUI(peerId) {
    pendingIncomingCallPeer = peerId;
    const c = contacts.get(peerId);
    document.getElementById('callInAvatar').textContent = avatarLetter((c?.nickname && c.nickname !== c.shortId) ? c.nickname : null);
    document.getElementById('callInAvatar').style.background = avatarColor(peerId);
    document.getElementById('callInName').textContent = getDisplayName(c);
    openModal('callIncomingOverlay');
    playRingtone();
}

function showActiveCallUI(peerId) {
    closeModal('callOutgoingOverlay');
    closeModal('callIncomingOverlay');
    stopRingtone();
    const c = contacts.get(peerId);
    document.getElementById('callBarPeerName').textContent = getDisplayName(c);
    document.getElementById('callTimer').textContent = '00:00';
    document.getElementById('callStatusText').textContent = 'Соединение...';
    document.getElementById('callVolumeSlider').value = 100;
    document.getElementById('btnToggleMute').classList.remove('muted');
    document.getElementById('btnToggleMute').textContent = '🎤';
    document.getElementById('callActiveBar').style.display = 'flex';
    updateCallButtonState();
}

function updateCallButtonState() {
    const btn = document.getElementById('btnStartCall');
    if (!btn || !activeContactId) return;
    const session = sessions.get(activeContactId);
    btn.disabled = !session?.isMlKemReady || !!activeCallPeerId;
}

function playRingtone() {
    stopRingtone();
    const ring = () => {
        try {
            const AudioContext = window.AudioContext || window.webkitAudioContext;
            if (!AudioContext) return;
            const ctx = new AudioContext();
            const osc = ctx.createOscillator(), gain = ctx.createGain();
            osc.type = 'sine'; osc.frequency.setValueAtTime(660, ctx.currentTime);
            gain.gain.setValueAtTime(0.12, ctx.currentTime);
            gain.gain.exponentialRampToValueAtTime(0.001, ctx.currentTime + 0.5);
            osc.connect(gain); gain.connect(ctx.destination);
            osc.start(); osc.stop(ctx.currentTime + 0.5);
        } catch {}
    };
    ring();
    ringtoneInterval = setInterval(ring, 1500);
}

function stopRingtone() { clearInterval(ringtoneInterval); ringtoneInterval = null; }

// ═══════════════════════════════════════════════════════════
//  MESSAGE STATUS
// ═══════════════════════════════════════════════════════════
function updateMessageStatus(msgId, newStatus) {
    const entry = messageStatusMap.get(msgId);
    if (!entry) return;
    entry.status = newStatus;
    // Once delivery is confirmed we no longer need to be able to resend this
    // exact message, so drop the cached copy (which, for file messages, can
    // be holding onto real memory).
    if (newStatus === 'delivered' || newStatus === 'read') entry.resend = null;
    const el = entry.element?.querySelector('.msg-status');
    if (!el) return;
    if (newStatus === 'sent')      { el.innerHTML = '✓';  el.style.color = 'var(--text-color)'; el.style.opacity = '0.5'; el.title = ''; }
    else if (newStatus === 'delivered') { el.innerHTML = '✓✓'; el.style.color = 'var(--text-color)'; el.style.opacity = '0.7'; el.title = ''; }
    else if (newStatus === 'read') { el.innerHTML = '✓✓'; el.style.color = '#4fc3f7'; el.style.opacity = '1'; el.title = ''; }
    updateMsgStatus(msgId, newStatus);
}

// Marks a message as genuinely failed to deliver — called only from real
// events (send() throwing, the data channel closing mid-send, or the
// connection being declared lost while this message was still unacked)
// rather than from a fixed timer, since on a slow connection "hasn't been
// acked yet" and "failed" are not the same thing. Adds a retry (🔄) button
// next to the existing reply/copy/delete actions when the original content
// needed to resend is still available.
function markMessageFailed(gId) {
    const entry = messageStatusMap.get(gId);
    if (!entry || entry.status === 'failed') return;
    entry.status = 'failed';
    const bubble = entry.element;
    const el = bubble?.querySelector('.msg-status');
    if (el) { el.innerHTML = '⚠'; el.style.color = 'var(--danger-color)'; el.style.opacity = '1'; el.title = 'Не доставлено'; }
    if (bubble && entry.resend && !bubble.querySelector('[data-action="retry"]')) {
        const btn = document.createElement('button');
        btn.className = 'msg-action-btn';
        btn.dataset.action = 'retry';
        btn.dataset.target = gId;
        btn.title = 'Повторить отправку';
        btn.textContent = '🔄';
        bubble.appendChild(btn);
    }
    updateMsgStatus(gId, 'failed');
}

// ═══════════════════════════════════════════════════════════
//  CHAT SEND & RECEIVE
// ═══════════════════════════════════════════════════════════
async function chatEncrypt() {
    if (!getActiveSession()?.isMlKemReady) { showStatus('error','Канал не подключён'); return; }
    const input    = document.getElementById('chatInput');
    const text     = input.value.trim();
    const hasFiles = chatAttachedFiles.length > 0;
    if (!text && !hasFiles) { showStatus('error','Введите сообщение или прикрепите файл'); return; }

    const filesToSend = chatAttachedFiles.slice();
    const replyId      = replyToGlobalId;

    clearAttachedFiles();
    stopTypingIndicator();
    input.value = ''; autoResizeInput(); cancelReply();

    await composeAndSendMessage({ text, files: filesToSend, replyToGId: replyId });
}

// Core of both a normal send and a retry: builds the message, ratchet-
// encrypts it, renders the local bubble, persists it, and hands it to
// sendEnvelope() — marking it 'failed' (rather than leaving it stuck) if the
// send doesn't actually make it out. Called with fresh plaintext/files every
// time, including on retry, so a retried message is a brand-new ratchet step
// and a brand-new message — it reappears at the bottom of the chat like any
// other freshly-sent message rather than trying to reuse a possibly-already-
// consumed ratchet position.
async function composeAndSendMessage({ text, files, replyToGId }) {
    const session = getActiveSession();
    if (!session?.isMlKemReady) { showStatus('error','Канал не подключён'); return null; }
    const hasFiles = !!(files && files.length);
    if (!text && !hasFiles) return null;

    try {
        const msgGlobalId = crypto.randomUUID();
        const metadata     = { gId: msgGlobalId };

        if (replyToGId) {
            metadata.rId     = replyToGId;
            metadata.rSender = getMessageSender(replyToGId);
            metadata.rPrev   = getMessagePreview(replyToGId);
        }

        const rData = RatchetOps.ratchetEncrypt(session.ratchetState);
        let plainBytes, ctB64, envelope;

        if (hasFiles) {
            metadata.files = files.map(f => ({ name: f.file.name, type: f.file.type, size: f.file.size }));
            if (text) metadata.txt = text;
            plainBytes = packMultiPayload(metadata, files.map(f => f.data));
            ctB64      = await encryptPayload(plainBytes, AAD_FILE, rData.mk);
            envelope   = buildEnvelope('file', ctB64, rData.header);

            addMessageBubble({
                side: 'mine', globalId: msgGlobalId, text: text || null,
                filesInfo: files.map(f => ({ name: f.file.name, size: f.file.size, type: f.file.type, mediaData: f.data, downloadData: f.data })),
                replyTo: replyToGId,
                resendPayload: { text, files, replyToGId }
            });
        } else {
            metadata.txt = text;
            plainBytes   = packPayload(metadata);
            ctB64        = await encryptPayload(plainBytes, AAD_MESSAGE, rData.mk);
            envelope     = buildEnvelope('msg', ctB64, rData.header);
            addMessageBubble({
                side: 'mine', globalId: msgGlobalId, text, replyTo: replyToGId,
                resendPayload: { text, files: [], replyToGId }
            });
        }

        await persistMessage(activeContactId, {
            gId:       msgGlobalId,
            direction: 'out',
            text:      text || null,
            fileMeta:  hasFiles ? files.map(f => ({ name: f.file.name })) : null,
            ts:        Date.now(),
            status:    'sent',
            replyToGId: replyToGId || null
        });

        const ok = await sendEnvelope(session, envelope, hasFiles);
        if (!ok) markMessageFailed(msgGlobalId);

        return msgGlobalId;
    } catch (e) {
        showStatus('error','Ошибка отправки: ' + e.message);
        return null;
    }
}

// Retries a failed message: removes the old failed bubble/record entirely
// and re-sends the same text/attachments as a fresh message, which lands at
// the bottom of the chat like any newly-sent message.
async function retryMessage(gId) {
    const entry = messageStatusMap.get(gId);
    if (!entry?.resend) { showStatus('error','Не удалось повторить отправку — исходные данные недоступны'); return; }
    const { text, files, replyToGId } = entry.resend;

    const oldEl = entry.element;
    if (oldEl) oldEl.remove();
    messageStatusMap.delete(gId);
    globalToLocalMap.delete(gId);
    replyInfoCache.delete(gId);
    await deleteMsgFromDB(gId);
    updateChatEmptyState();

    await composeAndSendMessage({ text, files: files || [], replyToGId: replyToGId || null });
}

async function receiveMessage(session, peerId, envelopeB64) {
    try {
        const env = parseEnvelope(envelopeB64);
        if (!env) throw new Error("Неверный конверт");
        if (!env.rh) throw new Error("Нет заголовка Ratchet");

        // Silent ratchet-priming packet (see sendRatchetPrimer): run it through
        // the ratchet and MAC-verify it like any other message so a forged
        // packet can't desync the ratchet, but never show/store/ack it — it
        // carries no user content at all.
        if (env.type === 'sys') {
            const rRes = RatchetOps.ratchetDecryptTentative(session.ratchetState, env.rh);
            await decryptPayload(env.ct, AAD_SYS, rRes.mk);
            RatchetOps.commitState(session, rRes.tentativeState, rRes.skipKeyToRemove);
            return;
        }

        const aadPrefix = env.type === 'file' ? AAD_FILE : AAD_MESSAGE;

        const rRes = RatchetOps.ratchetDecryptTentative(session.ratchetState, env.rh);
        const res  = await decryptPayload(env.ct, aadPrefix, rRes.mk);
        RatchetOps.commitState(session, rRes.tentativeState, rRes.skipKeyToRemove);

        let metadata, filesInfo = null;
        if (env.type === 'file') {
            const unpacked = unpackMultiPayload(res.data);
            metadata = unpacked.metadata;
            filesInfo = metadata.files.map((f, i) => ({
                name: f.name, size: f.size, type: f.type,
                mediaData: unpacked.buffers[i], downloadData: unpacked.buffers[i]
            }));
        } else {
            metadata = unpackPayload(res.data).metadata;
        }

        // Only draw the bubble if this peer's chat is actually the one open right now —
        // it still gets decrypted, persisted and acked either way. Note that by the
        // time we get here the *entire* envelope — every bundled attachment — has
        // already arrived and been reassembled (see handleChunk), so a multi-photo
        // message is only ever rendered once, complete, never partially.
        if (activeContactId === peerId) {
            addMessageBubble({ side:'friend', globalId:metadata.gId,
                text: metadata.txt || null, filesInfo, timeCheck: res.timeCheck,
                replyTo: metadata.rId, replyPreview: metadata.rPrev, replySender: metadata.rSender });
        }

        await persistMessage(peerId, {
            gId:       metadata.gId,
            direction: 'in',
            text:      metadata.txt || null,
            fileMeta:  env.type === 'file' ? metadata.files.map(f => ({ name: f.name })) : null,
            ts:        Date.now(),
            status:    'read',
            replyToGId: metadata.rId || null
        });

        sendAckAndRead(session, metadata.gId);
        ackedMessages.add(metadata.gId);
        playNotificationSound();

        const c = contacts.get(peerId);
        if (c) { c.lastSeenAt = Date.now(); await saveContact(c); renderContactsList(); }
    } catch(e) {
        console.error("Receive error:", e);
        if (activeContactId === peerId) showStatus('error','Ошибка приёма: ' + e.message);
    }
}

function sendAckAndRead(session, msgId) {
    if (!session?.dataChannel || session.dataChannel.readyState !== 'open') return;
    session.dataChannel.send(JSON.stringify({ type:'MSG_ACK', msgId }));
    setTimeout(() => {
        if (session.dataChannel?.readyState === 'open') session.dataChannel.send(JSON.stringify({ type:'MSG_READ', msgId }));
    }, 400);
}

// Returns true once the whole envelope has actually been handed off to the
// data channel, false if it didn't make it (channel closed mid-send, or a
// send() call itself threw). The caller uses this to mark the message
// 'failed' (with a retry button) instead of leaving it stuck on a checkmark
// that never resolves either way.
async function sendEnvelope(session, envelope, isFile) {
    if (!session?.dataChannel || session.dataChannel.readyState !== 'open') return false;

    const BUFFER_HIGH = 1024 * 1024;
    const BUFFER_LOW  = 256 * 1024;

    function waitForDrain() {
        return new Promise(resolve => {
            const dc = session.dataChannel;
            if (!dc || dc.bufferedAmount <= BUFFER_LOW) { resolve(); return; }
            let done = false;
            const finish = () => { if (!done) { done = true; clearInterval(poll); resolve(); } };
            dc.bufferedAmountLowThreshold = BUFFER_LOW;
            dc.addEventListener('bufferedamountlow', finish, { once: true });
            const poll = setInterval(() => {
                const cur = session.dataChannel;
                if (!cur || cur.readyState !== 'open' || cur.bufferedAmount <= BUFFER_LOW) {
                    finish();
                }
            }, 50);
        });
    }

    if (isFile) { try { session.dataChannel.send(JSON.stringify({ type: 'PEER_STATUS', status: 'sending_file' })); } catch {} }

    let success = true;

    if (envelope.length <= CHUNK_SIZE) {
        try {
            session.dataChannel.send(JSON.stringify({ type: 'CHAT_MSG', payload: envelope }));
        } catch {
            success = false;
        }
    } else {
        // Large / multi-attachment payloads go out as ordered, reliable
        // chunks with no fixed time budget — there's no deadline here, only
        // "did every chunk make it out before the channel closed". While
        // this loop runs we suspend the heartbeat (see suspendHeartbeat):
        // otherwise our own PING, queued behind every chunk still waiting
        // its turn on this same ordered channel, can arrive so late that the
        // "no PONG in 30s" watchdog fires purely from that head-of-line
        // blocking — not an actual dropped connection — and tears down a
        // transfer that was proceeding fine, just slowly on a weak link.
        // A genuine drop is still caught immediately via dataChannel.onclose
        // / oniceconnectionstatechange regardless of the suspension.
        session.transferInFlight = (session.transferInFlight || 0) + 1;
        suspendHeartbeat(session, true);
        try {
            const msgId = crypto.randomUUID();
            const total = Math.ceil(envelope.length / CHUNK_SIZE);

            for (let i = 0; i < total; i++) {
                if (!session.dataChannel || session.dataChannel.readyState !== 'open') {
                    success = false;
                    break;
                }
                if (session.dataChannel.bufferedAmount > BUFFER_HIGH) {
                    await waitForDrain();
                }
                if (!session.dataChannel || session.dataChannel.readyState !== 'open') {
                    success = false;
                    break;
                }
                try {
                    session.dataChannel.send(JSON.stringify({
                        type: 'CHAT_CHUNK', msgId, index: i, total,
                        data: envelope.slice(i * CHUNK_SIZE, (i + 1) * CHUNK_SIZE)
                    }));
                } catch {
                    success = false;
                    break;
                }
            }
        } finally {
            session.transferInFlight = Math.max(0, (session.transferInFlight || 1) - 1);
            if (session.transferInFlight === 0) suspendHeartbeat(session, false);
        }
    }

    if (!success) showStatus('error', '⚠️ Соединение прервано во время отправки. Сообщение можно отправить повторно.');
    if (isFile && session.dataChannel?.readyState === 'open') { try { session.dataChannel.send(JSON.stringify({ type: 'PEER_STATUS', status: 'idle' })); } catch {} }

    return success;
}

function handleChunk(session, peerId, msg) {
    const { msgId, index, total, data } = msg;
    if (!chunkBuffer.has(msgId)) {
        chunkBuffer.set(msgId, { total, parts: new Array(total).fill(null), count: 0 });
        session.transferInFlight = (session.transferInFlight || 0) + 1;
        suspendHeartbeat(session, true);
    }
    const entry = chunkBuffer.get(msgId);
    if (entry.parts[index] === null) { entry.parts[index] = data; entry.count++; }
    if (entry.count === entry.total) {
        chunkBuffer.delete(msgId);
        session.transferInFlight = Math.max(0, (session.transferInFlight || 1) - 1);
        if (session.transferInFlight === 0) suspendHeartbeat(session, false);
        receiveMessage(session, peerId, entry.parts.join(''));
    }
}

// ═══════════════════════════════════════════════════════════
//  UI — CHAT BUBBLES
// ═══════════════════════════════════════════════════════════
// opts.filesInfo, when present, is an array of one or more
// { name, size, type, mediaData?, downloadData? } — one entry per attachment
// bundled into this message. mediaData/downloadData are the raw bytes, when
// available (always for a message we're sending; also for a message we just
// received in full — see receiveMessage — but not for stubs rebuilt from
// history on reload, since raw attachment bytes aren't persisted to
// IndexedDB). A single attachment renders like before; two or more render as
// a compact gallery grid.
function addMessageBubble(opts) {
    const container = document.getElementById('chatMessages');
    const empty = container.querySelector('.chat-empty');
    if (empty) empty.remove();

    const msgId = ++chatMessageCounter;
    if (opts.globalId) {
        globalToLocalMap.set(opts.globalId, msgId);
        registerMessageInCache(opts.globalId, opts.side, opts.text, opts.filesInfo?.[0]?.name, opts.filesInfo?.length || 0);
    }

    const bubble = document.createElement('div');
    bubble.className = 'msg-bubble msg-' + opts.side;
    bubble.id = 'msg-' + msgId;
    if (opts.globalId) bubble.dataset.msgId = opts.globalId;
    if (opts.text) bubble._decryptedText = opts.text;

    const peerName = getDisplayName(contacts.get(activeContactId));
    let html = `<div class="msg-sender">${opts.side === 'mine' ? myIdentity.nickname : peerName}</div>`;

    if (opts.replyTo) {
        const rSender  = opts.replySender || getMessageSender(opts.replyTo) || 'Собеседник';
        const rPreview = opts.replyPreview || getMessagePreview(opts.replyTo) || '…';
        if (!replyInfoCache.has(opts.replyTo)) replyInfoCache.set(opts.replyTo, { sender: rSender, preview: rPreview });
        html += `<div class="msg-reply-preview" data-action="scroll-to" data-target="${escapeHtml(opts.replyTo)}"><strong>${escapeHtml(rSender)}:</strong> ${escapeHtml(rPreview)}</div>`;
    }

    const downloadFiles = [];
    if (opts.filesInfo?.length) {
        const galleryItems = [];
        let chipsHtml = '';
        for (const f of opts.filesInfo) {
            if (f.downloadData || f.mediaData) downloadFiles.push({ name: f.name, type: f.type, data: f.downloadData || f.mediaData });

            const rawData  = f.mediaData;
            const verified = rawData ? getVerifiedMediaType(rawData) : null;
            let cat        = verified ? SAFE_MEDIA_TYPES[verified] : null;
            const isSafe   = !!(cat && rawData && !containsScriptContent(rawData));
            // Voice notes are recorded as audio/webm, but WebM's container magic
            // bytes look identical whether or not there's a video track, so the
            // byte-sniffed type alone can't tell them apart from a video/webm —
            // fall back to the filename convention used for recorded voice notes.
            if (isSafe && cat === 'video' && f.name?.includes('Voice_')) cat = 'audio';

            if (isSafe && (cat === 'image' || cat === 'video')) {
                const url = URL.createObjectURL(new Blob([rawData], { type: verified }));
                mediaObjectUrls.push(url);
                galleryItems.push({ url, cat });
            } else if (isSafe && cat === 'audio') {
                const url = URL.createObjectURL(new Blob([rawData], { type: verified }));
                mediaObjectUrls.push(url);
                chipsHtml += `<div class="msg-media"><div style="display:flex;gap:6px;"><audio src="${url}" controls controlsList="nodownload" style="flex:1;"></audio><select class="audio-speed-select" data-action="set-speed"><option value="0.5">0.5x</option><option value="1" selected>1x</option><option value="1.5">1.5x</option><option value="2">2x</option></select></div></div>`;
            } else {
                chipsHtml += `<div class="msg-file-info"><div class="msg-file-icon">${getFileIconEmoji(f.type)}</div>
                    <div class="msg-file-details"><div class="msg-file-name">${escapeHtml(f.name)}</div>
                    ${f.size ? `<div class="msg-file-size">${formatFileSize(f.size)}</div>` : ''}</div></div>`;
            }
        }

        if (galleryItems.length === 1) {
            const it = galleryItems[0];
            html += '<div class="msg-media">' + (it.cat === 'image'
                ? `<img src="${it.url}" data-action="view-image">`
                : `<video src="${it.url}" controls controlsList="nodownload"></video>`) + '</div>';
        } else if (galleryItems.length > 1) {
            const cols = galleryItems.length >= 3 ? 3 : 2;
            html += `<div class="msg-gallery" style="grid-template-columns:repeat(${cols},1fr);">` +
                galleryItems.map(it => it.cat === 'image'
                    ? `<img src="${it.url}" data-action="view-image" class="msg-gallery-item">`
                    : `<video src="${it.url}" controls controlsList="nodownload" class="msg-gallery-item"></video>`
                ).join('') + `</div>`;
        }
        html += chipsHtml;
    }

    if (opts.text) html += `<div class="msg-text">${escapeHtml(opts.text)}</div>`;
    if (opts.timeCheck?.warning) html += `<div class="msg-sig-warn">${escapeHtml(opts.timeCheck.message)}</div>`;

    const statusHtml = opts.side === 'mine' ? `<span class="msg-status">✓</span>` : '';
    html += `<div class="msg-meta"><span>${formatTime(new Date())}</span>${statusHtml}</div>`;

    if (!opts.filesInfo?.length && opts.text) html += `<button class="msg-action-btn" data-action="copy" data-msg-id="${msgId}">📋</button>`;
    html += `<button class="msg-action-btn" data-action="reply" data-target="${escapeHtml(opts.globalId || String(msgId))}">↩️</button>`;
    if (opts.globalId) html += `<button class="msg-action-btn" data-action="delete-msg" data-target="${escapeHtml(opts.globalId)}">🗑️</button>`;
    if (downloadFiles.length) html += `<button class="msg-action-btn" data-action="download" data-msg-id="${msgId}">💾</button>`;

    bubble.innerHTML = html;

    if (downloadFiles.length) bubble._downloadFiles = downloadFiles;

    container.appendChild(bubble);

    if (opts.side === 'mine' && opts.globalId) {
        messageStatusMap.set(opts.globalId, { status:'sent', element: bubble, sentAt: Date.now(), peerId: activeContactId, resend: opts.resendPayload || null });
    }

    container.scrollTop = container.scrollHeight;
    return msgId;
}

function getMessagePreview(gId) {
    const localId = globalToLocalMap.get(gId);
    if (localId) {
        const el = document.getElementById('msg-' + localId);
        if (el) {
            const t = el.querySelector('.msg-text'); if (t) return t.textContent.slice(0,60);
            const f = el.querySelector('.msg-file-name'); if (f) return '📎 ' + f.textContent;
            if (el.querySelector('.msg-gallery')) return '📷 Медиа';
        }
    }
    return replyInfoCache.get(gId)?.preview || '…';
}

function getMessageSender(gId) {
    const localId = globalToLocalMap.get(gId);
    if (localId) {
        const el = document.getElementById('msg-' + localId);
        if (el) return el.classList.contains('msg-mine') ? myIdentity.nickname : getDisplayName(contacts.get(activeContactId));
    }
    return replyInfoCache.get(gId)?.sender || '';
}

function registerMessageInCache(gId, side, text, fileName, fileCount = 0) {
    const sender  = side === 'mine' ? (myIdentity?.nickname || 'Вы') : getDisplayName(contacts.get(activeContactId));
    let preview;
    if (text) preview = text.slice(0,60);
    else if (fileCount > 1) preview = `📎 ${fileCount} вложений`;
    else if (fileName) preview = '📎 ' + fileName;
    else preview = '…';
    replyInfoCache.set(gId, { sender, preview });
}

function setReplyTo(gId) {
    replyToGlobalId = gId;
    document.getElementById('replyBarSender').textContent = getMessageSender(gId);
    document.getElementById('replyBarText').textContent   = getMessagePreview(gId);
    document.getElementById('chatReplyBar').classList.add('show');
    document.getElementById('chatInput').focus();
}

function cancelReply() { replyToGlobalId = null; document.getElementById('chatReplyBar').classList.remove('show'); }

function scrollToMessage(gId) {
    const el = document.getElementById('msg-' + globalToLocalMap.get(gId));
    if (el) {
        el.scrollIntoView({ behavior:'smooth', block:'center' });
        el.style.outline = '2px solid var(--primary-color)';
        setTimeout(() => el.style.outline = '', 1500);
    } else showStatus('info','Сообщение не найдено в истории');
}

function requestDeleteMessage(globalId) {
    msgIdToDelete = globalId;
    openModal('confirmDeleteMsgOverlay');
}

let chatIdPendingDeletion = null;

function toggleChatMenu(event) {
    event.stopPropagation();
    document.getElementById('chatDotMenu').classList.toggle('show');
}
document.addEventListener('click', () => {
    document.getElementById('chatDotMenu')?.classList.remove('show');
});

function requestDeleteChat() {
    document.getElementById('chatDotMenu').classList.remove('show');
    if (!activeContactId) return;
    chatIdPendingDeletion = activeContactId;
    openModal('confirmDeleteChatOverlay');
}

async function executeDeleteChatConfirmed() {
    closeModal('confirmDeleteChatOverlay');
    if (!chatIdPendingDeletion) return;
    const idToDelete = chatIdPendingDeletion;
    chatIdPendingDeletion = null;

    destroySession(idToDelete);
    removePendingRequestsFrom(idToDelete);
    await deleteContact(idToDelete);

    if (activeContactId === idToDelete) {
        activeContactId = null;
        clearChatDOM();
        document.getElementById('chatContainer').style.display = 'none';
        document.getElementById('connectPanel').style.display = 'none';
        document.getElementById('welcomeScreen').style.display = 'flex';
    }

    renderContactsList();
    showStatus('success', '🗑️ Чат и контакт удалены');
}

async function executeDeleteMessage() {
    if (!msgIdToDelete) return;
    const gId = msgIdToDelete;
    closeModal('confirmDeleteMsgOverlay');
    await deleteMessageLocally(gId, false);
    const session = getActiveSession();
    if (session?.dataChannel?.readyState === 'open')
        session.dataChannel.send(JSON.stringify({ type:'CHAT_MSG_DELETE', payload: gId }));
    msgIdToDelete = null;
}

async function deleteMessageLocally(gId, fromPeer) {
    const localId = globalToLocalMap.get(gId);
    if (localId) {
        const el = document.getElementById('msg-' + localId);
        if (el) el.remove();
    }
    await deleteMsgFromDB(gId);
    const container = document.getElementById('chatMessages');
    if (container && !container.querySelector('.msg-bubble')) updateChatEmptyState();
}

async function copyDecryptedText(id) {
    const el = document.getElementById('msg-'+id);
    if (el?._decryptedText) { await navigator.clipboard.writeText(el._decryptedText); showStatus('success','Скопировано!'); }
}

function downloadFileFromMsg(id) {
    const el = document.getElementById('msg-'+id);
    if (!el?._downloadFiles?.length) return;
    // Staggered so the browser doesn't treat several near-simultaneous
    // downloads as a popup-blockable burst when a message bundles several files.
    el._downloadFiles.forEach((f, i) => {
        setTimeout(() => {
            const url = URL.createObjectURL(new Blob([f.data], { type: f.type || 'application/octet-stream' }));
            const a = document.createElement('a'); a.href = url; a.download = f.name; a.click();
            URL.revokeObjectURL(url);
        }, i * 300);
    });
}

function showPeerStatus(status) {
    const el = document.getElementById('peerStatusBar');
    if (!el) return;
    clearTimeout(el._autoHide);
    const name = getDisplayName(contacts.get(activeContactId));

    if (status === 'typing')       { el.textContent = name + ' печатает...'; el.classList.add('show'); el._autoHide = setTimeout(() => el.classList.remove('show'), 4000); }
    else if (status === 'sending_file') { el.textContent = name + ' отправляет файл...'; el.classList.add('show'); el._autoHide = setTimeout(() => el.classList.remove('show'), 60000); }
    else if (status === 'recording')   { el.textContent = name + ' записывает голосовое...'; el.classList.add('show'); el._autoHide = setTimeout(() => el.classList.remove('show'), 60000); }
    else if (status === 'reconnecting'){ el.textContent = '🔄 Переподключение...'; el.classList.add('show'); }
    else if (status === 'lost')        { el.textContent = '❌ Соединение потеряно'; el.classList.add('show'); }
    else { el.classList.remove('show'); }
}

function onChatInputTyping() {
    const session = getActiveSession();
    if (!session?.isMlKemReady || session.dataChannel?.readyState !== 'open') return;
    if (!document.getElementById('chatInput').value.trim()) { stopTypingIndicator(); return; }
    if (!isTypingSent) { isTypingSent = true; session.dataChannel.send(JSON.stringify({ type:'PEER_STATUS', status:'typing' })); }
    clearTimeout(typingTimer);
    typingTimer = setTimeout(stopTypingIndicator, 2000);
}

function stopTypingIndicator() {
    clearTimeout(typingTimer);
    const session = getActiveSession();
    if (isTypingSent && session?.dataChannel?.readyState === 'open')
        session.dataChannel.send(JSON.stringify({ type:'PEER_STATUS', status:'idle' }));
    isTypingSent = false;
}

let mediaRecorder = null, audioChunks = [], isVoiceRecording = false;

async function toggleVoiceRecord() {
    const btn = document.getElementById('btnVoiceRecord');
    const session = getActiveSession();
    if (isVoiceRecording) {
        mediaRecorder.stop(); btn.textContent = '🎤';
        btn.classList.remove('recording-active');
        isVoiceRecording = false;
        if (session?.dataChannel?.readyState === 'open') session.dataChannel.send(JSON.stringify({ type:'PEER_STATUS', status:'idle' }));
    } else {
        try {
            const stream = await navigator.mediaDevices.getUserMedia({ audio: true });
            mediaRecorder = new MediaRecorder(stream);
            audioChunks   = [];
            mediaRecorder.ondataavailable = e => { if (e.data.size > 0) audioChunks.push(e.data); };
            mediaRecorder.onstop = () => {
                const blob = new Blob(audioChunks, { type: 'audio/webm' });
                attachFiles([new File([blob], `Voice_${formatTime(new Date()).replace(':','-')}.webm`, { type:'audio/webm' })]);
                stream.getTracks().forEach(t => t.stop());
            };
            mediaRecorder.start();
            isVoiceRecording = true;
            btn.textContent = '⏹️';
            btn.classList.add('recording-active');
            if (session?.dataChannel?.readyState === 'open') session.dataChannel.send(JSON.stringify({ type:'PEER_STATUS', status:'recording' }));
        } catch { showStatus('error','Доступ к микрофону заблокирован'); }
    }
}

async function attachFiles(fileList) {
    const incoming = Array.from(fileList || []);
    if (!incoming.length) return;
    if (chatAttachedFiles.length + incoming.length > MAX_ATTACHMENTS_PER_MESSAGE) {
        showStatus('error', `Максимум ${MAX_ATTACHMENTS_PER_MESSAGE} вложений в одном сообщении`);
    }
    const room  = Math.max(0, MAX_ATTACHMENTS_PER_MESSAGE - chatAttachedFiles.length);
    const toAdd = incoming.slice(0, room);
    for (const file of toAdd) {
        try {
            const data = await readFileAsArrayBuffer(file);
            chatAttachedFiles.push({ file, data });
        } catch { showStatus('error', `Не удалось прочитать файл ${file.name}`); }
    }
    renderAttachedFilesPreview();
}

function removeAttachedFile(index) {
    chatAttachedFiles.splice(index, 1);
    renderAttachedFilesPreview();
}

function clearAttachedFiles() {
    chatAttachedFiles = [];
    renderAttachedFilesPreview();
    document.getElementById('chatFileInput').value = '';
}

function renderAttachedFilesPreview() {
    attachmentPreviewUrls.forEach(u => URL.revokeObjectURL(u));
    attachmentPreviewUrls = [];

    const wrap = document.getElementById('chatFilesPreview');
    if (!chatAttachedFiles.length) { wrap.classList.remove('show'); wrap.innerHTML = ''; return; }

    wrap.classList.add('show');
    wrap.innerHTML = chatAttachedFiles.map((a, i) => {
        let thumb;
        if (a.file.type.startsWith('image/')) {
            const url = URL.createObjectURL(a.file);
            attachmentPreviewUrls.push(url);
            thumb = `<img class="file-chip-thumb" src="${url}">`;
        } else {
            thumb = `<div class="file-chip-thumb">${getFileIconEmoji(a.file.type)}</div>`;
        }
        return `<div class="file-chip">${thumb}<span class="file-chip-name">${escapeHtml(a.file.name)}</span>
            <button class="file-chip-remove" data-action="remove-attachment" data-index="${i}" title="Убрать">✕</button></div>`;
    }).join('');
}

function autoResizeInput() {
    const el = document.getElementById('chatInput');
    el.style.height = 'auto';
    el.style.height = Math.min(el.scrollHeight, 110) + 'px';
}

function playNotificationSound() {
    try {
        const AudioContext = window.AudioContext || window.webkitAudioContext;
        if (!AudioContext) return;
        const ctx = new AudioContext();
        const playTone = (freq, start, dur) => {
            const osc = ctx.createOscillator(), gain = ctx.createGain();
            osc.type = 'sine'; osc.frequency.setValueAtTime(freq, start);
            gain.gain.setValueAtTime(0, start);
            gain.gain.linearRampToValueAtTime(0.14, start + 0.02);
            gain.gain.exponentialRampToValueAtTime(0.001, start + dur);
            osc.connect(gain); gain.connect(ctx.destination);
            osc.start(start); osc.stop(start + dur);
        };
        const t = ctx.currentTime;
        playTone(880, t, 0.15); playTone(1320, t + 0.08, 0.25);
    } catch {}
}

// ═══════════════════════════════════════════════════════════
//  UI — SIDEBAR & ROUTING
// ═══════════════════════════════════════════════════════════
function renderContactsList() {
    const list = document.getElementById('contactsList');
    const empty = document.getElementById('contactsEmpty');
    if (contacts.size === 0) { empty.style.display = ''; list.innerHTML = ''; list.appendChild(empty); return; }
    empty.style.display = 'none';

    const existingIds = new Set([...list.querySelectorAll('.contact-item')].map(el => el.dataset.id));
    const newIds = new Set(contacts.keys());
    for (const id of existingIds) if (!newIds.has(id)) list.querySelector(`[data-id="${id}"]`)?.remove();

    const sorted = [...contacts.values()].sort((a,b) => (b.lastSeenAt||0) - (a.lastSeenAt||0));

    for (const contact of sorted) {
        let item = list.querySelector(`[data-id="${contact.shortId}"]`);
        if (!item) {
            item = document.createElement('div');
            item.className = 'contact-item';
            item.dataset.id = contact.shortId;
            item.onclick = () => openChat(contact.shortId);
            list.appendChild(item);
        }
        item.classList.toggle('active', contact.shortId === activeContactId);

        const color  = avatarColor(contact.shortId);
        const online = sessions.get(contact.shortId)?.isMlKemReady || false;
        const displayName   = getDisplayName(contact);
        const knownNickname = (contact.nickname && contact.nickname !== contact.shortId) ? contact.nickname : null;
        const subtitle = online ? 'В сети' : (contact.lastSeenAt ? formatTime(new Date(contact.lastSeenAt)) : '');

        item.innerHTML = `
            <div class="contact-avatar" style="background:${color}">
                ${avatarLetter(knownNickname)}
                <div class="contact-online-dot ${online ? 'show' : ''}"></div>
            </div>
            <div class="contact-info">
                <div class="contact-name">${escapeHtml(displayName)}</div>
                <div class="contact-last-msg">${escapeHtml(subtitle)}</div>
            </div>`;
    }
}

async function openChat(contactId, connectAutomatically = false) {
    activeContactId = contactId;
    const contact = contacts.get(contactId);
    if (!contact) return;

    isTypingSent = false; clearTimeout(typingTimer);
    const warnEl = document.getElementById('fpTofuWarn');
    if (warnEl) warnEl.style.display = 'none';

    if (window.innerWidth <= 640) hideSidebar();

    document.querySelectorAll('.contact-item').forEach(el => el.classList.toggle('active', el.dataset.id === contactId));

    document.getElementById('welcomeScreen').style.display = 'none';
    document.getElementById('chatContainer').style.display = 'flex';
    document.getElementById('chatContainer').style.flexDirection = 'column';
    document.getElementById('chatContainer').style.flex = '1';

    const color = avatarColor(contactId);
    const knownNickname = (contact.nickname && contact.nickname !== contactId) ? contact.nickname : null;
    document.getElementById('chatPeerAvatar').textContent = avatarLetter(knownNickname);
    document.getElementById('chatPeerAvatar').style.background = color;
    document.getElementById('chatPeerName').textContent = getDisplayName(contact);
    document.getElementById('chatPeerId').textContent   = 'ID: ' + contact.shortId;

    clearChatDOM();

    const history = await loadHistory(contactId);
    for (const m of history) {
        // fileMeta is stored as an array going forward (one entry per bundled
        // attachment); normalize older single-object records from before
        // multi-attachment support so history reload doesn't choke on them.
        const filesArr = m.fileMeta ? (Array.isArray(m.fileMeta) ? m.fileMeta : [m.fileMeta]) : null;
        addMessageBubble({
            side:      m.direction === 'out' ? 'mine' : 'friend',
            globalId:  m.gId,
            text:      m.text || null,
            filesInfo: filesArr ? filesArr.map(f => ({ name: f.name, size: 0, type: '' })) : null
        });
    }
    updateChatEmptyState();

    const session = sessions.get(contactId);
    const connectPanel = document.getElementById('connectPanel');
    if (session?.isMlKemReady) {
        connectPanel.style.display = 'none';
        updateChatHeader();
        resendPendingAcknowledgements(contactId);
    } else {
        connectPanel.style.display = 'block';
        document.getElementById('chatHeaderStatus').textContent = '⚪ Не подключено';
        if (connectAutomatically) initiateConnection();
    }

    document.getElementById('btnFingerprint').disabled = !session?.sessionFingerprint;
    updateCallButtonState();
}

function updateChatHeader() {
    const statusEl = document.getElementById('chatHeaderStatus');
    if (!statusEl) return;
    const session = getActiveSession();
    if (session?.isMlKemReady) {
        statusEl.textContent = '🔒 Зашифровано · P2P';
        document.getElementById('connectPanel').style.display = 'none';
    } else {
        statusEl.textContent = '⚪ Не подключено';
    }
    updateCallButtonState();
}

function clearChatDOM() {
    const container = document.getElementById('chatMessages');
    container.innerHTML = '';
    chatMessageCounter = 0;
    globalToLocalMap.clear();
    replyInfoCache.clear();
    cancelReply();
    clearAttachedFiles();
}

function clearChat() {
    clearChatDOM();
    if (activeContactId) {
        dbClearMessages(activeContactId);
        updateChatEmptyState();
    }
}

function updateChatEmptyState() {
    const container = document.getElementById('chatMessages');
    if (container.querySelector('.msg-bubble')) return;
    const session = getActiveSession();
    const text = session?.isMlKemReady ? 'Напишите первое сообщение' : 'Подключитесь, чтобы начать чат';
    container.innerHTML = `<div class="chat-empty"><div class="chat-empty-icon">💬</div><div class="chat-empty-text">${text}</div></div>`;
}

function hideSidebar()  { document.getElementById('sidebar').classList.add('hidden-mobile'); }
function showSidebar()  { document.getElementById('sidebar').classList.remove('hidden-mobile'); }

// ═══════════════════════════════════════════════════════════
//  THEME
// ═══════════════════════════════════════════════════════════
function setTheme(name) {
    const html = document.documentElement;
    html.removeAttribute('data-theme');
    if (name !== 'cream') html.setAttribute('data-theme', name);
    document.querySelectorAll('.theme-dot-btn').forEach(b => b.classList.toggle('active', b.dataset.theme === name));
    localStorage.setItem('theme', name);
    dbPut('settings', { key:'theme', value:name });
}

function loadTheme() {
    let theme = localStorage.getItem('theme');
    if (!theme) theme = window.matchMedia('(prefers-color-scheme: dark)').matches ? 'midnight' : 'ocean';
    setTheme(theme);
}

// ═══════════════════════════════════════════════════════════
//  ONBOARDING & PROFILE
// ═══════════════════════════════════════════════════════════
async function finishOnboarding() {
    const nickname = document.getElementById('onboardingNickname').value.trim();
    if (nickname) myIdentity.nickname = nickname.slice(0, 30);
    await persistIdentity();
    closeModal('onboardingOverlay');
    renderMyIdentity();
    await initSignalling();
}

function renderMyIdentity() {
    if (!myIdentity) return;
    document.getElementById('myNicknameDisplay').textContent = myIdentity.nickname;
    document.getElementById('myPeerIdDisplay').textContent   = myIdentity.shortId;
    document.getElementById('myAvatarEl').textContent = avatarLetter(myIdentity.nickname);
    document.getElementById('myAvatarEl').style.background = avatarColor(myIdentity.shortId);
}

function openProfileModal() {
    document.getElementById('profileNickname').value = myIdentity.nickname;
    document.getElementById('profileIdDisplay').innerHTML = myIdentity.shortId + `<small>Постоянный — выводится из публичного ключа</small>`;
    openModal('profileOverlay');
}

async function saveProfile() {
    const val = document.getElementById('profileNickname').value.trim();
    if (val) { myIdentity.nickname = val.slice(0,30); await persistIdentity(); renderMyIdentity(); }
    closeModal('profileOverlay');
}

function openAddContactModal() { document.getElementById('addContactId').value = ''; document.getElementById('addContactLog').innerHTML = ''; openModal('addContactOverlay'); }

async function connectToId() {
    const targetId = document.getElementById('addContactId').value.trim().toUpperCase();
    if (targetId.length < 8) { document.getElementById('addContactLog').innerHTML = '<div class="status-pill error">Введите корректный ID</div>'; return; }
    if (targetId === myIdentity.shortId) { document.getElementById('addContactLog').innerHTML = '<div class="status-pill error">Нельзя подключиться к себе</div>'; return; }

    if (!contacts.has(targetId)) {
        await saveContact({ shortId: targetId, ikPub:'', nickname: null, verified:false, addedAt: Date.now(), lastSeenAt: Date.now() });
        renderContactsList();
    }
    closeModal('addContactOverlay');
    await openChat(targetId, true);
}

// ═══════════════════════════════════════════════════════════
//  APP LOCK
// ═══════════════════════════════════════════════════════════
async function toggleAppLock(enabled) {
    const toggle = document.getElementById('appLockToggle');
    if (enabled) {
        const pwd = await askPassword('create');
        if (!pwd) { toggle.checked = false; return; }
        try {
            await enableAppLock(pwd);
            showStatus('success', '🔒 Локальный пароль включён');
        } catch (e) {
            toggle.checked = false;
            showStatus('error', '❌ Не удалось включить пароль: ' + e.message);
        }
    } else {
        const pwd = await askPassword('unlock');
        if (!pwd) { toggle.checked = true; return; }
        try {
            await disableAppLock(pwd);
            showStatus('success', '🔓 Локальный пароль отключён');
        } catch (e) {
            toggle.checked = true;
            showStatus('error', '❌ Не удалось отключить пароль: ' + e.message);
        }
    }
}

async function enableAppLock(pwd) {
    await sodium.ready;

    if (typeof sodium.crypto_pwhash !== 'function' || !sodium.crypto_pwhash_SALTBYTES) {
        throw new Error('Эта сборка libsodium не поддерживает crypto_pwhash (Argon2id)');
    }

    const salt      = sodium.randombytes_buf(sodium.crypto_pwhash_SALTBYTES);
    const opslimit  = sodium.crypto_pwhash_OPSLIMIT_INTERACTIVE;
    const memlimit  = sodium.crypto_pwhash_MEMLIMIT_INTERACTIVE;
    const rawKey    = sodium.crypto_pwhash(32, te.encode(pwd), salt, opslimit, memlimit, sodium.crypto_pwhash_ALG_ARGON2ID13);
    const nonce     = sodium.randombytes_buf(sodium.crypto_aead_xchacha20poly1305_ietf_NPUBBYTES);
    const encSec    = sodium.crypto_aead_xchacha20poly1305_ietf_encrypt(myIdentity.ikSec, null, null, nonce, rawKey);
    const encBlob   = new Uint8Array(nonce.length + encSec.length);
    encBlob.set(nonce, 0);
    encBlob.set(encSec, nonce.length);

    const stored = await dbGet('identity', 'self');
    const prevIkSecB64 = stored.ikSec;
    const prevAppLock  = stored.appLockEnabled;

    stored.ikSec          = arrayBufferToBase64(encBlob.buffer);
    stored.appLockEnabled = true;

    try {
        await dbPut('settings', { key:'vaultMeta', salt: arrayBufferToBase64(salt.buffer), opslimit, memlimit });
        await dbPut('identity', stored);
    } catch (e) {
        stored.ikSec = prevIkSecB64;
        stored.appLockEnabled = prevAppLock;
        await dbPut('identity', stored).catch(() => {});
        await dbDelete('settings', 'vaultMeta').catch(() => {});
        throw e;
    }

    myIdentity.appLockEnabled = true;
    appLockKey = rawKey;
}

async function disableAppLock(pwd) {
    await sodium.ready;
    const vaultMeta = await dbGet('settings', 'vaultMeta');
    if (!vaultMeta) {
        myIdentity.appLockEnabled = false;
        await persistIdentity();
        return;
    }

    const stored = await dbGet('identity', 'self');
    const salt   = new Uint8Array(base64ToArrayBuffer(vaultMeta.salt));
    const rawKey = sodium.crypto_pwhash(32, te.encode(pwd), salt, vaultMeta.opslimit, vaultMeta.memlimit, sodium.crypto_pwhash_ALG_ARGON2ID13);

    const encBuf    = new Uint8Array(base64ToArrayBuffer(stored.ikSec));
    const NONCE_LEN = sodium.crypto_aead_xchacha20poly1305_ietf_NPUBBYTES;
    const nonce     = encBuf.slice(0, NONCE_LEN);
    const ct        = encBuf.slice(NONCE_LEN);

    let plain;
    try {
        plain = sodium.crypto_aead_xchacha20poly1305_ietf_decrypt(null, ct, null, nonce, rawKey);
    } catch {
        throw new Error('Неверный пароль');
    }

    myIdentity.ikSec          = new Uint8Array(plain);
    myIdentity.appLockEnabled = false;
    await persistIdentity();
    await dbDelete('settings', 'vaultMeta');
    appLockKey = null;
}

function askPassword(mode) {
    return new Promise(resolve => {
        openPasswordModal(mode, resolve, mode === 'create');
        passwordModalResolve = resolve;
    });
}

function openPasswordModal(mode, callback, showConfirm = false) {
    const titles = { create:'Создайте пароль', unlock:'Введите пароль', backup_export:'Пароль для бэкапа', backup_import:'Пароль от бэкапа' };
    document.getElementById('passwordModalIcon').textContent  = mode === 'create' ? '🔒' : '🔑';
    document.getElementById('passwordModalTitle').textContent = titles[mode] || 'Введите пароль';
    document.getElementById('passwordModalSub').textContent   = mode === 'create' ? 'Используется для шифрования ваших ключей' : 'Для расшифровки данных';
    document.getElementById('passwordInput').value    = '';
    document.getElementById('passwordConfirm').value  = '';
    document.getElementById('passwordError').style.display = 'none';
    document.getElementById('passwordConfirm').style.display = showConfirm ? '' : 'none';
    passwordModalResolve = callback;
    openModal('passwordOverlay');
}

function confirmPasswordModal() {
    const pwd = document.getElementById('passwordInput').value;
    const confirm = document.getElementById('passwordConfirm');
    if (confirm.style.display !== 'none' && pwd !== confirm.value) {
        document.getElementById('passwordError').textContent = 'Пароли не совпадают';
        document.getElementById('passwordError').style.display = 'block';
        return;
    }
    if (!pwd) { document.getElementById('passwordError').textContent = 'Введите пароль'; document.getElementById('passwordError').style.display = 'block'; return; }
    closeModal('passwordOverlay');
    if (passwordModalResolve) { passwordModalResolve(pwd); passwordModalResolve = null; }
}

function cancelPasswordModal() {
    closeModal('passwordOverlay');
    if (passwordModalResolve) { passwordModalResolve(null); passwordModalResolve = null; }
}

// ═══════════════════════════════════════════════════════════
//  BACKUP EXPORT / IMPORT
// ═══════════════════════════════════════════════════════════
async function exportBackup() {
    const pwd = await askPassword('backup_export');
    if (!pwd) return;

    try {
        await sodium.ready;
        const allMsgs = await dbGetAll('messages');
        const blob = {
            v:        2,
            identity: {
                shortId:  myIdentity.shortId,
                ikPub:    arrayBufferToBase64(myIdentity.ikPub.buffer),
                ikSec:    arrayBufferToBase64(myIdentity.ikSec.buffer),
                nickname: myIdentity.nickname
            },
            contacts: [...contacts.values()],
            messages: allMsgs.map(m => ({ gId:m.gId, contactId:m.contactId, direction:m.direction, text:m.text, fileMeta:m.fileMeta, ts:m.ts, status:m.status, replyToGId:m.replyToGId }))
        };

        const salt     = sodium.randombytes_buf(sodium.crypto_pwhash_SALTBYTES);
        const opslimit = sodium.crypto_pwhash_OPSLIMIT_INTERACTIVE;
        const memlimit = sodium.crypto_pwhash_MEMLIMIT_INTERACTIVE;
        const rawKey   = sodium.crypto_pwhash(32, te.encode(pwd), salt, opslimit, memlimit, sodium.crypto_pwhash_ALG_ARGON2ID13);
        const nonce    = sodium.randombytes_buf(sodium.crypto_aead_xchacha20poly1305_ietf_NPUBBYTES);
        const plain    = te.encode(JSON.stringify(blob));
        const ct       = sodium.crypto_aead_xchacha20poly1305_ietf_encrypt(plain, null, null, nonce, rawKey);

        const out = JSON.stringify({
            v: 2,
            salt: arrayBufferToBase64(salt.buffer),
            opslimit, memlimit,
            nonce: arrayBufferToBase64(nonce.buffer),
            ct: arrayBufferToBase64(ct.buffer)
        });

        const url = URL.createObjectURL(new Blob([out], { type:'application/json' }));
        const a   = document.createElement('a');
        a.href    = url;
        a.download = `scryptor-backup-${myIdentity.shortId}-${new Date().toISOString().slice(0,10)}.json`;
        a.click();
        URL.revokeObjectURL(url);
        showStatus('success','📤 Бэкап скачан');
    } catch (e) {
        showStatus('error','❌ Не удалось создать бэкап: ' + e.message);
    }
}

async function importBackup(inputEl) {
    const file = inputEl.files[0]; if (!file) return;
    const pwd = await askPassword('backup_import');
    if (!pwd) return;

    try {
        const raw  = JSON.parse(await file.text());
        await sodium.ready;
        const salt     = new Uint8Array(base64ToArrayBuffer(raw.salt));
        const rawKey   = sodium.crypto_pwhash(32, te.encode(pwd), salt, raw.opslimit, raw.memlimit, sodium.crypto_pwhash_ALG_ARGON2ID13);
        const nonce    = new Uint8Array(base64ToArrayBuffer(raw.nonce));
        const ct       = new Uint8Array(base64ToArrayBuffer(raw.ct));
        const plainBuf = sodium.crypto_aead_xchacha20poly1305_ietf_decrypt(null, ct, null, nonce, rawKey);
        const blob     = JSON.parse(td.decode(plainBuf));

        await dbPut('identity', { id:'self', ...blob.identity, appLockEnabled: false });
        for (const c of blob.contacts) await dbPut('contacts', c);
        for (const m of blob.messages) await dbPut('messages', m);

        showStatus('success','📥 Бэкап восстановлен. Перезагрузите страницу.');
        setTimeout(() => location.reload(), 2000);
    } catch {
        showStatus('error','❌ Неверный пароль или повреждённый файл');
    }
    inputEl.value = '';
}

// ═══════════════════════════════════════════════════════════
//  DESTROY ALL DATA
// ═══════════════════════════════════════════════════════════
function destroyAllData() { openModal('confirmDestroyOverlay'); }

async function executeDestroyAllData() {
    closeModal('confirmDestroyOverlay');

    for (const peerId of [...sessions.keys()]) destroySession(peerId);
    if (mqttClient) { try { mqttClient.end(true); } catch {} mqttClient = null; }

    if (myIdentity?.ikSec) secureZero(myIdentity.ikSec);

    await dbClearAll();

    mediaObjectUrls.forEach(u => URL.revokeObjectURL(u));
    mediaObjectUrls = [];

    myIdentity = null;
    contacts.clear(); activeContactId = null;
    sessions.clear();

    showStatus('success','🔥 Все данные уничтожены из RAM и IndexedDB');
    setTimeout(() => location.reload(), 1500);
}

function openSettingsModal() {
    document.getElementById('appLockToggle').checked = myIdentity?.appLockEnabled || false;
    const storedTheme = localStorage.getItem('theme') || 'ocean';
    document.querySelectorAll('.theme-dot-btn').forEach(b => b.classList.toggle('active', b.dataset.theme === storedTheme));
    openModal('settingsOverlay');
}

document.addEventListener('visibilitychange', () => {
    if (document.visibilityState !== 'visible') return;
    for (const [peerId, session] of sessions) {
        if (session.isMlKemReady && session.dataChannel?.readyState === 'open') {
            if (!session.heartbeatInterval) startHeartbeat(session, peerId);
        } else if (session.isMlKemReady && !session.isReconnecting) {
            handleConnectionLost(peerId);
        }
    }
    if (!mqttClient?.connected && myIdentity) initSignalling();
});

// ═══════════════════════════════════════════════════════════
//  EVENT WIRING (replaces the old inline onclick="" attributes
//  now that CSP script-src no longer allows 'unsafe-inline')
// ═══════════════════════════════════════════════════════════
function wireChatMessagesDelegation() {
    const container = document.getElementById('chatMessages');

    // Click delegation for reply-preview / image / copy / reply / delete / download buttons
    container.addEventListener('click', e => {
        const target = e.target.closest('[data-action]');
        if (!target) return;
        const action = target.dataset.action;
        if (action === 'scroll-to')      scrollToMessage(target.dataset.target);
        else if (action === 'view-image') window.open(target.src, '_blank');
        else if (action === 'copy')       copyDecryptedText(target.dataset.msgId);
        else if (action === 'reply')      setReplyTo(target.dataset.target);
        else if (action === 'delete-msg') requestDeleteMessage(target.dataset.target);
        else if (action === 'download')   downloadFileFromMsg(target.dataset.msgId);
        else if (action === 'retry')      retryMessage(target.dataset.target);
    });

    // Change delegation for the per-voice-message playback-speed <select>
    container.addEventListener('change', e => {
        if (e.target.dataset.action === 'set-speed') {
            const audio = e.target.previousElementSibling;
            if (audio) audio.playbackRate = parseFloat(e.target.value);
        }
    });
}

function wireStaticButtons() {
    document.getElementById('btnAddContactBtn').addEventListener('click', openAddContactModal);
    document.getElementById('btnSettingsBtn').addEventListener('click', openSettingsModal);
    document.getElementById('btnProfileBtn').addEventListener('click', openProfileModal);
    document.getElementById('btnDestroyAll').addEventListener('click', destroyAllData);

    document.getElementById('chatBackBtn').addEventListener('click', showSidebar);
    document.getElementById('btnFingerprint').addEventListener('click', showFingerprintModal);
    document.getElementById('btnClearChat').addEventListener('click', clearChat);

    document.getElementById('btnStartCall').addEventListener('click', () => { if (activeContactId) startCall(activeContactId); });
    document.getElementById('btnAcceptCall').addEventListener('click', acceptIncomingCall);
    document.getElementById('btnRejectCall').addEventListener('click', rejectIncomingCall);
    document.getElementById('btnCancelOutgoingCall').addEventListener('click', cancelOutgoingCall);
    document.getElementById('btnToggleMute').addEventListener('click', toggleCallMute);
    document.getElementById('btnHangupCall').addEventListener('click', hangupActiveCall);
    document.getElementById('callVolumeSlider').addEventListener('input', e => setCallVolume(e.target.value));
    document.getElementById('btnChatMenu').addEventListener('click', toggleChatMenu);
    document.getElementById('btnRequestDeleteChat').addEventListener('click', requestDeleteChat);

    document.getElementById('btnCancelReply').addEventListener('click', cancelReply);
    document.getElementById('chatFilesPreview').addEventListener('click', e => {
        const btn = e.target.closest('[data-action="remove-attachment"]');
        if (btn) removeAttachedFile(parseInt(btn.dataset.index, 10));
    });
    document.getElementById('btnAttachFile').addEventListener('click', () => document.getElementById('chatFileInput').click());
    document.getElementById('btnVoiceRecord').addEventListener('click', toggleVoiceRecord);
    document.getElementById('btnSend').addEventListener('click', chatEncrypt);

    document.getElementById('btnConnect').addEventListener('click', initiateConnection);
    document.getElementById('btnFinishOnboarding').addEventListener('click', finishOnboarding);

    document.getElementById('btnCancelProfile').addEventListener('click', () => closeModal('profileOverlay'));
    document.getElementById('btnSaveProfile').addEventListener('click', saveProfile);

    document.getElementById('btnCancelAddContact').addEventListener('click', () => closeModal('addContactOverlay'));
    document.getElementById('btnAddContact').addEventListener('click', connectToId);

    document.getElementById('btnRejectRequest').addEventListener('click', rejectConnectionRequest);
    document.getElementById('btnAcceptRequest').addEventListener('click', acceptConnectionRequest);

    document.getElementById('btnCloseFpModal').addEventListener('click', () => closeModal('fpModalOverlay'));
    // Restore backdrop-click-to-close (only the fingerprint modal had this in the original)
    document.getElementById('fpModalOverlay').addEventListener('click', e => {
        if (e.target === e.currentTarget) closeModal('fpModalOverlay');
    });

    document.getElementById('themeButtons').addEventListener('click', e => {
        const btn = e.target.closest('.theme-dot-btn');
        if (btn?.dataset.theme) setTheme(btn.dataset.theme);
    });

    document.getElementById('appLockToggle').addEventListener('change', e => toggleAppLock(e.target.checked));

    document.getElementById('btnExportBackup').addEventListener('click', exportBackup);
    document.getElementById('btnImportBackup').addEventListener('click', () => document.getElementById('importFileInput').click());
    document.getElementById('importFileInput').addEventListener('change', function () { importBackup(this); });

    document.getElementById('btnCloseSettings').addEventListener('click', () => closeModal('settingsOverlay'));

    document.getElementById('btnPasswordCancel').addEventListener('click', cancelPasswordModal);
    document.getElementById('btnPasswordOk').addEventListener('click', confirmPasswordModal);

    document.getElementById('btnCancelDeleteMsg').addEventListener('click', () => closeModal('confirmDeleteMsgOverlay'));
    document.getElementById('btnConfirmDeleteMsg').addEventListener('click', executeDeleteMessage);

    document.getElementById('btnCancelDeleteChat').addEventListener('click', () => closeModal('confirmDeleteChatOverlay'));
    document.getElementById('btnConfirmDeleteChat').addEventListener('click', executeDeleteChatConfirmed);

    document.getElementById('btnCancelDestroy').addEventListener('click', () => closeModal('confirmDestroyOverlay'));
    document.getElementById('btnConfirmDestroy').addEventListener('click', executeDestroyAllData);

    wireChatMessagesDelegation();
}

document.addEventListener('DOMContentLoaded', async () => {
    // Wire up all buttons first, regardless of sodium/init outcome below,
    // so the UI (modals, theme switcher, etc.) never ends up totally dead.
    wireStaticButtons();

    document.getElementById('chatFileInput').addEventListener('change', e => { if (e.target.files.length) attachFiles(e.target.files); });

    const ci = document.getElementById('chatInput');
    ci.addEventListener('input', () => { autoResizeInput(); onChatInputTyping(); });
    ci.addEventListener('keydown', e => {
        if (e.key === 'Enter' && !e.shiftKey && window.innerWidth > 640) { e.preventDefault(); chatEncrypt(); }
    });
    ci.addEventListener('paste', async e => {
        if (!e.clipboardData?.items) return;
        const files = [];
        for (const item of e.clipboardData.items) {
            if (item.kind === 'file') { const f = item.getAsFile(); if (f) files.push(f); }
        }
        if (files.length) { e.preventDefault(); attachFiles(files); }
    });

    const msgArea = document.getElementById('chatMessages');
    msgArea.addEventListener('dragover', e => { e.preventDefault(); e.dataTransfer.dropEffect = 'copy'; });
    msgArea.addEventListener('drop',     e => { e.preventDefault(); if (e.dataTransfer.files.length) attachFiles(e.dataTransfer.files); });

    window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', e => {
        if (!localStorage.getItem('theme')) setTheme(e.matches ? 'midnight' : 'ocean');
    });

    try {
        if (typeof sodium === 'undefined') { alert('libsodium.js не загружена'); return; }
        await sodium.ready;
    } catch(e) { console.error("sodium init failed:", e); return; }

    db = await openDB();
    loadTheme();
    const isFirstLaunch = await loadOrCreateIdentity();

    if (isFirstLaunch) {
        document.getElementById('onboardingNickname').value = myIdentity.nickname;
        document.getElementById('onboardingIdDisplay').innerHTML =
            myIdentity.shortId + `<small>Выводится из вашего публичного ключа</small>`;
        document.getElementById('btnFinishOnboarding').disabled = false;
        document.getElementById('onboardingSpinner').style.display = 'none';
        document.getElementById('btnFinishOnboarding').innerHTML = '✅ Создать аккаунт';
    } else {
        closeModal('onboardingOverlay');
        await loadContacts();
        renderContactsList();
        renderMyIdentity();
        await initSignalling();
    }
});

window.addEventListener('beforeunload', () => mediaObjectUrls.forEach(u => URL.revokeObjectURL(u)));