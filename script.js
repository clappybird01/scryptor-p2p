'use strict';
// ═══════════════════════════════════════════════════════════
//  GLOBALS & CONSTANTS
// ═══════════════════════════════════════════════════════════
const te = new TextEncoder();
const td = new TextDecoder();

const AAD_MESSAGE = te.encode("ScryptorP2P-MSG-v2");
const AAD_FILE    = te.encode("ScryptorP2P-FILE-v2");
const DB_NAME     = 'ScryptorDB';
const DB_VERSION  = 1;
const SIGNALING_TOPIC = "scryptor-p2p-v2/signal/";
const CHUNK_SIZE  = 12000;
const MAX_MESSAGE_AGE_MS    = 5 * 60 * 1000;
const MAX_FUTURE_TOLERANCE_MS = 60 * 1000;
const ACK_TIMEOUT_MS = 30000;
const MAX_RECONNECT_ATTEMPTS = 60;

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
        { urls: 'stun:stun1.l.google.com:19302' },
        { urls: 'stun:stun.cloudflare.com:3478' },
        { urls: 'stun:openrelay.metered.ca:80' },
        { urls: 'turn:openrelay.metered.ca:80',  username: 'openrelayproject', credential: 'openrelayproject' },
        { urls: 'turn:openrelay.metered.ca:443', username: 'openrelayproject', credential: 'openrelayproject' },
        { urls: 'turns:openrelay.metered.ca:443?transport=tcp', username: 'openrelayproject', credential: 'openrelayproject' }
    ],
    iceCandidatePoolSize: 10
};

// ── App state ──
let db = null;                        // IndexedDB handle
let myIdentity = null;                // { shortId, ikPub, ikSec, nickname, appLockEnabled }
let appLockKey  = null;               // CryptoKey if lock enabled & unlocked

let contacts = new Map();             // shortId → { shortId, ikPub, nickname, verified, addedAt, lastSeenAt }
let activeContactId = null;           // shortId of open chat

// ── Session state (per connection) ──
let mqttClient    = null;
let peerConnection = null;
let dataChannel   = null;
let connectionTimeout = null;
let currentPeerShortId = null;       // who we're connected/connecting to
let pendingOfferData   = null;       // { offer, senderId, nickname, ikPub }
const iceCandidateBuffer = new Map();// senderId → [candidate,…]

// ── Crypto session ──
let currentSymmetricKey = null;
let isMlKemReady = false;
let isInitiatorRole = null;
let sessionFingerprint = null;

// Ephemeral keys for current handshake
let myEphKxKeyPair   = null;         // X25519 ephemeral
let myEphMlKemPair   = null;         // ML-KEM768 ephemeral
let tempFriendEphX25519 = null;      // peer's ephemeral X25519 pub

// ── UI/chat state ──
let chatMessageCounter = 0;
let chatAttachedFile   = null;
let replyToGlobalId    = null;
const globalToLocalMap = new Map();
const replyInfoCache   = new Map();
let mediaObjectUrls    = [];
const messageStatusMap = new Map();
const ackedMessages    = new Set();
const chunkBuffer      = new Map();

let isTypingSent  = false;
let typingTimer   = null;
let heartbeatInterval = null;
let heartbeatTimeout  = null;
let isReconnecting    = false;
let reconnectAttempts = 0;
let reconnectTimer    = null;
let connectionLostNotified = false;

// Password modal callback
let passwordModalResolve = null;

// Message to delete
let msgIdToDelete = null;

const themeNames = { cream:'Кремовая', dark:'Тёмная', rose:'Розовая', ocean:'Океан', forest:'Лесная', midnight:'Полночь' };

// ═══════════════════════════════════════════════════════════
//  UTILITIES
// ═══════════════════════════════════════════════════════════
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
    if (a.length>=12&&a[0]===0x52&&a[1]===0x49&&a[2]===0x46&&a[3]===0x46&&a[8]===0x57&&a[9]===0x45&&a[10]===0x42&&a[11]===0x50) return 'image/webp';
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
    // deterministic hue from ID
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
            // identity: single record { id:'self', ... }
            if (!db.objectStoreNames.contains('identity'))
                db.createObjectStore('identity', { keyPath: 'id' });
            // contacts: keyed by shortId
            if (!db.objectStoreNames.contains('contacts'))
                db.createObjectStore('contacts', { keyPath: 'shortId' });
            // messages: auto-increment, index by contactId
            if (!db.objectStoreNames.contains('messages')) {
                const ms = db.createObjectStore('messages', { keyPath: 'id', autoIncrement: true });
                ms.createIndex('byContact', 'contactId', { unique: false });
                ms.createIndex('byGId', 'gId', { unique: false });
            }
            // settings
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
//  IDENTITY — first launch or load
// ═══════════════════════════════════════════════════════════
async function loadOrCreateIdentity() {
    const stored = await dbGet('identity', 'self');
    if (stored) {
        // Already have identity — decrypt if appLock enabled
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
        return false; // not first launch
    }
    // Generate new identity keys
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
    return true; // first launch
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

// ── App lock (unlock flow) ──
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
                // Verify by trying to decrypt ikSec
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

// TOFU
async function tofuContact(shortId, ikPubB64, nickname) {
    const existing = contacts.get(shortId);
    const isPlaceholderNickname = !nickname;

    if (existing) {
        if (existing.ikPub && existing.ikPub !== ikPubB64) {
            // Ключ изменился — НЕ обновляем ikPub, НЕ обновляем никнейм,
            // возвращаем 'mismatch' и даём вызывающему коду решить, что делать.
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
//  MESSAGES — IndexedDB persistence
// ═══════════════════════════════════════════════════════════
async function persistMessage(contactId, msg) {
    // msg: { gId, direction:'in'|'out', text, fileMeta, ts, status, replyToGId }
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
const Ratchet = {
    state: { RK:null, CKs:null, CKr:null, DHs:null, DHr:null, Ns:0, Nr:0, PN:0, skipped:{} },
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

    init(sharedSecret, isAlice, friendEphX25519Pub, myEphX25519KeyPair) {
        this.state = { RK: sharedSecret, CKs:null, CKr:null, DHs:null, DHr:null, Ns:0, Nr:0, PN:0, skipped:{} };
        if (isAlice) {
            this.state.DHs = sodium.crypto_kx_keypair();
            this.state.DHr = friendEphX25519Pub;
            const dh_out = sodium.crypto_scalarmult(this.state.DHs.privateKey, this.state.DHr);
            const kdf    = this.KDF_RK(this.state.RK, dh_out);
            secureZero(this.state.RK); secureZero(dh_out);
            this.state.RK  = kdf.RK;
            this.state.CKs = kdf.CK;
        } else {
            this.state.DHs = myEphX25519KeyPair;
        }
    },

    ratchetEncrypt() {
        if (!this.state.CKs) throw new Error("Дождитесь первого сообщения от собеседника.");
        const kdf    = this.KDF_CK(this.state.CKs);
        secureZero(this.state.CKs);
        this.state.CKs = kdf.CK;
        const header   = { dh: arrayBufferToBase64(this.state.DHs.publicKey), n: this.state.Ns, pn: this.state.PN };
        this.state.Ns++;
        return { mk: kdf.MK, header };
    },

    ratchetDecryptTentative(header) {
        const skipKey = header.dh + '_' + header.n;
        if (this.state.skipped[skipKey])
            return { mk: this.state.skipped[skipKey], tentativeState: null, skipKeyToRemove: skipKey };

        let ts = {
            RK:  new Uint8Array(this.state.RK),
            CKs: this.state.CKs ? new Uint8Array(this.state.CKs) : null,
            CKr: this.state.CKr ? new Uint8Array(this.state.CKr) : null,
            DHs: { publicKey: new Uint8Array(this.state.DHs.publicKey), privateKey: new Uint8Array(this.state.DHs.privateKey) },
            DHr: this.state.DHr ? new Uint8Array(this.state.DHr) : null,
            Ns: this.state.Ns, Nr: this.state.Nr, PN: this.state.PN,
            skipped: { ...this.state.skipped }
        };

        const dh_pub = new Uint8Array(base64ToArrayBuffer(header.dh));
        if (!ts.DHr || arrayBufferToBase64(ts.DHr) !== header.dh) {
            this._skipMessageKeys(ts, header.pn);
            this._DHRatchetStep(ts, dh_pub);
        }
        this._skipMessageKeys(ts, header.n);
        const kdf = this.KDF_CK(ts.CKr);
        secureZero(ts.CKr); ts.CKr = kdf.CK; ts.Nr++;
        return { mk: kdf.MK, tentativeState: ts, skipKeyToRemove: null };
    },

    commitState(ts, skipKeyToRemove) {
        if (skipKeyToRemove) { secureZero(this.state.skipped[skipKeyToRemove]); delete this.state.skipped[skipKeyToRemove]; }
        if (ts) this.state = ts;
    },

    _DHRatchetStep(state, dh_pub) {
        state.PN = state.Ns; state.Ns = 0; state.Nr = 0; state.DHr = dh_pub;
        let dh_out = sodium.crypto_scalarmult(state.DHs.privateKey, state.DHr);
        let kdf    = this.KDF_RK(state.RK, dh_out);
        secureZero(dh_out); secureZero(state.RK);
        state.RK = kdf.RK; state.CKr = kdf.CK;
        state.DHs  = sodium.crypto_kx_keypair();
        dh_out = sodium.crypto_scalarmult(state.DHs.privateKey, state.DHr);
        kdf    = this.KDF_RK(state.RK, dh_out);
        secureZero(dh_out); secureZero(state.RK);
        state.RK = kdf.RK; state.CKs = kdf.CK;
    },

    _skipMessageKeys(state, until_n) {
        if (state.Nr + this.MAX_SKIP < until_n) throw new Error("Превышен лимит пропуска.");
        if (state.CKr != null) {
            while (state.Nr < until_n) {
                const kdf = this.KDF_CK(state.CKr);
                secureZero(state.CKr); state.CKr = kdf.CK;
                state.skipped[arrayBufferToBase64(state.DHr) + '_' + state.Nr] = kdf.MK;
                state.Nr++;
            }
        }
    }
};

// ═══════════════════════════════════════════════════════════
//  CRYPTO — ENCRYPT / DECRYPT PAYLOAD
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

// ── Payload packing ──
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

// ── Envelope ──
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
    if (!sessionFingerprint) return;
    document.getElementById('fpCodeDisplay').textContent   = sessionFingerprint.code;
    document.getElementById('fpEmojisDisplay').textContent = sessionFingerprint.emojis;
    openModal('fpModalOverlay');
}

// ═══════════════════════════════════════════════════════════
//  UI INITIALIZATION & EVENT LISTENERS (Stubs to make it run)
// ═══════════════════════════════════════════════════════════
document.addEventListener('DOMContentLoaded', async () => {
    // Bind buttons that were previously using inline onclick handlers
    const bindClick = (id, handler) => {
        const el = document.getElementById(id);
        if (el) el.addEventListener('click', handler);
    };

    bindClick('btnAddContactBtn', openAddContactModal);
    bindClick('btnSettingsBtn', openSettingsModal);
    bindClick('btnProfileBtn', openProfileModal);
    bindClick('btnDestroyAll', () => openModal('confirmDestroyOverlay'));
    bindClick('chatBackBtn', showSidebar);
    bindClick('btnFingerprint', showFingerprintModal);
    bindClick('btnClearChat', clearChat);
    bindClick('btnChatMenu', toggleChatMenu);
    bindClick('btnRequestDeleteChat', requestDeleteChat);
    bindClick('btnCancelReply', cancelReply);
    bindClick('btnClearAttachedFile', clearAttachedFile);
    bindClick('btnAttachFile', () => document.getElementById('chatFileInput').click());
    bindClick('btnVoiceRecord', toggleVoiceRecord);
    bindClick('btnSend', chatEncrypt);
    bindClick('btnConnect', initiateConnection);
    bindClick('btnFinishOnboarding', finishOnboarding);
    bindClick('btnCancelProfile', () => closeModal('profileOverlay'));
    bindClick('btnSaveProfile', saveProfile);
    bindClick('btnCancelAddContact', () => closeModal('addContactOverlay'));
    bindClick('btnAddContact', connectToId);
    bindClick('btnRejectRequest', rejectConnectionRequest);
    bindClick('btnAcceptRequest', acceptConnectionRequest);
    bindClick('btnCloseFpModal', () => closeModal('fpModalOverlay'));
    
    // Settings toggles and buttons
    const themeBtns = document.querySelectorAll('.theme-dot-btn');
    themeBtns.forEach(btn => {
        btn.addEventListener('click', () => setTheme(btn.dataset.theme));
    });
    
    const appLockToggle = document.getElementById('appLockToggle');
    if (appLockToggle) {
        appLockToggle.addEventListener('change', (e) => toggleAppLock(e.target.checked));
    }

    bindClick('btnExportBackup', exportBackup);
    bindClick('btnImportBackup', () => document.getElementById('importFileInput').click());
    
    const importInput = document.getElementById('importFileInput');
    if (importInput) {
        importInput.addEventListener('change', (e) => importBackup(e.target));
    }

    bindClick('btnCloseSettings', () => closeModal('settingsOverlay'));
    bindClick('btnPasswordCancel', cancelPasswordModal);
    bindClick('btnPasswordOk', confirmPasswordModal);
    bindClick('btnCancelDeleteMsg', () => closeModal('confirmDeleteMsgOverlay'));
    bindClick('btnConfirmDeleteMsg', executeDeleteMessage);
    bindClick('btnCancelDeleteChat', () => closeModal('confirmDeleteChatOverlay'));
    bindClick('btnConfirmDeleteChat', executeDeleteChatConfirmed);
    bindClick('btnCancelDestroy', () => closeModal('confirmDestroyOverlay'));
    bindClick('btnConfirmDestroy', executeDestroyAllData);


    // Initialize DB and Load Identity
    try {
        db = await openDB();
        const isFirstLaunch = await loadOrCreateIdentity();
        
        // Setup initial UI state based on identity
        if (isFirstLaunch) {
            // Keep onboarding overlay open (it is open by default in HTML)
            setupOnboarding();
        } else {
            closeModal('onboardingOverlay');
            await finishInitialization();
        }
        
    } catch (e) {
        console.error("Initialization error:", e);
        showStatus('error', "Ошибка инициализации: " + e.message);
    }
});

// ═══════════════════════════════════════════════════════════
//  PLACEHOLDER FUNCTIONS FOR LOGIC (to make UI responsive)
// ═══════════════════════════════════════════════════════════
function openAddContactModal() { openModal('addContactOverlay'); }
function openSettingsModal() { openModal('settingsOverlay'); }
function openProfileModal() { openModal('profileOverlay'); }
function showSidebar() { 
    document.getElementById('sidebar').classList.remove('hidden-mobile');
}
function hideSidebarOnMobile() {
    if (window.innerWidth <= 640) {
        document.getElementById('sidebar').classList.add('hidden-mobile');
    }
}
function clearChat() { alert('Clear Chat functionality would go here.'); }
function toggleChatMenu(event) {
    const menu = document.getElementById('chatDotMenu');
    menu.classList.toggle('show');
    event.stopPropagation();
}
document.addEventListener('click', (e) => {
    const menu = document.getElementById('chatDotMenu');
    if (menu && menu.classList.contains('show') && e.target.id !== 'btnChatMenu') {
        menu.classList.remove('show');
    }
});
function requestDeleteChat() { openModal('confirmDeleteChatOverlay'); }
function cancelReply() { document.getElementById('chatReplyBar').classList.remove('show'); }
function clearAttachedFile() {
    chatAttachedFile = null;
    document.getElementById('chatFileInput').value = '';
    document.getElementById('chatFilePreview').classList.remove('show');
}
function toggleVoiceRecord() { alert('Voice recording toggled.'); }
function chatEncrypt() { alert('Message encryption and sending logic here.'); }
function initiateConnection() { alert('Connection logic here.'); }
function connectToId() { alert('Connecting to ID...'); }
function rejectConnectionRequest() { closeModal('reqModalOverlay'); }
function acceptConnectionRequest() { alert('Accepting connection...'); closeModal('reqModalOverlay'); }
function setTheme(theme) {
    document.documentElement.setAttribute('data-theme', theme);
    document.querySelectorAll('.theme-dot-btn').forEach(b => b.classList.remove('active'));
    document.querySelector(`.theme-dot-btn.t-${theme}`).classList.add('active');
}
function toggleAppLock(checked) { alert(`App lock toggled: ${checked}`); }
function exportBackup() { alert('Backup export logic...'); }
function importBackup(input) { alert('Backup import logic...'); }
function openPasswordModal(mode, resolveCallback, showConfirm) {
    passwordModalResolve = resolveCallback;
    document.getElementById('passwordModalTitle').textContent = mode === 'unlock' ? 'Разблокировка' : 'Установка пароля';
    document.getElementById('passwordConfirm').style.display = showConfirm ? 'block' : 'none';
    document.getElementById('passwordInput').value = '';
    document.getElementById('passwordConfirm').value = '';
    document.getElementById('passwordError').style.display = 'none';
    openModal('passwordOverlay');
}
function cancelPasswordModal() {
    closeModal('passwordOverlay');
    if (passwordModalResolve) passwordModalResolve(null);
}
function confirmPasswordModal() {
    const pwd = document.getElementById('passwordInput').value;
    if (passwordModalResolve) passwordModalResolve(pwd);
}
function executeDeleteMessage() { alert('Message deleted.'); closeModal('confirmDeleteMsgOverlay'); }
function executeDeleteChatConfirmed() { alert('Chat deleted.'); closeModal('confirmDeleteChatOverlay'); }
function executeDestroyAllData() { alert('All data destroyed.'); closeModal('confirmDestroyOverlay'); }

async function setupOnboarding() {
    const btn = document.getElementById('btnFinishOnboarding');
    const spinner = document.getElementById('onboardingSpinner');
    btn.disabled = false;
    spinner.style.display = 'none';
    
    // Simulate generation of ID display
    document.getElementById('onboardingIdDisplay').innerHTML = `
        ${myIdentity.shortId}
        <small>Выводится из вашего публичного ключа — уникален и постоянен</small>
    `;
    document.getElementById('onboardingNickname').value = myIdentity.nickname;
}

async function finishOnboarding() {
    const nick = document.getElementById('onboardingNickname').value.trim();
    if (nick) myIdentity.nickname = nick;
    await persistIdentity();
    closeModal('onboardingOverlay');
    await finishInitialization();
}

async function finishInitialization() {
    updateMyIdentityUI();
    await loadContacts();
    renderContactsList();
}

function updateMyIdentityUI() {
    if (!myIdentity) return;
    document.getElementById('myNicknameDisplay').textContent = myIdentity.nickname;
    document.getElementById('myPeerIdDisplay').textContent = myIdentity.shortId;
    document.getElementById('myAvatarEl').textContent = avatarLetter(myIdentity.nickname);
    document.getElementById('myAvatarEl').style.backgroundColor = avatarColor(myIdentity.shortId);
    
    document.getElementById('profileNickname').value = myIdentity.nickname;
    document.getElementById('profileIdDisplay').textContent = myIdentity.shortId;
}

function renderContactsList() {
    const list = document.getElementById('contactsList');
    const empty = document.getElementById('contactsEmpty');
    
    // Remove old items
    list.querySelectorAll('.contact-item').forEach(el => el.remove());
    
    if (contacts.size === 0) {
        empty.style.display = 'flex';
        return;
    }
    empty.style.display = 'none';
    
    for (const [id, contact] of contacts.entries()) {
        const div = document.createElement('div');
        div.className = 'contact-item' + (id === activeContactId ? ' active' : '');
        div.onclick = () => selectContact(id);
        
        div.innerHTML = `
            <div class="contact-avatar" style="background-color:${avatarColor(id)}">
                ${avatarLetter(contact.nickname)}
                <div class="contact-online-dot"></div>
            </div>
            <div class="contact-info">
                <div class="contact-name">${escapeHtml(getDisplayName(contact))}</div>
                <div class="contact-last-msg"></div>
            </div>
        `;
        list.appendChild(div);
    }
}

function selectContact(id) {
    activeContactId = id;
    renderContactsList();
    
    const contact = contacts.get(id);
    if (!contact) return;
    
    document.getElementById('welcomeScreen').style.display = 'none';
    document.getElementById('chatContainer').style.display = 'flex';
    document.getElementById('connectPanel').style.display = 'block'; // Or hide if connected
    
    document.getElementById('chatPeerName').textContent = getDisplayName(contact);
    document.getElementById('chatPeerId').textContent = id;
    document.getElementById('chatPeerAvatar').textContent = avatarLetter(contact.nickname);
    document.getElementById('chatPeerAvatar').style.backgroundColor = avatarColor(id);
    
    hideSidebarOnMobile();
}

async function saveProfile() {
    const nick = document.getElementById('profileNickname').value.trim();
    if (nick) myIdentity.nickname = nick;
    await persistIdentity();
    updateMyIdentityUI();
    closeModal('profileOverlay');
}