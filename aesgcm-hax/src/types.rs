/// AES-128 key (128 bits).
pub type AesKey = [u8; 16];

/// AES block (128 bits).
pub type AesBlock = [u8; 16];

/// GCM nonce (96 bits).
pub type GcmNonce = [u8; 12];

/// GCM authentication tag (128 bits).
pub type GcmTag = [u8; 16];

/// GHASH accumulator state (128 bits).
pub type GcmState = [u8; 16];
