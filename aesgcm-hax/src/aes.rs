use crate::types::{AesBlock, AesKey};

/// Trait abstracting the AES-128 block cipher.
///
/// The trait lets the block cipher be treated as an opaque primitive by
/// an extraction backend; [`crate::aes_impl::RealAes`] and
/// [`crate::realgcm::RealGcm`] implement it with FIPS 197 AES-128.
pub trait AesCipher: Copy {
    /// Encrypt a single 128-bit block under AES-128.
    fn aes128_encrypt_block(self, key: &AesKey, block: &AesBlock) -> AesBlock;
}
