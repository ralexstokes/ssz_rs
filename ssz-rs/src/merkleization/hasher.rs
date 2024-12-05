use super::BYTES_PER_CHUNK;

use ::sha2::{Digest, Sha256};

#[inline]
fn hash_chunks_sha256(left: impl AsRef<[u8]>, right: impl AsRef<[u8]>) -> [u8; BYTES_PER_CHUNK] {
    let mut hasher = Sha256::new();
    hasher.update(left.as_ref());
    hasher.update(right.as_ref());
    hasher.finalize_reset().into()
}

/// Function that hashes 2 [BYTES_PER_CHUNK] (32) len byte slices together. Depending on the feature
/// flags, this will either use:
/// - sha256 (default)
/// - TODO: sha256 with assembly support (with the "sha2-asm" feature flag)
/// - TODO: hashtree (with the "hashtree" feature flag)
#[inline]
pub fn hash_chunks(left: impl AsRef<[u8]>, right: impl AsRef<[u8]>) -> [u8; BYTES_PER_CHUNK] {
    debug_assert!(left.as_ref().len() == BYTES_PER_CHUNK);
    debug_assert!(right.as_ref().len() == BYTES_PER_CHUNK);
    hash_chunks_sha256(left, right)
}
