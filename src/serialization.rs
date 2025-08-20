//! Zero-copy serialization utilities.

use anybytes::Bytes;
use anyhow::Result;

/// Types that can be reconstructed from frozen [`Bytes`] using metadata.
///
/// Implementors write their data into a [`ByteArea`](anybytes::ByteArea) and
/// expose lightweight metadata that describes where their bytes live. Given
/// the metadata and the full `Bytes` region, the type can be rebuilt without
/// copying.
pub trait Serializable: Sized {
    /// Metadata describing the byte layout required to reconstruct `Self`.
    type Meta;

    /// Returns metadata for this instance.
    fn metadata(&self) -> Self::Meta;

    /// Rebuilds an instance from metadata and the arena's frozen bytes.
    fn from_bytes(meta: Self::Meta, bytes: Bytes) -> Result<Self>;
}
