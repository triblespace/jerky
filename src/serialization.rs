//! Zero-copy serialization utilities.

use anybytes::Bytes;
use anyhow::Result;

/// Marker trait for metadata structures that can be safely written to and
/// read from bytes.
///
/// Types implementing this trait satisfy the requirements from `zerocopy` and
/// `anybytes` for zero-copy serialization. It is automatically implemented for
/// any type that implements the necessary `zerocopy` traits.
pub trait Metadata: zerocopy::FromBytes + zerocopy::KnownLayout + zerocopy::Immutable {}

impl<T> Metadata for T where T: zerocopy::FromBytes + zerocopy::KnownLayout + zerocopy::Immutable {}

/// Types that can be reconstructed from frozen [`Bytes`] using metadata.
///
/// Implementors write their data into a [`ByteArea`](anybytes::ByteArea) and
/// expose lightweight metadata that describes where their bytes live. Given
/// the metadata and the full `Bytes` region, the type can be rebuilt without
/// copying.
pub trait Serializable: Sized {
    /// Metadata describing the byte layout required to reconstruct `Self`.
    type Meta: Metadata;

    /// Returns metadata for this instance.
    fn metadata(&self) -> Self::Meta;

    /// Rebuilds an instance from metadata and the arena's frozen bytes.
    fn from_bytes(meta: Self::Meta, bytes: Bytes) -> Result<Self>;
}
