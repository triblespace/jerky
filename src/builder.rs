//! Generic builder trait for streaming construction.
//!
//! Types implementing this trait provide a way to push items incrementally and
//! finalize them into a concrete structure using [`Builder::build`].

use anyhow::Result;

/// Generic builder interface for streaming construction of data structures.
pub trait Builder {
    /// Item type accepted by the builder.
    type Item;
    /// Final type produced by [`Self::build`].
    type Build;

    /// Pushes a single item into the builder.
    fn push(&mut self, item: Self::Item) -> Result<()>;

    /// Extends the builder with items from an iterator.
    fn extend<I>(&mut self, iter: I) -> Result<()>
    where
        I: IntoIterator<Item = Self::Item>,
    {
        for item in iter {
            self.push(item)?;
        }
        Ok(())
    }

    /// Finalizes the builder and returns the constructed value.
    fn build(self) -> Self::Build;
}

/// Convenience trait for constructing objects through a streaming [`Builder`].
pub trait Build: Sized {
    /// Builder type used for construction.
    type Builder: Builder<Build = Self>;

    /// Returns a new builder instance.
    fn builder() -> Self::Builder;

    /// Creates an instance from an iterator of items.
    fn from_iter<I>(iter: I) -> Result<Self>
    where
        I: IntoIterator<Item = <Self::Builder as Builder>::Item>,
    {
        let mut b = Self::builder();
        b.extend(iter)?;
        Ok(b.build())
    }
}
