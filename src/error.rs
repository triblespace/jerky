//! Common error types used throughout the crate.

use std::fmt;

use anybytes::view::ViewError;

/// Result type used across the crate.
pub type Result<T, E = Error> = std::result::Result<T, E>;

/// Error type covering failures across Jerky data structures.
#[derive(Debug)]
pub enum Error {
    /// An argument violated preconditions.
    InvalidArgument(String),
    /// Deserialized metadata was malformed or inconsistent.
    InvalidMetadata(String),
    /// A mismatch between serialized hint flags and the requested type.
    MismatchedHintFlags,
    /// Wrapper around [`std::io::Error`] values.
    Io(std::io::Error),
    /// Wrapper around [`anybytes::ViewError`] values.
    View(ViewError),
}

impl Error {
    /// Creates an [`Error::InvalidArgument`] with the provided message.
    pub fn invalid_argument(msg: impl Into<String>) -> Self {
        Self::InvalidArgument(msg.into())
    }

    /// Creates an [`Error::InvalidMetadata`] with the provided message.
    pub fn invalid_metadata(msg: impl Into<String>) -> Self {
        Self::InvalidMetadata(msg.into())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidArgument(msg) => write!(f, "{msg}"),
            Error::InvalidMetadata(msg) => write!(f, "{msg}"),
            Error::MismatchedHintFlags => write!(f, "mismatched hint flags"),
            Error::Io(err) => write!(f, "I/O error: {err}"),
            Error::View(err) => write!(f, "view error: {err}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::InvalidArgument(_) | Error::InvalidMetadata(_) | Error::MismatchedHintFlags => {
                None
            }
            Error::Io(err) => Some(err),
            Error::View(err) => Some(err),
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        Error::Io(err)
    }
}

impl From<ViewError> for Error {
    fn from(err: ViewError) -> Self {
        Error::View(err)
    }
}
