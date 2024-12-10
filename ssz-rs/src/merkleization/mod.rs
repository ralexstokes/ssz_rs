pub mod generalized_index;
mod merkleize;
pub mod multiproofs;
mod node;
pub mod proofs;

use crate::{lib::*, ser::SerializeError};
pub use generalized_index::{
    get_power_of_two_ceil, GeneralizedIndex, GeneralizedIndexable, Path, PathElement,
};
pub use merkleize::*;
pub use node::*;

pub(crate) const BYTES_PER_CHUNK: usize = 32;
pub(crate) const BITS_PER_CHUNK: usize = BYTES_PER_CHUNK * (crate::BITS_PER_BYTE as usize);

/// An error encountered during merkleization.
#[derive(Debug)]
pub enum MerkleizationError {
    /// An error serializing a type while computing the hash tree.
    SerializationError(SerializeError),
    /// More data was provided than expected
    InputExceedsLimit(usize),
    /// Proof verification failed
    InvalidProof,
    /// Signals an invalid generalized index (e.g. `0`) was presented.
    InvalidGeneralizedIndex,
    /// Signals an invalid type of path element when walking a `GeneralizedIndexable` type
    InvalidPathElement(PathElement),
    /// Signals an invalid path when walking a `GeneralizedIndexable` type
    InvalidPath(Vec<PathElement>),
    /// Attempt to prove an inner element outside the bounds of what the implementing type
    /// supports.
    InvalidInnerIndex,
    /// Attempt to prove an inner element for a "basic" type that doesn't have one
    NoInnerElement,
    /// Attempt to turn an instance of a type in Merkle chunks when this is not supported
    NotChunkable,
}

impl From<SerializeError> for MerkleizationError {
    fn from(err: SerializeError) -> Self {
        MerkleizationError::SerializationError(err)
    }
}

impl Display for MerkleizationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::SerializationError(err) => {
                write!(f, "failed to serialize value: {err}")
            }
            Self::InputExceedsLimit(size) => write!(f, "data exceeds the declared limit {size}"),
            Self::InvalidProof => write!(f, "merkle proof verification failed"),
            Self::InvalidGeneralizedIndex => write!(f, "invalid generalized index"),
            Self::InvalidPathElement(element) => write!(f, "invalid path element {element:?}"),
            Self::InvalidPath(path) => write!(f, "invalid path {path:?}"),
            Self::InvalidInnerIndex => write!(f, "requested to compute proof for an inner element outside the bounds of what this type supports"),
            Self::NoInnerElement => write!(
                f,
                "requested to compute proof for an inner element which does not exist for this type"
            ),
            Self::NotChunkable => {
                write!(f, "requested to compute chunks for a type which does not support this")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for MerkleizationError {}
