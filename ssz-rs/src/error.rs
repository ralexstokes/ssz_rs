use crate::{de::DeserializeError, lib::*, merkleization::MerkleizationError, ser::SerializeError};

/// Top-level error to wrap all other errors in this crate
#[derive(Debug)]
pub enum Error {
    /// A serialization error.
    Serialize(SerializeError),
    /// A deserialization error.
    Deserialize(DeserializeError),
    /// A merkleization error.
    Merkleization(MerkleizationError),
    Instance(InstanceError),
    Type(TypeError),
}

impl From<SerializeError> for Error {
    fn from(err: SerializeError) -> Self {
        Self::Serialize(err)
    }
}

impl From<DeserializeError> for Error {
    fn from(err: DeserializeError) -> Self {
        Self::Deserialize(err)
    }
}

impl From<MerkleizationError> for Error {
    fn from(err: MerkleizationError) -> Self {
        Self::Merkleization(err)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Serialize(err) => write!(f, "could not serialize: {err}"),
            Self::Deserialize(err) => write!(f, "could not deserialize: {err}"),
            Self::Merkleization(err) => write!(f, "merkleization error: {err}"),
            Self::Instance(err) => write!(f, "error constructing instance: {err}"),
            Self::Type(err) => write!(f, "type error: {err}"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

#[derive(Debug)]
pub enum TypeError {
    /// A type is invalid within the given bounds.
    InvalidBound(usize),
}

impl Display for TypeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidBound(size) => {
                write!(f, "the type for this value is invalid with bound {size}")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TypeError {}

/// Instance errors.
#[derive(Debug)]
pub enum InstanceError {
    /// The number of elements did not match (`provided != required`)
    Exact { required: usize, provided: usize },
    /// The number of elements exceeded the maximum expected amount (`provided > bound`)
    Bounded { bound: usize, provided: usize },
}

impl Display for InstanceError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Exact { required, provided } => write!(
                f,
                "required {required} elements for this type but {provided} elements given"
            ),
            Self::Bounded { bound, provided } => write!(
                f,
                "{provided} elements given for a type with (inclusive) upper bound {bound}"
            ),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InstanceError {}
