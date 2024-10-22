//! An implementation of the [SSZ][ssz] serialization scheme.
//!
//! # Examples
//!
//! {De,}serialize a simple value:
//!
//! ```
//! # use ssz_rs::prelude::*;
//! let mut buf = Vec::new();
//! 42u64.serialize(&mut buf);
//! assert_eq!(u64::deserialize(&buf).unwrap(), 42);
//! ```
//!
//! {De,}serialize a custom type using the derive macro:
//!
//! ```
//! # use ssz_rs::prelude::*;
//! #[derive(Debug, Default, PartialEq, Eq, SimpleSerialize)]
//! struct Data {
//!   flag: bool,
//!   value: u64
//! }
//!
//! let mut buf = Vec::new();
//! Data { flag: true, value: 42 }.serialize(&mut buf);
//! assert_eq!(
//!   Data::deserialize(&buf).unwrap(),
//!   Data { flag: true, value: 42 }
//! );
//! ```
//!
//! Compute the root of some type's SSZ merkle tree:
//!
//! ```
//! # use ssz_rs::prelude::*;
//! # use alloy_primitives::hex::FromHex;
//! #[derive(Debug, Default, PartialEq, Eq, SimpleSerialize)]
//! struct SomeOtherData {
//!   flag: bool,
//!   value: u64
//! }
//!
//! let root = SomeOtherData { flag: true, value: 42 }.hash_tree_root().unwrap();
//! assert_eq!(
//!   root,
//!   Node::from_hex("0xabde25256089fc38a25254778ebc4c8812dfd1a31e9634b013c6ff1983a77eda").unwrap()
//! );
//! ```
//!
//! Compute "generalized" indices for a given type:
//!
//! ```
//! # use ssz_rs::prelude::*;
//! #[derive(Debug, Default, PartialEq, Eq, SimpleSerialize)]
//! struct SomeType {
//!   flag: u8,
//!   value: List<U256, 800>,
//! }
//!
//! let path = &["value".into(), 23.into()];
//! let index = SomeType::generalized_index(path).unwrap();
//! assert_eq!(
//!   index,
//!   6167
//! );
//! ```
//!
//! Generate (and verify) a Merkle proof for some node in the type's Merkle tree:
//!
//! ```
//! # use ssz_rs::prelude::*;
//! #[derive(Debug, Default, PartialEq, Eq, SimpleSerialize)]
//! struct YetAnotherType {
//!   flag: u8,
//!   value: List<U256, 800>,
//! }
//!
//! let path = &["value".into(), 23.into()];
//! let data = YetAnotherType::default();
//! let (proof, witness) = data.prove(path).unwrap();
//! assert!(proof.verify(witness).is_ok());
//! ```
//!
//! [ssz]: https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md

#[cfg(not(feature = "std"))]
extern crate alloc;

mod array;
mod bitlist;
mod bitvector;
mod boolean;
mod container;
mod de;
mod error;
mod list;
mod merkleization;
mod ser;
#[cfg(feature = "serde")]
mod serde;
mod uint;
mod union;
mod vector;

mod lib {
    mod core {
        #[cfg(not(feature = "std"))]
        pub use core::*;
        #[cfg(feature = "std")]
        pub use std::*;
    }

    pub use self::core::{any, cmp, fmt};

    pub use self::{
        cmp::Ordering,
        core::{
            fmt::{Debug, Display, Formatter},
            ops::{Deref, DerefMut, Index, IndexMut},
            slice::SliceIndex,
        },
    };

    #[cfg(not(feature = "std"))]
    pub use alloc::{format, string::String, string::ToString, vec, vec::Vec};

    #[cfg(feature = "std")]
    pub use std::vec::Vec;

    #[cfg(not(feature = "std"))]
    pub use alloc::collections::{BTreeMap as HashMap, BTreeSet as HashSet};

    #[cfg(feature = "std")]
    pub use std::collections::{HashMap, HashSet};

    #[cfg(feature = "serde")]
    pub use self::core::marker::PhantomData;
}

pub(crate) const BITS_PER_BYTE: u32 = 8;

/// `Serializable` is a trait for types that can be
/// serialized and deserialized according to the SSZ spec.
pub trait Serializable: Serialize + Deserialize {
    // is this type variable or fixed size?
    fn is_variable_size() -> bool;

    // expected number of bytes for the serialization of this type
    // or 0 if unknown ahead of time
    fn size_hint() -> usize;
}

/// `SimpleSerialize` is a trait for types conforming to the SSZ spec.
/// These types can be encoded and decoded while also supporting the
/// merkelization scheme of SSZ.
pub trait SimpleSerialize: Serializable + HashTreeRoot + GeneralizedIndexable + Prove {}

mod exports {
    pub use crate::{
        bitlist::Bitlist,
        bitvector::Bitvector,
        de::{Deserialize, DeserializeError},
        error::{Error as SimpleSerializeError, InstanceError, TypeError},
        list::List,
        merkleization::{
            generalized_index::default_generalized_index,
            multiproofs,
            proofs::{self, is_valid_merkle_branch, Prove},
            GeneralizedIndex, GeneralizedIndexable, HashTreeRoot, MerkleizationError, Node, Path,
            PathElement,
        },
        ser::{Serialize, SerializeError},
        uint::U256,
        vector::Vector,
    };

    /// `serialize` is a convenience function for taking a value that
    /// implements `SimpleSerialize` and attempts to encode it to
    /// a `Vec<u8>` according to the SSZ spec.
    pub fn serialize<T>(value: &T) -> Result<crate::lib::Vec<u8>, SerializeError>
    where
        T: crate::Serializable,
    {
        let mut result = crate::lib::Vec::new();
        value.serialize(&mut result)?;
        Ok(result)
    }

    /// `deserialize` is a convenience function for taking an encoding
    /// for some value that implements `SimpleSerialize` in a `&[u8]`
    /// and attempting to deserialize that value from the byte representation.
    pub fn deserialize<T>(encoding: &[u8]) -> Result<T, DeserializeError>
    where
        T: crate::Serializable,
    {
        T::deserialize(encoding)
    }
}

pub use crate::exports::*;

/// The `prelude` contains common traits and types a user of this library
/// would want to have handy with a simple (single) import.
pub mod prelude {
    pub use crate::{exports::*, Serializable, SimpleSerialize};

    // expose this so the derive macro has everything in scope
    // with a simple `prelude` import
    #[doc(hidden)]
    pub use crate as ssz_rs;
    pub use ssz_rs_derive::{
        GeneralizedIndexable, HashTreeRoot, Prove, Serializable, SimpleSerialize,
    };
}

#[doc(hidden)]
/// `internal` contains functionality that is exposed purely for the derive proc macro crate
pub mod __internal {
    // exported for derive macro to avoid code duplication...
    pub use crate::{
        de::ContainerDeserializer,
        merkleization::{generalized_index::get_power_of_two_ceil, merkleize, mix_in_selector},
        ser::Serializer,
    };
}
