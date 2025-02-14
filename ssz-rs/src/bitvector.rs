use crate::{
    de::{Deserialize, DeserializeError},
    error::{Error, InstanceError, TypeError},
    lib::*,
    merkleization::{
        get_power_of_two_ceil, merkleize, pack_bytes, proofs::Chunkable, GeneralizedIndex,
        GeneralizedIndexable, HashTreeRoot, MerkleizationError, Node, Path, PathElement,
        BITS_PER_CHUNK,
    },
    ser::{Serialize, SerializeError},
    visitor::Visitable,
    Serializable, SimpleSerialize,
};
#[cfg(feature = "serde")]
use alloy_primitives::Bytes;
use bitvec::{
    field::BitField,
    prelude::{BitVec, Lsb0},
};

const BITS_PER_BYTE: usize = crate::BITS_PER_BYTE as usize;

fn byte_length(bound: usize) -> usize {
    bound.div_ceil(BITS_PER_BYTE)
}

type BitvectorInner = BitVec<u8, Lsb0>;

/// A homogenous collection of a fixed number of boolean values.
///
/// NOTE: a `Bitvector` of length `0` is illegal.
// NOTE: once `const_generics` and `const_evaluatable_checked` features stabilize,
// this type can use something like
// bitvec::array::BitArray<T, {N / 8}> where T: BitRegister, [T; {N / 8}]: BitViewSized
//
// Refer: <https://stackoverflow.com/a/65462213>
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Bitvector<const N: usize>(BitvectorInner);

impl<const N: usize> fmt::Debug for Bitvector<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "Bitvector<{N}>[")?;
        let len = self.len();
        let mut bits_written = 0;
        for (index, bit) in self.iter().enumerate() {
            let value = i32::from(*bit);
            write!(f, "{value}")?;
            bits_written += 1;
            // SAFETY: checked subtraction is unnecessary, as len >= 1 for bitvectors; qed
            if bits_written % 4 == 0 && index != len - 1 {
                write!(f, "_")?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}

impl<const N: usize> Default for Bitvector<N> {
    fn default() -> Self {
        // SAFETY: there is currently no way to enforce statically
        // that `N` is non-zero with const generics so panics are possible.
        assert!(N > 0);

        Self(BitVec::repeat(false, N))
    }
}

impl<const N: usize> Bitvector<N> {
    /// Return the bit at `index`. `None` if index is out-of-bounds.
    pub fn get(&self, index: usize) -> Option<bool> {
        self.0.get(index).map(|value| *value)
    }

    /// Set the bit at `index` to `value`. Return the previous value
    /// or `None` if index is out-of-bounds.
    pub fn set(&mut self, index: usize, value: bool) -> Option<bool> {
        self.get_mut(index).map(|mut slot| {
            let old = *slot;
            *slot = value;
            old
        })
    }

    fn pack_bits(&self) -> Result<Vec<u8>, MerkleizationError> {
        let mut data = vec![];
        let _ = self.serialize(&mut data)?;
        pack_bytes(&mut data);
        Ok(data)
    }

    fn chunk_count() -> usize {
        N.div_ceil(BITS_PER_CHUNK)
    }
}

impl<const N: usize> Deref for Bitvector<N> {
    type Target = BitvectorInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const N: usize> DerefMut for Bitvector<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<const N: usize> Serializable for Bitvector<N> {
    fn is_variable_size() -> bool {
        false
    }

    fn size_hint() -> usize {
        byte_length(N)
    }
}

impl<const N: usize> Serialize for Bitvector<N> {
    fn serialize(&self, buffer: &mut Vec<u8>) -> Result<usize, SerializeError> {
        if N == 0 {
            return Err(TypeError::InvalidBound(N).into());
        }
        let bytes_to_write = Self::size_hint();
        buffer.reserve(bytes_to_write);
        for byte in self.0.chunks(BITS_PER_BYTE) {
            buffer.push(byte.load());
        }
        Ok(bytes_to_write)
    }
}

impl<const N: usize> Deserialize for Bitvector<N> {
    fn deserialize(encoding: &[u8]) -> Result<Self, DeserializeError> {
        if N == 0 {
            return Err(TypeError::InvalidBound(N).into());
        }

        let expected_length = byte_length(N);
        if encoding.len() < expected_length {
            return Err(DeserializeError::ExpectedFurtherInput {
                provided: encoding.len(),
                expected: expected_length,
            });
        }
        if encoding.len() > expected_length {
            return Err(DeserializeError::AdditionalInput {
                provided: encoding.len(),
                expected: expected_length,
            });
        }

        let mut result = Self::default();
        for (slot, byte) in result.chunks_mut(BITS_PER_BYTE).zip(encoding.iter().copied()) {
            slot.store_le(byte);
        }
        let remainder_count = N % BITS_PER_BYTE;
        if remainder_count != 0 {
            let last_byte = encoding.last().unwrap();
            let remainder_bits = last_byte >> remainder_count;
            if remainder_bits != 0 {
                return Err(DeserializeError::InvalidByte(*last_byte));
            }
        }
        Ok(result)
    }
}

impl<const N: usize> HashTreeRoot for Bitvector<N> {
    fn hash_tree_root(&self) -> Result<Node, MerkleizationError> {
        let chunks = self.pack_bits()?;
        merkleize(&chunks, Some(Self::chunk_count()))
    }
}

impl<const N: usize> GeneralizedIndexable for Bitvector<N> {
    fn chunk_count() -> usize {
        Self::chunk_count()
    }

    fn compute_generalized_index(
        parent: GeneralizedIndex,
        path: Path,
    ) -> Result<GeneralizedIndex, MerkleizationError> {
        if let Some((next, rest)) = path.split_first() {
            match next {
                PathElement::Index(i) => {
                    if *i >= N {
                        return Err(MerkleizationError::InvalidPathElement(next.clone()));
                    }
                    let chunk_position = i / 256;
                    let child = parent *
                        get_power_of_two_ceil(<Self as GeneralizedIndexable>::chunk_count()) +
                        chunk_position;
                    // NOTE: use `bool` as effective type of element
                    bool::compute_generalized_index(child, rest)
                }
                elem => Err(MerkleizationError::InvalidPathElement(elem.clone())),
            }
        } else {
            Ok(parent)
        }
    }
}

impl<const N: usize> Visitable for Bitvector<N> {}

impl<const N: usize> Chunkable for Bitvector<N> {
    fn chunks(&self) -> Result<Vec<u8>, MerkleizationError> {
        self.pack_bits()
    }
}

impl<const N: usize> SimpleSerialize for Bitvector<N> {}

impl<const N: usize> TryFrom<&[u8]> for Bitvector<N> {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        Self::deserialize(value).map_err(Error::Deserialize)
    }
}

impl<const N: usize> TryFrom<&[bool]> for Bitvector<N> {
    type Error = Error;

    fn try_from(value: &[bool]) -> Result<Self, Self::Error> {
        if value.len() != N {
            let len = value.len();
            Err(Error::Instance(InstanceError::Exact { required: N, provided: len }))
        } else {
            let mut result = Self::default();
            for (i, &bit) in value.iter().enumerate() {
                result.set(i, bit);
            }
            Ok(result)
        }
    }
}

#[cfg(feature = "serde")]
impl<const N: usize> serde::Serialize for Bitvector<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut buf = Vec::with_capacity(byte_length(N));
        Serialize::serialize(self, &mut buf).map_err(serde::ser::Error::custom)?;
        alloy_primitives::serde_hex::serialize(Bytes::from(buf), serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, const N: usize> serde::Deserialize<'de> for Bitvector<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let data: Bytes = alloy_primitives::serde_hex::deserialize(deserializer)?;
        Self::try_from(data.as_ref()).map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::serialize;

    const COUNT: usize = 12;

    #[test]
    fn encode_bitvector() {
        let value: Bitvector<4> = Bitvector::default();
        let encoding = serialize(&value).expect("can encode");
        let expected = [0u8];
        assert_eq!(encoding, expected);

        let value: Bitvector<COUNT> = Bitvector::default();
        let encoding = serialize(&value).expect("can encode");
        let expected = [0u8, 0u8];
        assert_eq!(encoding, expected);

        let mut value: Bitvector<COUNT> = Bitvector::default();
        value.set(3, true).expect("test data correct");
        value.set(4, true).expect("test data correct");
        assert!(value.get(4).expect("test data correct"));
        assert!(!value.get(0).expect("test data correct"));
        let encoding = serialize(&value).expect("can encode");
        let expected = [24u8, 0u8];
        assert_eq!(encoding, expected);
    }

    #[test]
    fn decode_bitvector() {
        let bytes = vec![12u8];
        let result = Bitvector::<4>::deserialize(&bytes).expect("test data is correct");
        let expected = Bitvector::try_from([false, false, true, true].as_ref()).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn decode_bitvector_several() {
        let bytes = vec![24u8, 1u8];
        let result = Bitvector::<COUNT>::deserialize(&bytes).expect("test data is correct");
        let expected = Bitvector::try_from(
            [false, false, false, true, true, false, false, false, true, false, false, false]
                .as_ref(),
        )
        .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn roundtrip_bitvector() {
        let input = Bitvector::<COUNT>::try_from(
            [false, false, false, true, true, false, false, false, false, false, false, false]
                .as_ref(),
        )
        .unwrap();
        let mut buffer = vec![];
        let _ = input.serialize(&mut buffer).expect("can serialize");
        let recovered = Bitvector::<COUNT>::deserialize(&buffer).expect("can decode");
        assert_eq!(input, recovered);
    }

    #[test]
    fn serde_roundtrip() {
        let input = Bitvector::<COUNT>::try_from(
            [false, false, false, true, true, false, false, false, false, false, false, false]
                .as_ref(),
        )
        .unwrap();

        let serialization = serde_json::to_string(&input).unwrap();
        let recovered: Bitvector<COUNT> = serde_json::from_str(&serialization).expect("can decode");
        assert_eq!(input, recovered);
    }

    #[test]
    fn serde_bitvector() {
        let input = Bitvector::<COUNT>::try_from(
            [false, false, false, true, true, false, false, false, false, true, false, false]
                .as_ref(),
        )
        .unwrap();

        let serialization = serde_json::to_string(&input).unwrap();
        assert_eq!(serialization, "\"0x1802\"");
    }
}
