use crate::{
    de::{deserialize_homogeneous_composite, Deserialize, DeserializeError},
    error::{InstanceError, TypeError},
    lib::*,
    merkleization::{
        elements_to_chunks, get_power_of_two_ceil, merkleize, pack, proofs::Chunkable,
        GeneralizedIndex, GeneralizedIndexable, HashTreeRoot, MerkleizationError, Node, Path,
        PathElement,
    },
    ser::{Serialize, SerializeError, Serializer},
    visitor::{self, Visitable, Visitor},
    Serializable, SimpleSerialize,
};

impl<T, const N: usize> Serializable for [T; N]
where
    T: Serializable,
{
    fn is_variable_size() -> bool {
        T::is_variable_size()
    }

    fn size_hint() -> usize {
        T::size_hint() * N
    }
}

impl<T, const N: usize> Serialize for [T; N]
where
    T: Serializable,
{
    fn serialize(&self, buffer: &mut Vec<u8>) -> Result<usize, SerializeError> {
        if N == 0 {
            return Err(TypeError::InvalidBound(N).into());
        }
        let mut serializer = Serializer::default();
        for element in self {
            serializer.with_element(element)?;
        }
        serializer.serialize(buffer)
    }
}

impl<T, const N: usize> Deserialize for [T; N]
where
    T: Serializable,
{
    fn deserialize(encoding: &[u8]) -> Result<Self, DeserializeError> {
        if N == 0 {
            return Err(TypeError::InvalidBound(N).into());
        }

        if !T::is_variable_size() {
            let expected_length = N * T::size_hint();
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
        }
        let elements = deserialize_homogeneous_composite(encoding)?;
        elements.try_into().map_err(|elements: Vec<T>| {
            InstanceError::Exact { required: N, provided: elements.len() }.into()
        })
    }
}

impl<T, const N: usize> HashTreeRoot for [T; N]
where
    T: SimpleSerialize,
{
    fn hash_tree_root(&self) -> Result<Node, MerkleizationError> {
        let chunks = self.chunks()?;
        merkleize(&chunks, None)
    }

    fn is_composite_type() -> bool {
        T::is_composite_type()
    }
}

impl<T, const N: usize> GeneralizedIndexable for [T; N]
where
    T: SimpleSerialize,
{
    fn chunk_count() -> usize {
        (N * T::item_length() + 31) / 32
    }

    fn compute_generalized_index(
        parent: GeneralizedIndex,
        path: Path<'_>,
    ) -> Result<GeneralizedIndex, MerkleizationError> {
        if let Some((next, rest)) = path.split_first() {
            match next {
                PathElement::Index(i) => {
                    if *i >= N {
                        return Err(MerkleizationError::InvalidPathElement(next.clone()));
                    }
                    let chunk_position = i * T::item_length() / 32;
                    let child =
                        parent * get_power_of_two_ceil(Self::chunk_count()) + chunk_position;
                    T::compute_generalized_index(child, rest)
                }
                elem => Err(MerkleizationError::InvalidPathElement(elem.clone())),
            }
        } else {
            Ok(parent)
        }
    }
}

impl<T, const N: usize> Visitable for [T; N]
where
    T: SimpleSerialize + Visitable,
{
    fn visit_element<V: Visitor>(&self, index: usize, visitor: &mut V) -> Result<(), V::Error> {
        if index >= N {
            Err(visitor::VisitorError::InvalidInnerIndex.into())
        } else {
            let child = &self[index];
            visitor.visit(child)
        }
    }

    fn element_count(&self) -> usize {
        N
    }
}

impl<T, const N: usize> Chunkable for [T; N]
where
    T: SimpleSerialize,
{
    fn chunks(&self) -> Result<Vec<u8>, MerkleizationError> {
        if T::is_composite_type() {
            let count = self.len();
            elements_to_chunks(self.iter().enumerate(), count)
        } else {
            pack(self)
        }
    }
}

impl<T, const N: usize> SimpleSerialize for [T; N] where T: SimpleSerialize {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::*;

    #[test]
    fn test_some_arrays() {
        let a = [22u8; 3];
        let serialized_a = serialize(&a).unwrap();
        let recovered_a = <[u8; 3]>::deserialize(&serialized_a).unwrap();
        assert_eq!(a, recovered_a);

        let a = [22u8; 333];
        let serialized_a = serialize(&a).unwrap();
        let recovered_a = <[u8; 333]>::deserialize(&serialized_a).unwrap();
        assert_eq!(a, recovered_a);
    }
}
