use crate::SimpleSerialize;
use std::fmt::{self, Display, Formatter};

#[derive(Debug)]
pub enum VisitorError {
    NoInnerElement,
    InvalidInnerIndex,
}

impl Display for VisitorError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoInnerElement => {
                write!(f, "requested to visit inner element which does not exist for this type")
            }
            Self::InvalidInnerIndex => write!(
                f,
                "requested to visit inner element outside the bounds of what this type supports"
            ),
        }
    }
}

/// A trait for types that can be visited by a `Visitor`.
/// All types that implement SimpleSerialize are visitable which is how proving and other algorithms
/// are implemented
pub trait Visitable {
    fn visit_element<V: Visitor>(&self, _index: usize, _visitor: &mut V) -> Result<(), V::Error> {
        Err(VisitorError::NoInnerElement.into())
    }

    fn element_count(&self) -> usize {
        0
    }
}

/// A trait for implementing the visitor pattern to traverse the SSZ data structures
///
/// Examples of visitors are the Prover for generating SSZ Merkle proofs.
/// Crate consumers can implement their own visitors to add diffent algorithms for generating proofs
/// or other behaviour
pub trait Visitor: Sized {
    type Error: From<VisitorError>;

    fn visit<T: SimpleSerialize + Visitable + ?Sized>(
        &mut self,
        element: &T,
    ) -> Result<(), Self::Error>;
}
