//! Support for computing Merkle trees.
use crate::{
    lib::*,
    merkleization::{hasher::hash_chunks, MerkleizationError as Error, Node, BYTES_PER_CHUNK},
    ser::Serialize,
    GeneralizedIndex,
};
#[cfg(feature = "serde")]
use alloy_primitives::hex::FromHex;
use std::thread;

// The generalized index for the root of the "decorated" type in any Merkleized type that supports
// decoration.
const INNER_ROOT_GENERALIZED_INDEX: GeneralizedIndex = 2;
// The generalized index for the "decoration" in any Merkleized type that supports decoration.
const DECORATION_GENERALIZED_INDEX: GeneralizedIndex = 3;

/// Types that can provide the root of their corresponding Merkle tree following the SSZ spec.
pub trait HashTreeRoot {
    /// Compute the "hash tree root" of `Self`.
    fn hash_tree_root(&self) -> Result<Node, Error>;

    /// Indicate the "composite" nature of `Self`.
    fn is_composite_type() -> bool {
        true
    }
}

// Ensures `buffer` can be exactly broken up into `BYTES_PER_CHUNK` chunks of bytes
// via padding any partial chunks at the end of `buffer`
pub fn pack_bytes(buffer: &mut Vec<u8>) {
    let incomplete_chunk_len = buffer.len() % BYTES_PER_CHUNK;
    if incomplete_chunk_len != 0 {
        // SAFETY: checked subtraction is unnecessary,
        // as BYTES_PER_CHUNK > incomplete_chunk_len; qed
        let bytes_to_pad = BYTES_PER_CHUNK - incomplete_chunk_len;
        buffer.resize(buffer.len() + bytes_to_pad, 0);
    }
}

// Packs serializations of `values` into the return buffer with the
// guarantee that `buffer.len() % BYTES_PER_CHUNK == 0`
pub fn pack<T>(values: &[T]) -> Result<Vec<u8>, Error>
where
    T: Serialize,
{
    let mut buffer = vec![];
    for value in values {
        value.serialize(&mut buffer)?;
    }
    pack_bytes(&mut buffer);
    Ok(buffer)
}

fn hash_nodes(a: impl AsRef<[u8]>, b: impl AsRef<[u8]>, out: &mut [u8]) {
    out.copy_from_slice(&hash_chunks(a, b));
}

const MAX_MERKLE_TREE_DEPTH: usize = 64;

#[derive(Debug)]
struct Context {
    zero_hashes: [u8; MAX_MERKLE_TREE_DEPTH * BYTES_PER_CHUNK],
}

impl Index<usize> for Context {
    type Output = [u8];

    fn index(&self, index: usize) -> &Self::Output {
        &self.zero_hashes[index * BYTES_PER_CHUNK..(index + 1) * BYTES_PER_CHUNK]
    }
}

// Grab the precomputed context from the build stage
include!(concat!(env!("OUT_DIR"), "/context.rs"));

/// Return the root of the root node of a binary tree formed from `chunks`.
///
/// `chunks` forms the bottom layer of this tree.
///
/// This implementation is memory efficient by relying on pre-computed subtrees of all
/// "zero" leaves stored in the `CONTEXT`. SSZ specifies that `chunks` is padded to the next power
/// of two and this can be quite large for some types. "Zero" subtrees are virtualized to avoid the
/// memory and computation cost of large trees with partially empty leaves.
///
/// The implementation approach treats `chunks` as the bottom layer of a perfect binary tree
/// and for each height performs the hashing required to compute the parent layer in place.
/// This process is repated until the root is computed.
///
/// Invariant: `chunks.len() % BYTES_PER_CHUNK == 0`
/// Invariant: `leaf_count.next_power_of_two() == leaf_count`
/// Invariant: `leaf_count != 0`
/// Invariant: `leaf_count.trailing_zeros() < MAX_MERKLE_TREE_DEPTH`
fn merkleize_chunks_with_virtual_padding(chunks: &[u8], leaf_count: usize) -> Result<Node, Error> {
    debug_assert!(chunks.len() % BYTES_PER_CHUNK == 0);
    // NOTE: This also asserts that leaf_count != 0
    debug_assert!(leaf_count.next_power_of_two() == leaf_count);
    // SAFETY: this holds as long as leaf_count != 0 and usize is no longer than u64
    debug_assert!((leaf_count.trailing_zeros() as usize) < MAX_MERKLE_TREE_DEPTH);

    let chunk_count = chunks.len() / BYTES_PER_CHUNK;
    let height = leaf_count.trailing_zeros() + 1;

    if chunk_count == 0 {
        // SAFETY: checked subtraction is unnecessary, as height >= 1; qed
        let depth = height - 1;
        // SAFETY: index is safe while depth == leaf_count.trailing_zeros() < MAX_MERKLE_TREE_DEPTH;
        // qed
        return Ok(CONTEXT[depth as usize].try_into().expect("can produce a single root chunk"));
    }

    let mut layer = chunks.to_vec();
    // SAFETY: checked subtraction is unnecessary, as we return early when chunk_count == 0; qed
    let mut last_index = chunk_count - 1;
    // for each layer of the tree, starting from the bottom and walking up to the root:
    for k in (1..height).rev() {
        // for each pair of nodes in this layer:
        for i in (0..2usize.pow(k)).step_by(2) {
            let parent_index = i / 2;
            let (parent, left, right) = match i.cmp(&last_index) {
                Ordering::Less => {
                    // SAFETY: index is safe because (i+1)*BYTES_PER_CHUNK < layer.len():
                    // i < last_index == chunk_count - 1 == (layer.len() / BYTES_PER_CHUNK) - 1
                    // so i+1 < layer.len() / BYTES_PER_CHUNK
                    // so (i+1)*BYTES_PER_CHUNK < layer.len(); qed
                    let focus =
                        &mut layer[parent_index * BYTES_PER_CHUNK..(i + 2) * BYTES_PER_CHUNK];
                    // SAFETY: checked subtraction is unnecessary:
                    // focus.len() = (i + 2 - parent_index) * BYTES_PER_CHUNK
                    // and
                    // i >= parent_index
                    // so focus.len() >= 2 * BYTES_PER_CHUNK; qed
                    let children_index = focus.len() - 2 * BYTES_PER_CHUNK;
                    let (parent, children) = focus.split_at_mut(children_index);
                    let (left, right) = children.split_at_mut(BYTES_PER_CHUNK);

                    // NOTE: we do not need mutability on `right` here so drop that capability
                    (parent, left, &*right)
                }
                Ordering::Equal => {
                    // SAFETY: index is safe because i*BYTES_PER_CHUNK < layer.len():
                    // i*BYTES_PER_CHUNK < (i+1)*BYTES_PER_CHUNK < layer.len()
                    // (see previous case); qed
                    let focus =
                        &mut layer[parent_index * BYTES_PER_CHUNK..(i + 1) * BYTES_PER_CHUNK];
                    // SAFETY: checked subtraction is unnecessary:
                    // focus.len() = (i + 1 - parent_index) * BYTES_PER_CHUNK
                    // and
                    // i >= parent_index
                    // so focus.len() >= BYTES_PER_CHUNK; qed
                    let children_index = focus.len() - BYTES_PER_CHUNK;
                    // NOTE: left.len() == BYTES_PER_CHUNK
                    let (parent, left) = focus.split_at_mut(children_index);
                    // SAFETY: checked subtraction is unnecessary:
                    // k <= height - 1
                    // so depth >= height - (height - 1) - 1
                    //           = 0; qed
                    let depth = height - k - 1;
                    // SAFETY: index is safe because depth < CONTEXT.len():
                    // depth <= height - 1 == leaf_count.trailing_zeros()
                    // leaf_count.trailing_zeros() < MAX_MERKLE_TREE_DEPTH == CONTEXT.len(); qed
                    let right = &CONTEXT[depth as usize];
                    (parent, left, right)
                }
                _ => break,
            };
            if i == 0 {
                // NOTE: nodes share memory here and so we can't use the `hash_nodes` utility
                // as the disjunct nature is reflect in that functions type signature
                // so instead we will just replicate here.
                left.copy_from_slice(&hash_chunks(&left, right));
            } else {
                // SAFETY: index is safe because parent.len() % BYTES_PER_CHUNK == 0 and
                // parent isn't empty; qed
                hash_nodes(left, right, &mut parent[..BYTES_PER_CHUNK]);
            }
        }
        last_index /= 2;
    }

    // SAFETY: index is safe because layer.len() >= BYTES_PER_CHUNK:
    // layer.len() == chunks.len()
    // chunks.len() % BYTES_PER_CHUNK == 0 and chunks.len() != 0 (because chunk_count != 0)
    // so chunks.len() >= BYTES_PER_CHUNK; qed
    Ok(layer[..BYTES_PER_CHUNK].try_into().expect("can produce a single root chunk"))
}

// Return the root of the Merklization of a binary tree formed from `chunks`.
// Invariant: `chunks.len() % BYTES_PER_CHUNK == 0`
pub fn merkleize(chunks: &[u8], limit: Option<usize>) -> Result<Node, Error> {
    debug_assert!(chunks.len() % BYTES_PER_CHUNK == 0);
    let chunk_count = chunks.len() / BYTES_PER_CHUNK;
    let mut leaf_count = chunk_count.next_power_of_two();
    if let Some(limit) = limit {
        if limit < chunk_count {
            return Err(Error::InputExceedsLimit(limit));
        }
        leaf_count = limit.next_power_of_two();
    }
    merkleize_chunks_with_virtual_padding(chunks, leaf_count)
}

fn mix_in_decoration(root: Node, decoration: usize) -> Node {
    let decoration_data = decoration.hash_tree_root().expect("can merkleize usize");

    let mut output = vec![0u8; BYTES_PER_CHUNK];
    hash_nodes(root, decoration_data, &mut output);
    output.as_slice().try_into().expect("can extract root")
}

pub(crate) fn mix_in_length(root: Node, length: usize) -> Node {
    mix_in_decoration(root, length)
}

pub fn mix_in_selector(root: Node, selector: usize) -> Node {
    mix_in_decoration(root, selector)
}

pub(crate) fn elements_to_chunks<'a, T: HashTreeRoot + 'a>(
    elements: impl Iterator<Item = (usize, &'a T)>,
    count: usize,
) -> Result<Vec<u8>, Error> {
    let mut chunks = vec![0u8; count * BYTES_PER_CHUNK];
    for (i, elem) in elements {
        let chunk = elem.hash_tree_root()?;
        let range = i * BYTES_PER_CHUNK..(i + 1) * BYTES_PER_CHUNK;
        chunks[range].copy_from_slice(chunk.as_ref());
    }
    Ok(chunks)
}

pub struct Tree(Vec<u8>);

impl Tree {
    pub fn mix_in_decoration(&mut self, decoration: usize) -> Result<(), Error> {
        let target_node = &mut self[DECORATION_GENERALIZED_INDEX];
        let decoration_node = decoration.hash_tree_root()?;
        target_node.copy_from_slice(decoration_node.as_ref());
        let out =
            hash_chunks(&self[INNER_ROOT_GENERALIZED_INDEX], &self[DECORATION_GENERALIZED_INDEX]);
        self[1].copy_from_slice(&out);
        Ok(())
    }

    #[cfg(feature = "serde")]
    fn nodes(&self) -> impl Iterator<Item = Node> + '_ {
        self.0.chunks(BYTES_PER_CHUNK).map(|chunk| Node::from_hex(chunk).unwrap())
    }
}

impl Index<GeneralizedIndex> for Tree {
    type Output = [u8];

    fn index(&self, index: GeneralizedIndex) -> &Self::Output {
        let start = (index - 1) * BYTES_PER_CHUNK;
        let end = index * BYTES_PER_CHUNK;
        &self.0[start..end]
    }
}

impl IndexMut<GeneralizedIndex> for Tree {
    fn index_mut(&mut self, index: GeneralizedIndex) -> &mut Self::Output {
        let start = (index - 1) * BYTES_PER_CHUNK;
        let end = index * BYTES_PER_CHUNK;
        &mut self.0[start..end]
    }
}

#[cfg(feature = "serde")]
impl std::fmt::Debug for Tree {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.nodes()).finish()
    }
}

// Return the full Merkle tree of the `chunks`.
// Invariant: `chunks.len() % BYTES_PER_CHUNK == 0`
// Invariant: `leaf_count.next_power_of_two() == leaf_count`
// NOTE: naive implementation, can make much more efficient
pub fn compute_merkle_tree(chunks: &[u8], leaf_count: usize) -> Result<Tree, Error> {
    // Input validation
    debug_assert!(chunks.len() % BYTES_PER_CHUNK == 0);
    debug_assert!(leaf_count.next_power_of_two() == leaf_count);

    // Calculate nodes needed in tree
    // SAFETY: checked subtraction is unnecessary,
    // as leaf_count != 0 (0.next_power_of_two() == 1); qed
    let node_count = 2 * leaf_count - 1;
    // SAFETY: checked subtraction is unnecessary, as node_count >= leaf_count; qed
    let interior_count = node_count - leaf_count;
    let leaf_start = interior_count * BYTES_PER_CHUNK;

    // Return early if there are less than two chunks
    if leaf_count < 2 {
        return Ok(Tree(chunks.to_vec()));
    }

    // Create buffer to entire tree
    let mut buffer = vec![0u8; node_count * BYTES_PER_CHUNK];

    // Copy input chunks to leaf positions
    buffer[leaf_start..leaf_start + chunks.len()].copy_from_slice(chunks);

    // Detect number of CPU cores
    let num_cores = thread::available_parallelism().map(|n| n.get()).unwrap_or(1);

    if leaf_count >= 16 && num_cores >= 8 {
        compute_merkle_tree_parallel_8(&mut buffer, node_count);
    } else if leaf_count >= 16 && num_cores >= 4 {
        compute_merkle_tree_parallel_4(&mut buffer, node_count);
    } else {
        compute_merkle_tree_serial(&mut buffer, node_count);
    }

    Ok(Tree(buffer))
}

// Compute the Merkle tree in parallel.
//
// We can take advantage of the fact that the tree is a perfect binary tree
// and process subtrees in parallel bottom-up.

//              0
//       /            \
//      1              2
//    /    \        /    \
//   3      4      5      6
//  / \    / \    / \    / \
// 7   8  9  10  11 12  13 14

// Split tree into 4 subtrees
fn compute_merkle_tree_parallel_4(buffer: &mut [u8], node_count: usize) {
    let nodes = split_merkle_tree_nodes(node_count);

    // Create buffers for each section
    let mut left_left_buf = vec![0u8; nodes.left_left.len() * BYTES_PER_CHUNK];
    let mut left_right_buf = vec![0u8; nodes.left_right.len() * BYTES_PER_CHUNK];
    let mut right_left_buf = vec![0u8; nodes.right_left.len() * BYTES_PER_CHUNK];
    let mut right_right_buf = vec![0u8; nodes.right_right.len() * BYTES_PER_CHUNK];

    // Copy data to section buffers
    copy_nodes_to_buffer(buffer, &nodes.left_left, &mut left_left_buf);
    copy_nodes_to_buffer(buffer, &nodes.left_right, &mut left_right_buf);
    copy_nodes_to_buffer(buffer, &nodes.right_left, &mut right_left_buf);
    copy_nodes_to_buffer(buffer, &nodes.right_right, &mut right_right_buf);

    // Process all sections in parallel
    rayon::scope(|s| {
        s.spawn(|_| process_subtree(&mut left_left_buf, nodes.left_left.len()));
        s.spawn(|_| process_subtree(&mut left_right_buf, nodes.left_right.len()));
        s.spawn(|_| process_subtree(&mut right_left_buf, nodes.right_left.len()));
        s.spawn(|_| process_subtree(&mut right_right_buf, nodes.right_right.len()));
    });

    // Copy results back
    copy_buffer_to_nodes(&left_left_buf, &nodes.left_left, buffer);
    copy_buffer_to_nodes(&left_right_buf, &nodes.left_right, buffer);
    copy_buffer_to_nodes(&right_left_buf, &nodes.right_left, buffer);
    copy_buffer_to_nodes(&right_right_buf, &nodes.right_right, buffer);

    // Compute node 1 from 3 and 4
    let node1_hash = hash_chunks(
        &buffer[3 * BYTES_PER_CHUNK..4 * BYTES_PER_CHUNK],
        &buffer[4 * BYTES_PER_CHUNK..5 * BYTES_PER_CHUNK],
    );
    buffer[BYTES_PER_CHUNK..2 * BYTES_PER_CHUNK].copy_from_slice(&node1_hash);

    // Compute node 2 from 5 and 6
    let node2_hash = hash_chunks(
        &buffer[5 * BYTES_PER_CHUNK..6 * BYTES_PER_CHUNK],
        &buffer[6 * BYTES_PER_CHUNK..7 * BYTES_PER_CHUNK],
    );
    buffer[2 * BYTES_PER_CHUNK..3 * BYTES_PER_CHUNK].copy_from_slice(&node2_hash);

    // Compute the root from 1 and 2
    let root_hash = hash_chunks(
        &buffer[BYTES_PER_CHUNK..2 * BYTES_PER_CHUNK],
        &buffer[2 * BYTES_PER_CHUNK..3 * BYTES_PER_CHUNK],
    );
    buffer[..BYTES_PER_CHUNK].copy_from_slice(&root_hash);
}

// Split tree into 8 subtrees with roots (7, 8, 9, 10, 11, 12, 13, 14)
//              0
//       /            \
//      1              2
//    /    \        /    \
//   3      4      5      6
//  / \    / \    / \    / \
// 7   8  9  10  11 12  13 14
// /\  /\ /\  /\ /\  /\ /\  /\
//15 16...              ...29 30
fn compute_merkle_tree_parallel_8(buffer: &mut [u8], node_count: usize) {
    let nodes = split_merkle_tree_nodes8(node_count);

    // Create buffers for each of the 8 subtrees
    let mut subtree_buffers = vec![
        vec![0u8; nodes.subtree0.len() * BYTES_PER_CHUNK],
        vec![0u8; nodes.subtree1.len() * BYTES_PER_CHUNK],
        vec![0u8; nodes.subtree2.len() * BYTES_PER_CHUNK],
        vec![0u8; nodes.subtree3.len() * BYTES_PER_CHUNK],
        vec![0u8; nodes.subtree4.len() * BYTES_PER_CHUNK],
        vec![0u8; nodes.subtree5.len() * BYTES_PER_CHUNK],
        vec![0u8; nodes.subtree6.len() * BYTES_PER_CHUNK],
        vec![0u8; nodes.subtree7.len() * BYTES_PER_CHUNK],
    ];

    // Copy data to subtree buffers
    copy_nodes_to_buffer(buffer, &nodes.subtree0, &mut subtree_buffers[0]);
    copy_nodes_to_buffer(buffer, &nodes.subtree1, &mut subtree_buffers[1]);
    copy_nodes_to_buffer(buffer, &nodes.subtree2, &mut subtree_buffers[2]);
    copy_nodes_to_buffer(buffer, &nodes.subtree3, &mut subtree_buffers[3]);
    copy_nodes_to_buffer(buffer, &nodes.subtree4, &mut subtree_buffers[4]);
    copy_nodes_to_buffer(buffer, &nodes.subtree5, &mut subtree_buffers[5]);
    copy_nodes_to_buffer(buffer, &nodes.subtree6, &mut subtree_buffers[6]);
    copy_nodes_to_buffer(buffer, &nodes.subtree7, &mut subtree_buffers[7]);

    let subtree_buffer_len = subtree_buffers[0].len();
    // Process all subtrees in parallel
    rayon::scope(|s| {
        for subtree_buffer in &mut subtree_buffers {
            s.spawn(|_| process_subtree(subtree_buffer, subtree_buffer_len / BYTES_PER_CHUNK));
        }
    });

    // Copy results back to the main buffer
    copy_buffer_to_nodes(&subtree_buffers[0], &nodes.subtree0, buffer);
    copy_buffer_to_nodes(&subtree_buffers[1], &nodes.subtree1, buffer);
    copy_buffer_to_nodes(&subtree_buffers[2], &nodes.subtree2, buffer);
    copy_buffer_to_nodes(&subtree_buffers[3], &nodes.subtree3, buffer);
    copy_buffer_to_nodes(&subtree_buffers[4], &nodes.subtree4, buffer);
    copy_buffer_to_nodes(&subtree_buffers[5], &nodes.subtree5, buffer);
    copy_buffer_to_nodes(&subtree_buffers[6], &nodes.subtree6, buffer);
    copy_buffer_to_nodes(&subtree_buffers[7], &nodes.subtree7, buffer);

    // Compute higher level nodes in deterministic order
    let mut level = 3; // Start at level 3 (nodes 7-14)

    while level > 0 {
        let start_idx = (1 << level) - 1;
        let end_idx = (1 << (level + 1)) - 1;

        for parent in (start_idx..end_idx).step_by(2) {
            if parent + 1 >= node_count {
                continue;
            }

            let hash = hash_chunks(
                &buffer[parent * BYTES_PER_CHUNK..(parent + 1) * BYTES_PER_CHUNK],
                &buffer[(parent + 1) * BYTES_PER_CHUNK..(parent + 2) * BYTES_PER_CHUNK],
            );

            let parent_idx = (parent - 1) / 2;
            buffer[parent_idx * BYTES_PER_CHUNK..(parent_idx + 1) * BYTES_PER_CHUNK]
                .copy_from_slice(&hash);
        }

        level -= 1;
    }
}

#[derive(Debug, PartialEq)]
struct SubtreeNodes {
    left_left: Vec<usize>,
    left_right: Vec<usize>,
    right_left: Vec<usize>,
    right_right: Vec<usize>,
}

// Split merkle tree into 4 subtrees
fn split_merkle_tree_nodes(node_count: usize) -> SubtreeNodes {
    let mut left_left = Vec::new();
    let mut left_right = Vec::new();
    let mut right_left = Vec::new();
    let mut right_right = Vec::new();

    // Skip root node (index 0)
    for i in 1..node_count {
        // Current level in tree (0-based)
        let level = (i + 1).ilog2() as usize;
        // Position within level
        let pos_in_level = i - ((1 << level) - 1);

        // Handle level 1 nodes (1,2) - skip them as they're not part of subtrees
        if level == 1 {
            continue;
        }

        // For level 2 nodes (3,4,5,6), they become the roots of our subtrees
        if level == 2 {
            match pos_in_level {
                0 => left_left.push(i),   // Node 3
                1 => left_right.push(i),  // Node 4
                2 => right_left.push(i),  // Node 5
                3 => right_right.push(i), // Node 6
                _ => unreachable!(),
            }
            continue;
        }

        // For deeper levels, assign based on their parent at level 2
        let ancestor_at_level_2 = {
            let steps_up = level - 2;
            let parent_pos = pos_in_level >> steps_up;
            parent_pos + 3 // +3 because level 2 starts at index 3
        };

        // Assign to appropriate subtree based on level 2 ancestor
        match ancestor_at_level_2 {
            3 => left_left.push(i),
            4 => left_right.push(i),
            5 => right_left.push(i),
            6 => right_right.push(i),
            _ => unreachable!(),
        }
    }

    SubtreeNodes { left_left, left_right, right_left, right_right }
}

#[derive(Debug, PartialEq)]
struct SubtreeNodes8 {
    subtree0: Vec<usize>,
    subtree1: Vec<usize>,
    subtree2: Vec<usize>,
    subtree3: Vec<usize>,
    subtree4: Vec<usize>,
    subtree5: Vec<usize>,
    subtree6: Vec<usize>,
    subtree7: Vec<usize>,
}

fn split_merkle_tree_nodes8(node_count: usize) -> SubtreeNodes8 {
    let mut subtrees = SubtreeNodes8 {
        subtree0: Vec::new(),
        subtree1: Vec::new(),
        subtree2: Vec::new(),
        subtree3: Vec::new(),
        subtree4: Vec::new(),
        subtree5: Vec::new(),
        subtree6: Vec::new(),
        subtree7: Vec::new(),
    };

    // Skip root node (index 0) and level 1-2 nodes (1-6)
    for i in 7..node_count {
        // Determine the level of the current node (0-based)
        let level = (i + 1).ilog2() as usize;
        // Position within the current level
        let pos_in_level = i - ((1 << level) - 1);

        // For level 3 nodes (indices 7-14), they become the start of our subtrees
        if level == 3 {
            match i {
                7 => subtrees.subtree0.push(i),
                8 => subtrees.subtree1.push(i),
                9 => subtrees.subtree2.push(i),
                10 => subtrees.subtree3.push(i),
                11 => subtrees.subtree4.push(i),
                12 => subtrees.subtree5.push(i),
                13 => subtrees.subtree6.push(i),
                14 => subtrees.subtree7.push(i),
                _ => unreachable!("Invalid level 3 index"),
            }
            continue;
        }

        // For deeper levels, assign based on their ancestor at level 3
        if level > 3 {
            let ancestor_at_level3 = {
                let steps_up = level - 3;
                let parent_pos = pos_in_level >> steps_up;
                parent_pos + 7 // +7 because level 3 starts at index 7
            };

            match ancestor_at_level3 {
                7 => subtrees.subtree0.push(i),
                8 => subtrees.subtree1.push(i),
                9 => subtrees.subtree2.push(i),
                10 => subtrees.subtree3.push(i),
                11 => subtrees.subtree4.push(i),
                12 => subtrees.subtree5.push(i),
                13 => subtrees.subtree6.push(i),
                14 => subtrees.subtree7.push(i),
                _ => unreachable!("Invalid ancestor index at level 3"),
            }
        }
    }

    subtrees
}

// Compute the Merkle tree serially.
fn compute_merkle_tree_serial(buffer: &mut [u8], node_count: usize) {
    for i in (1..node_count).rev().step_by(2) {
        // SAFETY: checked subtraction is unnecessary, as i >= 1; qed
        let parent_index = (i - 1) / 2;
        let focus = &mut buffer[parent_index * BYTES_PER_CHUNK..(i + 1) * BYTES_PER_CHUNK];
        // SAFETY: checked subtraction is unnecessary:
        // focus.len() = (i + 1 - parent_index) * BYTES_PER_CHUNK
        //             = ((2*i + 2 - i + 1) / 2) * BYTES_PER_CHUNK
        //             = ((i + 3) / 2) * BYTES_PER_CHUNK
        // and
        // i >= 1
        // so focus.len() >= 2 * BYTES_PER_CHUNK; qed
        let children_index = focus.len() - 2 * BYTES_PER_CHUNK;
        // NOTE: children.len() == 2 * BYTES_PER_CHUNK
        let (parent, children) = focus.split_at_mut(children_index);
        let (left, right) = children.split_at(BYTES_PER_CHUNK);
        hash_nodes(left, right, &mut parent[..BYTES_PER_CHUNK]);
    }
}

// Process a subtree of the Merkle tree.
#[inline]
fn process_subtree(buffer: &mut [u8], size: usize) {
    // No pairs to process
    if size < 2 {
        return;
    }
    // Process from leaves up, handling pairs of nodes
    for i in (0..size - 1).rev().step_by(2) {
        let left = &buffer[i * BYTES_PER_CHUNK..(i + 1) * BYTES_PER_CHUNK];
        let right = &buffer[(i + 1) * BYTES_PER_CHUNK..(i + 2) * BYTES_PER_CHUNK];

        // Check if both left and right are all zero or precomputed zero subtree hashes
        let maybe_parent = zero_parent_level(left, right, &CONTEXT);
        // Compute parent hash
        let parent_hash = if let Some(zero_hash) = maybe_parent {
            zero_hash
        } else {
            // Compute the hash normally
            hash_chunks(left, right)
        };

        // Store at parent position (i/2)
        // SAFETY: checked subtraction is unnecessary, as i >= 1; qed
        let parent_index = i / 2;
        let parent_slice =
            &mut buffer[parent_index * BYTES_PER_CHUNK..(parent_index + 1) * BYTES_PER_CHUNK];
        parent_slice.copy_from_slice(&parent_hash);
    }
}

// Determines subtree level if the node is a zero subtree.
fn zero_subtree_level(node: &[u8], context: &Context) -> Option<usize> {
    // Check against precomputed zero hashes in the context
    let total_levels = MAX_MERKLE_TREE_DEPTH;
    for lvl in 0..total_levels {
        if node == &context[lvl][..] {
            return Some(lvl + 1);
        }
    }
    None
}

// Determines the parent hash for a pair of nodes if they are both
// zero subtrees, allowing hashing to be skipped.
fn zero_parent_level(
    left: &[u8],
    right: &[u8],
    context: &Context,
) -> Option<[u8; BYTES_PER_CHUNK]> {
    let left_level = zero_subtree_level(left, context)?;
    let right_level = zero_subtree_level(right, context)?;
    if left_level == right_level {
        // Parent level is one higher
        let parent_lvl = left_level + 1;
        // Zero hashes in context start at index 0 for subtree level 1
        Some(context[parent_lvl - 1].try_into().expect("valid subtree hash"))
    } else {
        None
    }
}

#[inline]
fn copy_nodes_to_buffer(src: &[u8], nodes: &[usize], dst: &mut [u8]) {
    for (i, &node) in nodes.iter().enumerate() {
        let src_start = node * BYTES_PER_CHUNK;
        let dst_start = i * BYTES_PER_CHUNK;
        dst[dst_start..dst_start + BYTES_PER_CHUNK]
            .copy_from_slice(&src[src_start..src_start + BYTES_PER_CHUNK]);
    }
}

#[inline]
fn copy_buffer_to_nodes(src: &[u8], nodes: &[usize], dst: &mut [u8]) {
    for (i, &node) in nodes.iter().enumerate() {
        let src_start = i * BYTES_PER_CHUNK;
        let dst_start = node * BYTES_PER_CHUNK;
        dst[dst_start..dst_start + BYTES_PER_CHUNK]
            .copy_from_slice(&src[src_start..src_start + BYTES_PER_CHUNK]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{merkleization::proofs::tests::decode_node_from_hex, prelude::*};

    // Return the root of the Merklization of a binary tree formed from `chunks`.
    fn merkleize_chunks(chunks: &[u8], leaf_count: usize) -> Result<Node, Error> {
        let tree = compute_merkle_tree(chunks, leaf_count)?;
        let root_index = default_generalized_index();
        Ok(tree[root_index].try_into().expect("can produce a single root chunk"))
    }

    #[test]
    fn test_packing_basic_types_simple() {
        let b = true;
        let mut expected = vec![0u8; BYTES_PER_CHUNK];
        expected[0] = 1u8;
        let input = &[b];
        let result = pack(input).expect("can pack values");
        assert!(result.len() == BYTES_PER_CHUNK);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_packing_basic_types_extended() {
        let b = true;
        let input = &[b, !b, !b, b];
        let result = pack(input).expect("can pack values");

        let mut expected = vec![0u8; BYTES_PER_CHUNK];
        expected[0] = 1u8;
        expected[3] = 1u8;
        assert_eq!(result, expected);
    }

    #[test]
    fn test_packing_basic_types_multiple() {
        let data = U256::from_le_bytes([1u8; 32]);
        let input = &[data, data, data];
        let result = pack(input).expect("can pack values");

        let expected = vec![1u8; 3 * 32];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_merkleize_basic() {
        let input = &[];
        let result = merkleize(input, None).expect("can merkle");
        assert_eq!(result, Node::default());

        let b = true;
        let input = &[b];
        let input = pack(input).expect("can pack");
        let result = merkleize(&input, None).expect("can merkle");
        let mut expected = Node::default();
        expected[0] = 1u8;
        assert_eq!(result, expected);
    }

    #[test]
    fn test_naive_merkleize_chunks() {
        let chunks = vec![0u8; 2 * BYTES_PER_CHUNK];
        let root = merkleize_chunks(&chunks, 2).expect("can merkleize");
        assert_eq!(
            root,
            decode_node_from_hex(
                "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
            )
        );

        let chunks = vec![1u8; 2 * BYTES_PER_CHUNK];
        let root = merkleize_chunks(&chunks, 2).expect("can merkleize");
        assert_eq!(
            root,
            decode_node_from_hex(
                "7c8975e1e60a5c8337f28edf8c33c3b180360b7279644a9bc1af3c51e6220bf5"
            )
        );

        let chunks = vec![0u8; BYTES_PER_CHUNK];
        let root = merkleize_chunks(&chunks, 4).expect("can merkleize");
        assert_eq!(
            root,
            decode_node_from_hex(
                "db56114e00fdd4c1f85c892bf35ac9a89289aaecb1ebd0a96cde606a748b5d71"
            )
        );

        let chunks = vec![1u8; BYTES_PER_CHUNK];
        let root = merkleize_chunks(&chunks, 4).expect("can merkleize");
        assert_eq!(
            root,
            decode_node_from_hex(
                "29797eded0e83376b70f2bf034cc0811ae7f1414653b1d720dfd18f74cf13309"
            )
        );

        let chunks = vec![2u8; BYTES_PER_CHUNK];
        let root = merkleize_chunks(&chunks, 8).expect("can merkleize");
        assert_eq!(
            root,
            decode_node_from_hex(
                "fa4cf775712aa8a2fe5dcb5a517d19b2e9effcf58ff311b9fd8e4a7d308e6d00"
            )
        );

        let chunks = vec![1u8; 5 * BYTES_PER_CHUNK];
        let root = merkleize_chunks(&chunks, 8).expect("can merkleize");
        assert_eq!(
            root,
            decode_node_from_hex(
                "0ae67e34cba4ad2bbfea5dc39e6679b444021522d861fab00f05063c54341289"
            )
        );
    }

    #[test]
    fn test_merkleize_chunks() {
        let chunks = vec![1u8; 3 * BYTES_PER_CHUNK];
        let root = merkleize_chunks_with_virtual_padding(&chunks, 4).expect("can merkleize");
        assert_eq!(
            root,
            decode_node_from_hex(
                "65aa94f2b59e517abd400cab655f42821374e433e41b8fe599f6bb15484adcec"
            )
        );

        let chunks = vec![1u8; 5 * BYTES_PER_CHUNK];
        let root = merkleize_chunks_with_virtual_padding(&chunks, 8).expect("can merkleize");
        assert_eq!(
            root,
            decode_node_from_hex(
                "0ae67e34cba4ad2bbfea5dc39e6679b444021522d861fab00f05063c54341289"
            )
        );

        let chunks = vec![1u8; 6 * BYTES_PER_CHUNK];
        let root = merkleize_chunks_with_virtual_padding(&chunks, 8).expect("can merkleize");
        assert_eq!(
            root,
            decode_node_from_hex(
                "0ef7df63c204ef203d76145627b8083c49aa7c55ebdee2967556f55a4f65a238"
            )
        );
    }

    #[test]
    fn test_merkleize_chunks_with_many_virtual_nodes() {
        let chunks = vec![1u8; 5 * BYTES_PER_CHUNK];
        let root =
            merkleize_chunks_with_virtual_padding(&chunks, 2usize.pow(10)).expect("can merkleize");
        assert_eq!(
            root,
            decode_node_from_hex(
                "2647cb9e26bd83eeb0982814b2ac4d6cc4a65d0d98637f1a73a4c06d3db0e6ce"
            )
        );

        let chunks = vec![1u8; 70 * BYTES_PER_CHUNK];
        let root =
            merkleize_chunks_with_virtual_padding(&chunks, 2usize.pow(63)).expect("can merkleize");
        assert_eq!(
            root,
            decode_node_from_hex(
                "9317695d95b5a3b46e976b5a9cbfcfccb600accaddeda9ac867cc9669b862979"
            )
        );
    }

    #[test]
    fn test_split_merkle_tree_nodes_tree() {
        //              0
        //       /            \
        //      1              2
        //    /    \        /    \
        //   3      4      5      6
        //  / \    / \    / \    / \
        // 7   8  9  10  11 12  13 14
        let nodes = split_merkle_tree_nodes(15);

        assert_eq!(nodes.left_left, vec![3, 7, 8]);
        assert_eq!(nodes.left_right, vec![4, 9, 10]);
        assert_eq!(nodes.right_left, vec![5, 11, 12]);
        assert_eq!(nodes.right_right, vec![6, 13, 14]);
    }

    #[test]
    fn test_split_merkle_tree_nodes_16_leaves() {
        //              0
        //       /            \
        //      1              2
        //    /    \        /    \
        //   3      4      5      6
        //  / \    / \    / \    / \
        // 7   8  9  10  11 12  13 14
        // /\  /\ /\  /\ /\  /\ /\  /\
        //15 16...           ...29 30

        let nodes = split_merkle_tree_nodes(31);

        assert_eq!(nodes.left_left, vec![3, 7, 8, 15, 16, 17, 18]);
        assert_eq!(nodes.left_right, vec![4, 9, 10, 19, 20, 21, 22]);
        assert_eq!(nodes.right_left, vec![5, 11, 12, 23, 24, 25, 26]);
        assert_eq!(nodes.right_right, vec![6, 13, 14, 27, 28, 29, 30]);
    }

    #[test]
    fn test_split_nodes_empty_tree() {
        // Test edge case with just root node
        let nodes = split_merkle_tree_nodes(1);

        assert_eq!(nodes.left_left, Vec::<usize>::new());
        assert_eq!(nodes.left_right, Vec::<usize>::new());
        assert_eq!(nodes.right_left, Vec::<usize>::new());
        assert_eq!(nodes.right_right, Vec::<usize>::new());
    }

    #[test]
    fn test_split_merkle_tree_nodes8_16_leaves() {
        //              0
        //       /            \
        //      1              2
        //    /    \        /    \
        //   3      4      5      6
        //  / \    / \    / \    / \
        // 7   8  9  10  11 12  13 14
        // /\  /\ /\  /\ /\  /\ /\  /\
        //15 16...              ...29 30

        let nodes = split_merkle_tree_nodes8(31);

        assert_eq!(nodes.subtree0, vec![7, 15, 16]);
        assert_eq!(nodes.subtree1, vec![8, 17, 18]);
        assert_eq!(nodes.subtree2, vec![9, 19, 20]);
        assert_eq!(nodes.subtree3, vec![10, 21, 22]);
        assert_eq!(nodes.subtree4, vec![11, 23, 24]);
        assert_eq!(nodes.subtree5, vec![12, 25, 26]);
        assert_eq!(nodes.subtree6, vec![13, 27, 28]);
        assert_eq!(nodes.subtree7, vec![14, 29, 30]);
    }

    #[test]
    fn test_process_subtree_with_size_zero() {
        let mut buffer = vec![0u8; 0];
        process_subtree(&mut buffer, 0);
        // Expect no panic and buffer remains unchanged
        assert_eq!(buffer.len(), 0);
    }

    #[test]
    fn test_process_subtree_with_size_one() {
        let mut buffer = vec![1u8; BYTES_PER_CHUNK];
        process_subtree(&mut buffer, 1);
        // Expect no changes since there's only one node
        assert_eq!(buffer, vec![1u8; BYTES_PER_CHUNK]);
    }

    #[test]
    fn test_process_subtree_with_size_two() {
        let mut buffer = vec![2u8; 2 * BYTES_PER_CHUNK];

        // Manually compute the expected hash of the two nodes
        let left_node = &buffer[0..BYTES_PER_CHUNK];
        let right_node = &buffer[BYTES_PER_CHUNK..2 * BYTES_PER_CHUNK];
        let expected_hash = hash_chunks(left_node, right_node);

        // Process the subtree
        process_subtree(&mut buffer, 2);

        // Extract the parent node (first 32 bytes)
        let parent_node = &buffer[0..BYTES_PER_CHUNK];

        // Assert that the parent node now contains the expected hash
        assert_eq!(parent_node, expected_hash.to_vec().as_slice());
    }

    #[test]
    fn test_hash_tree_root_of_list() {
        let a_list = List::<u16, 1024>::try_from(vec![
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
            65535, 65535, 65535, 65535,
        ])
        .unwrap();
        let root = a_list.hash_tree_root().expect("can compute root");
        assert_eq!(
            root,
            decode_node_from_hex(
                "d20d2246e1438d88de46f6f41c7b041f92b673845e51f2de93b944bf599e63b1"
            )
        );
    }

    #[test]
    fn test_hash_tree_root_of_empty_list() {
        let a_list = List::<u16, 1024>::try_from(vec![]).unwrap();
        let root = a_list.hash_tree_root().expect("can compute root");
        assert_eq!(
            root,
            decode_node_from_hex(
                "c9eece3e14d3c3db45c38bbf69a4cb7464981e2506d8424a0ba450dad9b9af30"
            )
        );
    }

    #[test]
    fn test_hash_tree_root() {
        #[derive(PartialEq, Eq, Debug, SimpleSerialize, Clone)]
        enum Bar {
            A(u32),
            B(List<bool, 32>),
        }

        impl Default for Bar {
            fn default() -> Self {
                Self::A(Default::default())
            }
        }

        #[derive(PartialEq, Eq, Debug, Default, SimpleSerialize, Clone)]
        struct Foo {
            a: u32,
            b: Vector<u32, 4>,
            c: bool,
            d: Bitlist<27>,
            e: Bar,
            f: Bitvector<4>,
            g: List<u16, 7>,
        }

        let mut foo = Foo {
            a: 16u32,
            b: Vector::try_from(vec![3u32, 2u32, 1u32, 10u32]).unwrap(),
            c: true,
            d: Bitlist::try_from(
                [
                    true, false, false, true, true, false, true, false, true, true, false, false,
                    true, true, false, true, false, true, true, false, false, true, true, false,
                    true, false, true,
                ]
                .as_ref(),
            )
            .unwrap(),
            e: Bar::B(List::try_from(vec![true, true, false, false, false, true]).unwrap()),
            f: Bitvector::try_from([false, true, false, true].as_ref()).unwrap(),
            g: List::try_from(vec![1, 2]).unwrap(),
        };

        let root = foo.hash_tree_root().expect("can make root");
        assert_eq!(
            root,
            decode_node_from_hex(
                "7078155bf8f0dc42d8afccec8d9b5aeb54f0a2e8e58fcef3e723f6a867232ce7"
            )
        );

        let original_foo = foo.clone();

        foo.b[2] = 44u32;
        foo.d.pop();
        foo.e = Bar::A(33);

        let root = original_foo.hash_tree_root().expect("can make root");
        assert_eq!(
            root,
            decode_node_from_hex(
                "7078155bf8f0dc42d8afccec8d9b5aeb54f0a2e8e58fcef3e723f6a867232ce7"
            )
        );

        let root = foo.hash_tree_root().expect("can make root");
        assert_eq!(
            root,
            decode_node_from_hex(
                "0063bfcfabbca567483a2ee859fcfafb958329489eb328ac7f07790c7df1b231"
            )
        );

        let encoding = serialize(&original_foo).expect("can serialize");

        let mut restored_foo = Foo::deserialize(&encoding).expect("can deserialize");

        let root = restored_foo.hash_tree_root().expect("can make root");
        assert_eq!(
            root,
            decode_node_from_hex(
                "7078155bf8f0dc42d8afccec8d9b5aeb54f0a2e8e58fcef3e723f6a867232ce7"
            )
        );

        restored_foo.b[2] = 44u32;
        restored_foo.d.pop();
        restored_foo.e = Bar::A(33);

        let root = foo.hash_tree_root().expect("can make root");
        assert_eq!(
            root,
            decode_node_from_hex(
                "0063bfcfabbca567483a2ee859fcfafb958329489eb328ac7f07790c7df1b231"
            )
        );
    }

    #[test]
    fn test_simple_serialize_of_root() {
        let root = Node::default();
        let mut result = vec![];
        let _ = root.serialize(&mut result).expect("can encode");
        let expected_encoding = vec![0; 32];
        assert_eq!(result, expected_encoding);

        let recovered_root = Node::deserialize(&result).expect("can decode");
        assert_eq!(recovered_root, Node::default());

        let hash_tree_root = root.hash_tree_root().expect("can find root");
        assert_eq!(hash_tree_root, Node::default());
    }

    #[test]
    fn test_derive_hash_tree_root() {
        #[derive(Debug, HashTreeRoot)]
        struct Foo {
            a: U256,
        }

        let foo = Foo { a: U256::from(68) };
        let foo_root = foo.hash_tree_root().unwrap();
        let expected_root = decode_node_from_hex(
            "4400000000000000000000000000000000000000000000000000000000000000",
        );
        assert_eq!(foo_root, expected_root);
    }
}
