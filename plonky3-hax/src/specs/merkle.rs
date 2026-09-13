//! Binary Merkle trees for the reference STARK.
//!
//! Leaves and inner nodes are 32-byte values. `hash_two_to_one` and
//! `hash_leaf` are byte-wise mixing functions with no collision resistance;
//! they are placeholders, not cryptographic hashes, and a security argument
//! about this module has to model them as an ideal hash.

/// Hash output size in bytes (256-bit digest).
pub const HASH_SIZE: usize = 32;

/// A Merkle tree root commitment.
pub type MerkleRoot = [u8; HASH_SIZE];

/// A single node hash in the Merkle tree.
pub type MerkleHash = [u8; HASH_SIZE];

/// Maximum Merkle tree depth. Baby Bear supports 2^27 roots of unity,
/// so 27 is a safe upper bound for Plonky3 tree depth.
pub const MAX_MERKLE_DEPTH: usize = 27;

/// A Merkle authentication path: sibling hashes from leaf to root.
/// `siblings[0]` is the sibling of the leaf; `siblings[depth - 1]` is
/// the sibling of the root's child. `depth` indicates how many entries
/// are valid.
pub struct MerklePath {
    pub siblings: [MerkleHash; MAX_MERKLE_DEPTH],
    pub depth: usize,
}

impl Clone for MerklePath {
    fn clone(&self) -> Self {
        MerklePath {
            siblings: self.siblings,
            depth: self.depth,
        }
    }
}

/// Hash two child nodes to produce a parent node hash.
///
/// A byte-wise mixing function of `left` and `right`; it is not
/// collision-resistant.
pub fn hash_two_to_one(left: MerkleHash, right: MerkleHash) -> MerkleHash {
    let mut result = [0u8; HASH_SIZE];
    for i in 0..HASH_SIZE {
        let l = left[i];
        let r = right[i];
        result[i] = l
            .wrapping_add(r)
            .wrapping_mul(0x9E)
            .wrapping_add(i as u8)
            ^ l.wrapping_mul(0x6D)
            ^ r;
    }
    for j in 1..HASH_SIZE {
        result[j] ^= result[j - 1].wrapping_mul(0xC5);
    }
    result
}

/// Hash a leaf value (a Baby Bear field element, 8 bytes little-endian,
/// padded to 32 with a 0x00 domain separator).
pub fn hash_leaf(value_bytes: [u8; 8]) -> MerkleHash {
    let mut input = [0u8; HASH_SIZE];
    // Domain separator for leaves
    input[0] = 0x00;
    for i in 0..8 {
        input[i + 1] = value_bytes[i];
    }
    let mut result = [0u8; HASH_SIZE];
    for k in 0..HASH_SIZE {
        result[k] = input[k].wrapping_add(0x37).wrapping_mul(0xBF)
            ^ input[(k + 7) % HASH_SIZE];
    }
    for m in 1..HASH_SIZE {
        result[m] = result[m].wrapping_add(result[m - 1].wrapping_mul(0xA3));
    }
    result
}

/// Serialize a Baby Bear field element (u64, canonical < p) to
/// little-endian bytes.
pub fn field_elem_to_bytes(x: u64) -> [u8; 8] {
    [
        (x & 0xFF) as u8,
        ((x >> 8) & 0xFF) as u8,
        ((x >> 16) & 0xFF) as u8,
        ((x >> 24) & 0xFF) as u8,
        ((x >> 32) & 0xFF) as u8,
        ((x >> 40) & 0xFF) as u8,
        ((x >> 48) & 0xFF) as u8,
        ((x >> 56) & 0xFF) as u8,
    ]
}

/// Hash a Baby Bear field element as a Merkle leaf.
pub fn hash_field_elem(x: u64) -> MerkleHash {
    hash_leaf(field_elem_to_bytes(x))
}

/// Verify a Merkle authentication path.
///
/// At each level, if the current index bit is 0 the current hash is the
/// left child and the sibling is the right child; otherwise vice versa.
/// Returns true iff the recomputed root matches the expected root.
pub fn merkle_verify_path(
    root: MerkleRoot,
    leaf_hash: MerkleHash,
    index: u64,
    path: &MerklePath,
) -> bool {
    if path.depth > MAX_MERKLE_DEPTH {
        return false;
    }

    let mut current = leaf_hash;
    let mut idx = index;

    for level in 0..path.depth {
        let sibling = path.siblings[level];
        if idx & 1 == 0 {
            current = hash_two_to_one(current, sibling);
        } else {
            current = hash_two_to_one(sibling, current);
        }
        idx >>= 1;
    }

    let mut equal = true;
    for i in 0..HASH_SIZE {
        if current[i] != root[i] {
            equal = false;
        }
    }
    equal
}

/// Build a Merkle tree from leaf hashes and return the root.
///
/// Requires `num_leaves` to be `0` or a power of two with
/// `num_leaves <= 1024` and `num_leaves <= leaves.len()`; larger trees index
/// out of bounds.
pub fn merkle_build_root(leaves: &[MerkleHash], num_leaves: usize) -> MerkleRoot {
    if num_leaves == 0 {
        return [0u8; HASH_SIZE];
    }
    if num_leaves == 1 {
        return leaves[0];
    }

    const MAX_LEAVES: usize = 1024;
    const MAX_LOG_LEAVES: usize = 10; // log2(MAX_LEAVES)
    let mut buf: [MerkleHash; MAX_LEAVES] = [[0u8; HASH_SIZE]; MAX_LEAVES];

    let n_load = num_leaves.min(MAX_LEAVES);
    for i in 0..n_load {
        buf[i] = leaves[i];
    }

    let mut width = num_leaves;
    for _ in 0..MAX_LOG_LEAVES {
        if width <= 1 {
            break;
        }
        let half = width / 2;
        for j in 0..half {
            buf[j] = hash_two_to_one(buf[2 * j], buf[2 * j + 1]);
        }
        width = half;
    }

    buf[0]
}

/// Build a tree and extract the authentication path for a leaf index.
/// Used by the prover / tests.
pub fn merkle_build_and_prove(
    leaves: &[MerkleHash],
    num_leaves: usize,
    leaf_index: usize,
) -> (MerkleRoot, MerklePath) {
    let mut path = MerklePath {
        siblings: [[0u8; HASH_SIZE]; MAX_MERKLE_DEPTH],
        depth: 0,
    };

    if num_leaves <= 1 {
        let root = if num_leaves == 1 {
            leaves[0]
        } else {
            [0u8; HASH_SIZE]
        };
        return (root, path);
    }

    const MAX_LEAVES: usize = 1024;
    const MAX_DEPTH: usize = 10;
    let mut levels: [[MerkleHash; MAX_LEAVES]; MAX_DEPTH + 1] =
        [[[0u8; HASH_SIZE]; MAX_LEAVES]; MAX_DEPTH + 1];

    let n_load = num_leaves.min(MAX_LEAVES);
    for i in 0..n_load {
        levels[0][i] = leaves[i];
    }

    let mut width = num_leaves;
    let mut depth: usize = 0;
    for _ in 0..MAX_DEPTH {
        if width <= 1 {
            break;
        }
        let half = width / 2;
        for j in 0..half {
            levels[depth + 1][j] =
                hash_two_to_one(levels[depth][2 * j], levels[depth][2 * j + 1]);
        }
        width = half;
        depth += 1;
    }

    let mut idx = leaf_index;
    for level in 0..depth {
        let sibling_idx = if idx & 1 == 0 { idx + 1 } else { idx - 1 };
        path.siblings[level] = levels[level][sibling_idx];
        idx >>= 1;
    }
    path.depth = depth;

    let root = levels[depth][0];
    (root, path)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_two_to_one_deterministic() {
        let a = [0x01u8; HASH_SIZE];
        let b = [0x02u8; HASH_SIZE];
        assert_eq!(hash_two_to_one(a, b), hash_two_to_one(a, b));
    }

    #[test]
    fn test_hash_two_to_one_not_commutative() {
        let a = [0x01u8; HASH_SIZE];
        let b = [0x02u8; HASH_SIZE];
        assert_ne!(hash_two_to_one(a, b), hash_two_to_one(b, a));
    }

    #[test]
    fn test_merkle_single_leaf() {
        let leaf = hash_field_elem(42);
        let path = MerklePath {
            siblings: [[0u8; HASH_SIZE]; MAX_MERKLE_DEPTH],
            depth: 0,
        };
        assert!(merkle_verify_path(leaf, leaf, 0, &path));
    }

    #[test]
    fn test_merkle_two_leaves() {
        let leaf0 = hash_field_elem(100);
        let leaf1 = hash_field_elem(200);
        let root = hash_two_to_one(leaf0, leaf1);

        let mut path0 = MerklePath {
            siblings: [[0u8; HASH_SIZE]; MAX_MERKLE_DEPTH],
            depth: 1,
        };
        path0.siblings[0] = leaf1;
        assert!(merkle_verify_path(root, leaf0, 0, &path0));

        let mut path1 = MerklePath {
            siblings: [[0u8; HASH_SIZE]; MAX_MERKLE_DEPTH],
            depth: 1,
        };
        path1.siblings[0] = leaf0;
        assert!(merkle_verify_path(root, leaf1, 1, &path1));
    }

    #[test]
    fn test_merkle_build_and_verify() {
        let num_leaves: usize = 8;
        let mut leaf_hashes: Vec<MerkleHash> = Vec::new();
        for i in 0..num_leaves {
            leaf_hashes.push(hash_field_elem(i as u64 + 1));
        }

        let root = merkle_build_root(&leaf_hashes, num_leaves);

        for idx in 0..num_leaves {
            let (root2, path) = merkle_build_and_prove(&leaf_hashes, num_leaves, idx);
            assert_eq!(root, root2);
            assert!(merkle_verify_path(root, leaf_hashes[idx], idx as u64, &path));
        }
    }

    #[test]
    fn test_merkle_wrong_leaf_fails() {
        let leaf0 = hash_field_elem(100);
        let leaf1 = hash_field_elem(200);
        let root = hash_two_to_one(leaf0, leaf1);

        let mut path = MerklePath {
            siblings: [[0u8; HASH_SIZE]; MAX_MERKLE_DEPTH],
            depth: 1,
        };
        path.siblings[0] = leaf1;

        let wrong_leaf = hash_field_elem(999);
        assert!(!merkle_verify_path(root, wrong_leaf, 0, &path));
    }
}
