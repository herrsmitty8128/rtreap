// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

/*!
 * This module contains a `Node` trait and a collection of functions designed to
 * perform operations on a binary search tree ("bst").
 *
 * Supported operations include:
 *
 * - build (construct a new bst from a slice of keys)
 * - insert
 * - remove
 * - search
 * - minimum
 * - maximum
 * - traversal (pre, post, and in-order)
 * - rotation (left and right)
 * - transplant (replace a node with another node in the tree)
 *
 * Binary search trees are rarely used in most applications. Instead, the operations
 * on a bst often form the basis for operations on other types of binary trees, such
 * as a red-black tree or a treap. Therefore, this module only contains the traits,
 * structs, and functions necessary to operate on a bst, but does not contain an
 * implementation of a bst struct.
 *
 * Memory allocations are designed to use a linear model, where nodes are stored
 * consecutively in an array or vector, rather than allocating memory for each
 * node separately on the heap. This has the advantage of reducing the number of
 * allocations at a cost of possibly using more memory.
 *
 * Instead of pointers or references, usize indexes are used to indicate the location
 * of a node in the array/vector. Therefore, nodes contain the usize index of both
 * children and parent nodes. An invalid index (that is out of bounds) is treated as
 * a sentinal/terminal value by all functions. The [NIL] constant is provided in this
 * module as a convenient way to help manage this. Keep in mind that you are responsible
 * for keeping track of the index of the root node in the tree.
 *
 * Since binary search trees are not self-balancing, all functions are iterative to
 * avoid the risk of stack overflow that can sometimes occur with recursive functions
 * on unbalanced trees.
*/

use std::cmp::Ordering;

/// Value used as a sentinel.
pub const NIL: usize = usize::MAX;

/// Trait designed to model the node in a binary tree.
pub trait BinaryNode<K>
where
    Self: Sized,
{
    /// Returns the index of the parent node.
    fn parent(&self) -> usize;

    /// Returns the index of the left child node.
    fn left(&self) -> usize;

    /// Returns the index of the right child node.
    fn right(&self) -> usize;

    /// Sets the index of the parent node.
    fn set_parent(&mut self, p: usize);

    /// Sets the index of the left child node.
    fn set_left(&mut self, l: usize);

    /// Sets the index of the right child node.
    fn set_right(&mut self, r: usize);

    /// Returns `true` if the node is a leaf node.
    fn is_leaf(&self) -> bool {
        self.left() == NIL && self.right() == NIL
    }

    /// Returns an immutable reference to the node's key.
    fn key(&self) -> &K;
}

/// A general purpose binary tree node that implements the `Node` trait
/// and can be used with the functions contained in the `bst` module.
#[derive(Debug, Clone, Copy)]
pub struct TreeNode<K>
where
    Self: Sized,
{
    parent: usize,
    left: usize,
    right: usize,
    key: K,
}

impl<K> From<K> for TreeNode<K>
where
    K: Ord,
{
    fn from(key: K) -> Self {
        Self {
            parent: NIL,
            left: NIL,
            right: NIL,
            key,
        }
    }
}

impl<K> BinaryNode<K> for TreeNode<K>
where
    K: Ord,
{
    fn key(&self) -> &K {
        &self.key
    }

    fn left(&self) -> usize {
        self.left
    }

    fn parent(&self) -> usize {
        self.parent
    }

    fn right(&self) -> usize {
        self.right
    }

    fn set_left(&mut self, l: usize) {
        self.left = l;
    }

    fn set_parent(&mut self, p: usize) {
        self.parent = p;
    }

    fn set_right(&mut self, r: usize) {
        self.right = r;
    }
}

/*  Constructs a binary search tree from a slice of objects that implement the
/// `Ord` and `Copy` traits and returns a tuple containing a vector of tree
/// nodes and the index of the root node.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{build, BinaryNode, TreeNode};
///
/// let values: [usize; 7] = [5, 7, 3, 4, 1, 9, 2];
/// let (nodes, root) = build::<usize, TreeNode<usize>>(&values);
/// assert!(nodes.len() == values.len(), "Number of nodes is incorrect.");
/// assert!(*nodes[root].key() == 5, "Root is {} instead of 5.", nodes[root].key());
/// ```
pub fn build<K, T>(s: &[K]) -> (Vec<T>, usize)
where
    K: Ord + Copy,
    T: BinaryNode<K> + From<K>,
{
    let mut nodes: Vec<T> = Vec::new();
    let mut root: usize = NIL;
    for i in s {
        insert(&mut nodes, &mut root, T::from(*i)).unwrap();
    }
    (nodes, root)
}*/

/*
/// Removes the node located at `index` from the vector `nodes` and returns it.
/// The removed node is replaced by the last node in the vector.
/// It does not remove the node from the tree.
///
/// ## Panics:
///
/// Panics if `root` or `index` are out of bounds.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{TreeNode, BinaryNode, swap_remove, build};
///
/// let values: [usize; 9] = [5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// let index: usize = 3;
/// let last: usize = nodes.len() - 1;
/// let node: TreeNode<usize> = nodes[last];
///
/// let is_left_child = if node.parent() < nodes.len() {
///     if nodes[node.parent()].right() == last {
///         false
///     } else if nodes[node.parent()].left() == last {
///         true
///     } else {
///         panic!("Node at index is not a child of its parent.")
///     }
/// } else {
///     panic!("Node at index has not parent. Pick a different node to test.")
/// };
///
/// swap_remove(&mut nodes, &mut root, index);
///
/// assert!(node.key() == nodes[index].key(), "Keys are not the same.");
/// assert!(node.parent() == nodes[index].parent(), "Parent is not the same.");
/// assert!(node.left() == nodes[index].left(), "Left child not the same.");
/// assert!(node.right() == nodes[index].right(), "Right child not the same.");
///
/// if is_left_child {
///     assert!(nodes[node.parent()].left() == index, "Parent node points to the wrong child.");
/// } else {
///     assert!(nodes[node.parent()].right() == index, "Parent node points to the wrong child.");
/// }
///
/// ```
pub fn swap_remove<K, N>(nodes: &mut Vec<N>, root: &mut usize, index: usize) -> N
where
    N: BinaryNode<K>,
{
    let len: usize = nodes.len();
    let n: usize = len - 1; // get the index of the last node
    if n != index {
        let p: usize = nodes[n].parent();
        let l: usize = nodes[n].left();
        let r: usize = nodes[n].right();
        if p < len {
            if nodes[p].left() == n {
                nodes[p].set_left(index);
            } else {
                nodes[p].set_right(index);
            }
        }
        if l < len {
            nodes[l].set_parent(index);
        }
        if r < len {
            nodes[r].set_parent(index);
        }
        if n == *root {
            *root = index;
        }
    }
    nodes.swap_remove(index)
}

/// Copies all the nodes from `src` and appends them to `dst` while updating their parent and child indices.
/// Returns the updated root index in the `dst` vector.
pub fn extend<K, N>(dst: &mut Vec<N>, src: &[N], src_root: usize) -> usize
where
    K: Ord + Copy,
    N: BinaryNode<K> + Default + Copy,
{
    let offset: usize = dst.len();
    let m: usize = src.len();
    let mut n: usize = offset;

    for node in src.iter() {
        dst.push(*node);

        let mut i = dst[n].parent();
        dst[n].set_parent(if i != NIL { i + offset } else { NIL });

        i = dst[n].left();
        dst[n].set_left(if i != NIL { i + offset } else { NIL });

        i = dst[n].right();
        dst[n].set_right(if i != NIL { i + offset } else { NIL });

        n += 1;
    }

    if src_root < m {
        src_root + offset
    } else {
        NIL
    }
}

*/

/// Removes the node at index `dst` from the tree by replacing it with node at index `src`.
/// It does not remove the node from the vector `nodes`.
///
/// ## Panics:
///
/// Panics if `root` or `dst` are out of bounds.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{BinaryNode, TreeNode, transplant, build, swap_remove};
///
/// let values: [usize; 9] = [5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// // remove node at index 2 from the tree and replace it with the node at index 5
/// transplant(&mut nodes, &mut root, 2, 5);
///
/// assert!(nodes[2].parent() == nodes[5].parent());
/// assert!(nodes[nodes[5].parent()].left() == 5);
///
/// // remove the node at index 2 from the vector
/// swap_remove(&mut nodes, &mut root, 2);
/// ```
pub fn transplant<K, T>(nodes: &mut [T], root: &mut usize, dst: usize, src: usize)
where
    K: Ord + Copy,
    T: BinaryNode<K>,
{
    let p: usize = nodes[dst].parent();
    if p == NIL {
        *root = src;
    } else if dst == nodes[p].left() {
        nodes[p].set_left(src);
    } else {
        nodes[p].set_right(src);
    }
    if src != NIL {
        nodes[src].set_parent(p);
    }
}

/// Removes the node located at `index` from the tree but not the vector `nodes`
/// and returns the index of the node that replaced it in the tree. Returns `None`
/// if the node was not replaced by another node becuase it was a leaf.
///
/// ## Panics:
///
/// Panics if `root` or `index` are out of bounds.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{TreeNode, BinaryNode, NIL, remove, insert, is_valid, swap_remove};
/// use rand::prelude::*;
///
/// let mut nodes: Vec<TreeNode<usize>> = Vec::new();
/// let mut root: usize = NIL;
///
/// for index in 0..1000 {
///     let node = TreeNode::from(rand::random::<usize>());
///     nodes.push(node);
///     insert(&mut nodes, &mut root, index);
/// }
///
/// for index in (0..nodes.len()).rev() {
///     assert!(root != NIL);
///     assert!(!nodes.is_empty());
///     assert!(is_valid(&nodes, root), "Tree is not valid");
///     let beg_len: usize = nodes.len();
///     //let index = rand::thread_rng().gen_range(0..nodes.len());
///     assert!(index != NIL);
///     assert!(root != NIL);
///     remove(&mut nodes, &mut root, index);
///     assert!(beg_len - nodes.len() == 1);
/// }
///
/// assert!(nodes.is_empty(), "Failed to remove all nodes.");
/// assert!(root == NIL, "root is not NIL.");
/// ```
pub fn remove<K, N>(nodes: &mut [N], root: &mut usize, index: usize) -> Option<usize>
where
    K: Ord + Copy,
    N: BinaryNode<K>,
{
    let r: usize = nodes[index].right();
    let l: usize = nodes[index].left();
    if l == NIL && r == NIL {
        // leaf node
        transplant(nodes, root, index, NIL);
        None
    } else if l == NIL && r != NIL {
        // only the right child exists
        transplant(nodes, root, index, r);
        Some(r)
    } else if l != NIL && r == NIL {
        // only the left child exists
        transplant(nodes, root, index, l);
        Some(l)
    } else {
        // both children exist
        let y: usize = minimum(nodes, r);
        if y != r {
            let yr = nodes[y].right();
            transplant(nodes, root, y, yr);
            nodes[y].set_right(r);
            nodes[r].set_parent(y);
        }
        transplant(nodes, root, index, y);
        nodes[y].set_left(l);
        nodes[l].set_parent(y);
        Some(y)
    }
}

/*
/// Removes the node at `index` from both the tree and the vector.
///
/// ## Panics:
///
/// Panics if `index` is out of bounds.
pub fn remove<K, N>(nodes: &mut Vec<N>, root: &mut usize, index: usize) -> N
where
    K: Ord + Copy,
    N: BinaryNode<K>,
{
    tree_remove(nodes, root, index);
    swap_remove(nodes, root, index)
}
*/

/// Returns the index of the node with the smallest key in the tree starting with the
/// node at `index` or `None` if the tree is empty.
///
/// ## Panics:
///
/// Panics if `index` is out of bounds.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{minimum, BinaryNode, TreeNode, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// let i: usize = minimum(&nodes, root);
///
/// assert!(*nodes[i].key() == 1, "Minimum returned {} instead of 1", i);
/// ```
pub fn minimum<K, T>(nodes: &[T], mut index: usize) -> usize
where
    K: Ord,
    T: BinaryNode<K>,
{
    loop {
        let left: usize = nodes[index].left();
        if left == NIL {
            return index;
        } else {
            index = left;
        }
    }
}

/// Returns the index of the node with the largest key in the tree starting with the
/// node at `index` or `None` if the tree is empty.
///
/// ```
/// use rtreap::bst::{maximum, BinaryNode, TreeNode, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// let i = maximum(&nodes, root);
///
/// assert!(*nodes[i].key() == 9, "Maximum returned {} instead of 9", i);
/// ```
pub fn maximum<K, T>(nodes: &[T], mut index: usize) -> usize
where
    K: Ord,
    T: BinaryNode<K>,
{
    loop {
        let right: usize = nodes[index].right();
        if right == NIL {
            return index;
        } else {
            index = right;
        }
    }
}

/// Inserts the node at `index` into the tree. Returns `Ok(())` if the key did not previously exist in the tree.
/// If the key of the new node already exists in the tree, then it will return `Err(usize)` containing
/// the index of the already existing node with the same key without replacing it.
///
/// ## Panics:
///
/// Panics if `root` or `index` are out of bounds.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{minimum, maximum, TreeNode, BinaryNode, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// assert!(values.len() == nodes.len(), "The tree does not contain the correct number of nodes.");
///
/// assert!(*nodes[root].key() == 5, "Invalid tree root node");
///
/// let i = minimum(&nodes, root);
/// assert!(*nodes[i].key() == 1, "Minimum value is {} instead of 1", nodes[i].key());
///
/// let i = maximum(&nodes, root);
/// assert!(*nodes[i].key() == 9, "Maximum value is {} instead of 9", nodes[i].key());
/// ```
pub fn insert<K, N>(nodes: &mut [N], root: &mut usize, index: usize) -> Result<(), usize>
where
    K: Ord + Copy,
    N: BinaryNode<K>,
{
    if *root == NIL {
        *root = index;
        nodes[index].set_parent(NIL);
    } else {
        let (p, order) = search(nodes, *root, nodes[index].key());
        match order {
            Ordering::Equal => return Err(p),
            Ordering::Greater => nodes[p].set_right(index),
            Ordering::Less => nodes[p].set_left(index),
        }
        nodes[index].set_parent(p);
    }
    nodes[index].set_left(NIL);
    nodes[index].set_right(NIL);
    Ok(())
}

/// Searches for the nodes containing `key` starting from `root`.
/// Returns `Ok(usize)` containing the index of the node containing the key.
/// Returns `Err(usize, bool) containing the index of the parent node and a bool value indicating
/// whether the child is a left (true) or right (false) child.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{search, BinaryNode, TreeNode, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// assert!(*nodes[root].key() == 5, "Invalid root");
///
/// let search_result = search(&nodes, root, &4).unwrap();
/// assert!(4 == *nodes[search_result].key(), "Search returned {} instead of 4.", search_result);
/// ```
pub fn search<K, N>(nodes: &[N], mut root: usize, key: &K) -> (usize, Ordering)
//Option<usize>
where
    K: Ord,
    N: BinaryNode<K>,
{
    loop {
        match key.cmp(nodes[root].key()) {
            Ordering::Equal => return (root, Ordering::Equal),
            Ordering::Less => {
                let left: usize = nodes[root].left();
                if left == NIL {
                    return (root, Ordering::Less);
                }
                root = left;
            }
            Ordering::Greater => {
                let right: usize = nodes[root].right();
                if right == NIL {
                    return (root, Ordering::Greater);
                }
                root = right;
            }
        };
    }
}

/// Rotates the node at `index` to the right.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{rotate_right, BinaryNode, TreeNode, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// let node1: usize = 3;
/// let node2: usize = nodes[node1].left();
///
/// assert!(node2 < nodes.len());
///
/// rotate_right(&mut nodes, &mut root, node1);
///
/// assert!(nodes[node2].right() == node1);
/// ```
pub fn rotate_right<K, N>(nodes: &mut [N], root: &mut usize, index: usize)
where
    N: BinaryNode<K>,
{
    //let len: usize = nodes.len();
    //if index < len {
    let l: usize = nodes[index].left();
    //if l < len {
    if l != NIL {
        let p: usize = nodes[index].parent();
        nodes[l].set_parent(p);
        //if p < len {
        if p != NIL {
            if index == nodes[p].left() {
                nodes[p].set_left(l);
            } else {
                nodes[p].set_right(l);
            }
        } else {
            *root = l;
        }
        nodes[index].set_parent(l);
        let r: usize = nodes[l].right();
        nodes[index].set_left(r);
        //if r < len {
        if r != NIL {
            nodes[r].set_parent(index);
        }
        nodes[l].set_right(index);
    }
    //}
}

/// Rotates the node at `index` to the left.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{rotate_left, BinaryNode, TreeNode, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// let node1: usize = 4;
/// let node2: usize = nodes[node1].right();
///
/// assert!(node2 < nodes.len());
///
/// rotate_left(&mut nodes, &mut root, node1);
///
/// assert!(nodes[node2].left() == node1);
/// ```
pub fn rotate_left<K, N>(nodes: &mut [N], root: &mut usize, index: usize)
where
    N: BinaryNode<K>,
{
    //let len: usize = nodes.len();
    //if index < len {
    let r: usize = nodes[index].right();
    //if r < len {
    if r != NIL {
        let p: usize = nodes[index].parent();
        nodes[r].set_parent(p);
        //if p < len {
        if p != NIL {
            if index == nodes[p].left() {
                nodes[p].set_left(r);
            } else {
                nodes[p].set_right(r);
            }
        } else {
            *root = r;
        }
        nodes[index].set_parent(r);
        let l: usize = nodes[r].left();
        nodes[index].set_right(l);
        //if l < len {
        if l != NIL {
            nodes[l].set_parent(index);
        }
        nodes[r].set_left(index);
    }
    //}
}

/// Returns the index of the next node in a pre-order traversal or `None` if there isn't one.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{pre_order_next, BinaryNode, TreeNode, build};
/// use rand::prelude::*;
///
/// // funcion used to recursively traverse a binary search tree (for testing only)
/// pub fn pre_order_recursive<K, T>(v: &mut Vec<usize>, nodes: &[T], index: usize)
/// where
///     K: Ord,
///     T: BinaryNode<K>,
/// {
///     if index < nodes.len() {
///         v.push(index);
///         pre_order_recursive(v, nodes, nodes[index].left());
///         pre_order_recursive(v, nodes, nodes[index].right());
///     }
/// }
///
/// // build a binary search tree from an array of random numbers
/// let mut values: [usize; 100] = [0; 100];
/// rand::thread_rng().fill(&mut values[..]);
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// // create two new vectors to hold the result of each traversal
/// let mut v1: Vec<usize> = Vec::new();
/// let mut v2: Vec<usize> = Vec::new();
///
/// // recursively traverse all nodes in the tree and append each index to v1
/// pre_order_recursive(&mut v1, &nodes, root);
///
/// // in a pre-order traversal, each node is visited before its children.
/// // therefore, the root node is visited first. So we get the root node,
/// // do something with it (here, we append it to v2), then pass it to
/// // pre_order_next()
/// let mut prev = root;
/// v2.push(prev);
///
/// // iteratively traverse all the nodes in the tree and append each index to v2
/// while let Some(next) = pre_order_next(&nodes, prev) {
///     v2.push(next);
///     prev = next;
/// }
///
/// // verify that both methods (recursive and iterative) had the same result
/// assert!(v1 == v2);
/// ```
pub fn pre_order_next<K, T>(nodes: &[T], mut prev: usize) -> Option<usize>
where
    K: Ord,
    T: BinaryNode<K>,
{
    let len: usize = nodes.len();
    if prev < len {
        if nodes[prev].left() < len {
            return Some(nodes[prev].left());
        }
        if nodes[prev].right() < len {
            return Some(nodes[prev].right());
        }
        while nodes[prev].parent() < len {
            let p: usize = nodes[prev].parent();
            if prev == nodes[p].left() && nodes[p].right() < len {
                return Some(nodes[p].right());
            }
            prev = p;
        }
    }
    None
}

/// Returns the index of the next node in a post-order traversal or `None` if there isn't one.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{post_order_next, BinaryNode, TreeNode, build, NIL};
/// use rand::prelude::*;
///
/// // funcion used to recursively traverse a binary search tree (for testing only)
/// pub fn post_order_recursive<K, T>(v: &mut Vec<usize>, nodes: &[T], index: usize)
/// where
///     K: Ord,
///     T: BinaryNode<K>,
/// {
///     if index < nodes.len() {
///         post_order_recursive(v, nodes, nodes[index].left());
///         post_order_recursive(v, nodes, nodes[index].right());
///         v.push(index);
///     }
/// }
///
/// // build a binary search tree from an array of random numbers
/// let mut values: [usize; 100] = [0; 100];
/// rand::thread_rng().fill(&mut values[..]);
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// // create two new vectors to hold the result of each traversal
/// let mut v1: Vec<usize> = Vec::new();
/// let mut v2: Vec<usize> = Vec::new();
///
/// // recursively traverse all nodes in the tree and append each index to v1
/// post_order_recursive(&mut v1, &nodes, root);
///
/// // in a post-order traversal, each node is visited after its children
/// // have been visited. Therefore, there is no previous node when starting
/// // a traversal. So we set it to NIL.
/// let mut prev: usize = NIL;
///
/// // iteratively traverse all the nodes in the tree and append each index to v2
/// while let Some(next) = post_order_next(&nodes, root, prev) {
///     v2.push(next);
///     prev = next;
/// }
///
/// // verify that both methods (recursive and iterative) had the same result
/// assert!(v1 == v2);
/// ```
pub fn post_order_next<K, T>(nodes: &[T], root: usize, mut prev: usize) -> Option<usize>
where
    K: Ord,
    T: BinaryNode<K>,
{
    if prev != root {
        let len: usize = nodes.len();
        if prev >= len {
            prev = root;
        }
        let p: usize = nodes[prev].parent();
        if p < len {
            if prev == nodes[p].left() && nodes[p].right() < len {
                prev = nodes[p].right();
            } else {
                return Some(p);
            }
        }
        // descend the tree to the next leaf node
        loop {
            if nodes[prev].left() < len {
                prev = nodes[prev].left();
            } else if nodes[prev].right() < len {
                prev = nodes[prev].right();
            } else {
                return Some(prev);
            }
        }
    }
    None
}

/// Returns the index of the next node in a pre-order traversal or `None` if one does not exist.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{TreeNode, BinaryNode, in_order_next, minimum, build};
/// use rand::prelude::*;
///
/// // build a binary search tree from an array of random numbers
/// let mut values: [usize; 100] = [0; 100];
/// rand::thread_rng().fill(&mut values[..]);
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// // get the first node in the traversal by calling minimum()
/// let mut prev: usize = minimum(&nodes, root);
///
/// // do something with prev here...
///
/// // traverse the rest of the nodes in the tree
/// while let Some(next) = in_order_next(&nodes, prev) {
///     assert!(*nodes[next].key() > *nodes[prev].key());
///     prev = next;
/// }
/// ```
pub fn in_order_next<K, T>(nodes: &[T], mut prev: usize) -> Option<usize>
where
    K: Ord,
    T: BinaryNode<K>,
{
    let len: usize = nodes.len();
    if prev < len {
        let r: usize = nodes[prev].right();
        if r < len {
            return Some(minimum(nodes, r));
        } else {
            let mut p: usize = nodes[prev].parent();
            while p < len {
                if prev == nodes[p].left() {
                    return Some(p);
                } else {
                    prev = p;
                    p = nodes[p].parent();
                }
            }
        }
    }
    None
}

/// Returns the index of the previous node in a pre-order traversal or `None` if one does not exist.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{TreeNode, BinaryNode, in_order_prev, maximum, build};
/// use rand::prelude::*;
///
/// // build a binary search tree from an array of random numbers
/// let mut values: [usize; 100] = [0; 100];
/// rand::thread_rng().fill(&mut values[..]);
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// // get the first node in the traversal by calling maximum()
/// let mut prev: usize = maximum(&nodes, root);
///
/// // do something with prev here...
///
/// // traverse the rest of the nodes in the tree
/// while let Some(next) = in_order_prev(&nodes, prev) {
///     assert!(*nodes[next].key() <= *nodes[prev].key());
///     prev = next;
/// }
/// ```
pub fn in_order_prev<K, T>(nodes: &[T], mut prev: usize) -> Option<usize>
where
    K: Ord,
    T: BinaryNode<K>,
{
    let len: usize = nodes.len();
    if prev < len {
        let l: usize = nodes[prev].left();
        if l < len {
            return Some(maximum(nodes, l));
        } else {
            let mut p: usize = nodes[prev].parent();
            while p < len {
                if prev == nodes[p].right() {
                    return Some(p);
                } else {
                    prev = p;
                    p = nodes[p].parent();
                }
            }
        }
    }
    None
}

/// Returns true if the properties of a binary tree hold true.
/// This function is primarily used for testing.
///
/// ## Panics:
///
/// Panics if `root` is out of bounds.
#[doc(hidden)]
pub fn is_valid<K, T>(nodes: &[T], root: usize) -> bool
where
    K: Ord,
    T: BinaryNode<K>,
{
    let mut prev: usize = minimum(nodes, root);
    while let Some(next) = in_order_next(nodes, prev) {
        if *nodes[prev].key() > *nodes[next].key() {
            return false;
        };
        prev = next;
    }
    true
}
