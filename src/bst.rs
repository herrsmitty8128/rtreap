// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

/*!
 * The `bst` module is contains a trait
*/

use crate::error::{Error, ErrorKind, Result};
use std::cmp::Ordering;

/// Value used as a sentinel.
pub const NIL: usize = usize::MAX;

pub trait Node<K>
where
    Self: Sized,
{
    fn parent(&self) -> usize;
    fn left(&self) -> usize;
    fn right(&self) -> usize;
    fn set_parent(&mut self, p: usize);
    fn set_left(&mut self, l: usize);
    fn set_right(&mut self, r: usize);
    fn key(&self) -> &K;
}

/// An implementation of a general purpose binary tree node that implements the
/// `Node` trait and can be used with the functions contained in the `bst` module.
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

impl<K> Node<K> for TreeNode<K>
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

/// Constructs a binary search tree from a slice of objects that implement the
/// `Ord` and `Copy` traits and returns a tuple containing a vector of tree
/// nodes and the index of the root node.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{build, Node, TreeNode};
///
/// let values: [usize; 7] = [5, 7, 3, 4, 1, 9, 2];
/// let (nodes, root) = build::<usize, TreeNode<usize>>(&values);
/// assert!(nodes.len() == values.len(), "Number of nodes is incorrect.");
/// assert!(*nodes[root].key() == 5, "Root is {} instead of 4.", nodes[root].key());
/// ```
pub fn build<K, T>(s: &[K]) -> (Vec<T>, usize)
where
    K: Ord + Copy,
    T: Node<K> + From<K>,
{
    let mut nodes: Vec<T> = Vec::new();
    let mut root: usize = NIL;
    for i in s {
        insert(&mut nodes, &mut root, T::from(*i)).unwrap();
    }
    (nodes, root)
}

/// Removes the node located at `index` from the vector `nodes` and returns it.
/// The removed node is replaced by the last node in the vector.
/// It does not remove the node from the tree.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{TreeNode, Node, swap_remove, build};
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
pub fn swap_remove<K, T>(nodes: &mut Vec<T>, root: &mut usize, index: usize) -> Result<T>
where
    T: Node<K>,
{
    let treap_size: usize = nodes.len();
    if index < treap_size {
        let n: usize = treap_size - 1; // get the index of the last node
        if n != index {
            let p: usize = nodes[n].parent();
            let l: usize = nodes[n].left();
            let r: usize = nodes[n].right();
            if p < treap_size {
                if nodes[p].left() == n {
                    nodes[p].set_left(index);
                } else {
                    nodes[p].set_right(index);
                }
            }
            if l < treap_size {
                nodes[l].set_parent(index);
            }
            if r < treap_size {
                nodes[r].set_parent(index);
            }
            if n == *root {
                *root = index;
            }
        }
        Ok(nodes.swap_remove(index))
    } else {
        Err(Error::new(
            ErrorKind::IndexOutOfBounds,
            "Cannot delete a node that does not exist.",
        ))
    }
}

/// Removes the node at index `dst` from the tree by replacing it with node at index `src`.
/// It does not remove the node from the vector `nodes`.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{Node, TreeNode, transplant, build, swap_remove};
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
    T: Node<K>,
{
    let len: usize = nodes.len();
    if dst < len {
        let p: usize = nodes[dst].parent();
        if p < len {
            if dst == nodes[p].left() {
                nodes[p].set_left(src);
            } else {
                nodes[p].set_right(src);
            }
        } else {
            *root = src;
        }
        if src < len {
            nodes[src].set_parent(p);
        }
    }
}

/// Removes the node located at `index` from the tree and the vector `nodes`
/// and returns its key. Returns Err(Error) if `index` is out of bounds.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{TreeNode, Node, NIL, remove, build};
///
/// let values: [usize; 9] = [5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// for i in (0..nodes.len()).rev() {
///     assert!(root != NIL);
///     assert!(!nodes.is_empty());
///     remove(&mut nodes, &mut root, i).unwrap();
/// }
///
/// assert!(nodes.is_empty(), "Failed to remove all nodes.");
/// assert!(root == NIL, "root is not NIL.");
/// ```
pub fn remove<K, T>(nodes: &mut Vec<T>, root: &mut usize, index: usize) -> Result<T>
where
    K: Ord + Copy,
    T: Node<K>,
{
    let len: usize = nodes.len();
    if index < len {
        let r: usize = nodes[index].right();
        let l: usize = nodes[index].left();
        if l >= len {
            transplant(nodes, root, index, r);
        } else if r >= len {
            transplant(nodes, root, index, l);
        } else {
            let y: usize = minimum(nodes, r).unwrap(); // should never panic
            if y != r {
                let yr = nodes[y].right();
                transplant(nodes, root, y, yr);
                nodes[y].set_right(r);
                nodes[r].set_parent(y);
            }
            transplant(nodes, root, index, y);
            nodes[y].set_left(l);
            nodes[l].set_parent(y);
        }
        swap_remove(nodes, root, index)
    } else {
        Err(Error::new(
            ErrorKind::IndexOutOfBounds,
            "Cannot delete a node that does not exist.",
        ))
    }
}

/// Returns the index of the node with the smallest value in the tree starting with the
/// node at `index` or `None` if the tree is empty.
///
/// ```
/// use rtreap::bst::{minimum, Node, TreeNode, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// let i: usize = minimum(&nodes, root).unwrap();
/// assert!(*nodes[i].key() == 1, "Minimum returned {} instead of 1", i);
/// ```
pub fn minimum<K, T>(nodes: &[T], mut index: usize) -> Option<usize>
where
    K: Ord,
    T: Node<K>,
{
    let num_nodes: usize = nodes.len();
    while index < num_nodes {
        let left: usize = nodes[index].left();
        if left < num_nodes {
            index = left;
        } else {
            return Some(index);
        }
    }
    None
}

/// Returns the index of the node with the largest value in the tree starting with the
/// node at `index` or `None` if the tree is empty.
///
/// ```
/// use rtreap::bst::{maximum, Node, TreeNode, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// if let Some(i) = maximum(&nodes, root) {
///     assert!(*nodes[i].key() == 9, "Maximum returned {} instead of 9", i);
/// } else {
///     panic!("Maximum returned None.");
/// }
/// ```
pub fn maximum<K, T>(nodes: &[T], mut index: usize) -> Option<usize>
where
    K: Ord,
    T: Node<K>,
{
    let num_nodes: usize = nodes.len();
    while index < num_nodes {
        let right: usize = nodes[index].right();
        if right < num_nodes {
            index = right;
        } else {
            return Some(index);
        }
    }
    None
}

/// Inserts `node` into the tree and returns `Some(usize)` containing the index of the inserted node.
/// If the key of the new node already exists in the tree, then it will return `Err(usize)` containing
/// the index of the already existing node with the same key without replacing it.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{minimum, maximum, TreeNode, Node, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// assert!(values.len() == nodes.len(), "The tree does not contain the correct number of nodes.");
///
/// assert!(*nodes[root].key() == 5, "Invalid tree root node");
///
/// let i = minimum(&nodes, root).unwrap();
/// assert!(*nodes[i].key() == 1, "Minimum value is {} instead of 1", nodes[i].key());
///
/// let i = maximum(&nodes, root).unwrap();
/// assert!(*nodes[i].key() == 9, "Maximum value is {} instead of 9", nodes[i].key());
/// ```
pub fn insert<K, T>(
    nodes: &mut Vec<T>,
    root: &mut usize,
    node: T,
) -> std::result::Result<usize, usize>
where
    K: Ord + Copy,
    T: Node<K>,
{
    let new_node: usize = nodes.len();
    if new_node == 0 {
        nodes.push(node);
        *root = new_node;
    } else {
        let mut n: usize = *root;
        let key: &K = node.key();
        loop {
            match key.cmp(nodes[n].key()) {
                Ordering::Greater => {
                    if nodes[n].right() < new_node {
                        n = nodes[n].right();
                    } else {
                        nodes.push(node);
                        nodes[n].set_right(new_node);
                        nodes[new_node].set_parent(n);
                        break;
                    }
                }
                Ordering::Less => {
                    if nodes[n].left() < new_node {
                        n = nodes[n].left();
                    } else {
                        nodes.push(node);
                        nodes[n].set_left(new_node);
                        nodes[new_node].set_parent(n);
                        break;
                    }
                }
                Ordering::Equal => {
                    return Err(n);
                }
            }
        }
    }
    Ok(new_node)
}

/// Searches a vector of nodes for `key` starting from `root`.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{search, Node, TreeNode, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// assert!(*nodes[root].key() == 5, "Invalid root");
///
/// let search_result = search(&nodes, root, &4).unwrap();
/// assert!(4 == *nodes[search_result].key(), "Search returned {} instead of 4.", search_result);
/// ```
pub fn search<K, T>(nodes: &[T], mut root: usize, key: &K) -> Option<usize>
where
    K: Ord,
    T: Node<K>,
{
    while root < nodes.len() {
        match key.cmp(nodes[root].key()) {
            Ordering::Equal => return Some(root),
            Ordering::Less => root = nodes[root].left(),
            Ordering::Greater => root = nodes[root].right(),
        };
    }
    None
}

/// Rotates the node at `index` to the right.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{rotate_right, Node, TreeNode, build};
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
pub fn rotate_right<K, T>(nodes: &mut [T], root: &mut usize, index: usize)
where
    T: Node<K>,
{
    let len: usize = nodes.len();
    if index < len {
        let l: usize = nodes[index].left();
        if l < len {
            let p: usize = nodes[index].parent();
            nodes[l].set_parent(p);
            if p < len {
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
            if r < len {
                nodes[r].set_parent(index);
            }
            nodes[l].set_right(index);
        }
    }
}

/// Rotates the node at `index` to the left.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{rotate_left, Node, TreeNode, build};
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
pub fn rotate_left<K, T>(nodes: &mut [T], root: &mut usize, index: usize)
where
    T: Node<K>,
{
    let len: usize = nodes.len();
    if index < len {
        let r: usize = nodes[index].right();
        if r < len {
            let p: usize = nodes[index].parent();
            nodes[r].set_parent(p);
            if p < len {
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
            if l < len {
                nodes[l].set_parent(index);
            }
            nodes[r].set_left(index);
        }
    }
}

/// Returns the index of the next node in a pre-order traversal or `None` if there isn't one.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{pre_order_next, Node, TreeNode, build};
/// use rand::prelude::*;
///
/// // funcion used to recursively traverse a binary search tree (for testing only)
/// pub fn pre_order_recursive<K, T>(v: &mut Vec<usize>, nodes: &[T], index: usize)
/// where
///     K: Ord,
///     T: Node<K>,
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
    T: Node<K>,
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
/// use rtreap::bst::{post_order_next, Node, TreeNode, build, NIL};
/// use rand::prelude::*;
///
/// // funcion used to recursively traverse a binary search tree (for testing only)
/// pub fn post_order_recursive<K, T>(v: &mut Vec<usize>, nodes: &[T], index: usize)
/// where
///     K: Ord,
///     T: Node<K>,
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
    T: Node<K>,
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
/// use rtreap::bst::{TreeNode, Node, in_order_next, minimum, build};
/// use rand::prelude::*;
///
/// // build a binary search tree from an array of random numbers
/// let mut values: [usize; 100] = [0; 100];
/// rand::thread_rng().fill(&mut values[..]);
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// // get the first node in the traversal by calling minimum()
/// let mut prev: usize = minimum(&nodes, root).unwrap();
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
    T: Node<K>,
{
    let len: usize = nodes.len();
    if prev < len {
        let r: usize = nodes[prev].right();
        if r < len {
            return minimum(nodes, r);
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
/// use rtreap::bst::{TreeNode, Node, in_order_prev, maximum, build};
/// use rand::prelude::*;
///
/// // build a binary search tree from an array of random numbers
/// let mut values: [usize; 100] = [0; 100];
/// rand::thread_rng().fill(&mut values[..]);
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// // get the first node in the traversal by calling maximum()
/// let mut prev: usize = maximum(&nodes, root).unwrap();
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
    T: Node<K>,
{
    let len: usize = nodes.len();
    if prev < len {
        let l: usize = nodes[prev].left();
        if l < len {
            return maximum(nodes, l);
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
