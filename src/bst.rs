// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

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

pub trait Tree<K, T>
where
    K: Ord + Copy,
    T: Node<K>,
{
    fn insert(&mut self, key: K) -> Option<K>;
    fn remove(&mut self, key: &K) -> Option<K>;
    fn search(&self, key: &K) -> Option<&K>;
    fn successor(&self, key: &K) -> Option<&K>;
    fn predecessor(&self, key: &K) -> Option<&K>;
    fn minimum(&self) -> Option<&K>;
    fn maximum(&self) -> Option<&K>;
}

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

/// Constructs a binary search tree from slice and returns a tuple containing
/// a vector of tree nodes and the index of the root node.
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
/// use rtreap::bst::{TreeNode, Node, insert, swap_remove, build};
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
/// use rtreap::bst::{Node, TreeNode, NIL, transplant, build, swap_remove};
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

/// Removes the node located at `index` from the tree and returns its key.
/// Returns Err(Error) if `index` is out of bounds.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{TreeNode, Node, insert, NIL, remove, build};
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

/// Returns the next larger node after the node at `index` or `None` if one does not exist.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{TreeNode, Node, insert, NIL, successor, minimum, build};
///
/// let values: [usize; 9] = [5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
/// let mut i: usize = minimum(&nodes, root).unwrap();
/// while let Some(next) = successor(&nodes, i) {
///     assert!(*nodes[next].key() == *nodes[i].key() + 1);
///     i = next;
/// }
/// ```
pub fn successor<K, T>(nodes: &[T], mut index: usize) -> Option<usize>
where
    K: Ord + Copy,
    T: Node<K>,
{
    let len: usize = nodes.len();
    if index < len {
        let r: usize = nodes[index].right();
        if r < len {
            return minimum(nodes, r);
        } else {
            let mut p: usize = nodes[index].parent();
            while p < len {
                if index == nodes[p].left() {
                    return Some(p);
                } else {
                    index = p;
                    p = nodes[p].parent();
                }
            }
        }
    }
    None
}

/// Returns the previous smaller node before the node at `index` or `None` if one does not exist.
/// ///
/// ## Example:
///
/// ```
/// use rtreap::bst::{TreeNode, Node, insert, NIL, predecessor, maximum, build};
///
/// let values: [usize; 9] = [5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
/// let mut i: usize = maximum(&nodes, root).unwrap();
/// while let Some(next) = predecessor(&nodes, i) {
///     assert!(*nodes[next].key() == *nodes[i].key() - 1);
///     i = next;
/// }
/// ```
pub fn predecessor<K, T>(nodes: &[T], mut index: usize) -> Option<usize>
where
    K: Ord + Copy,
    T: Node<K>,
{
    let len: usize = nodes.len();
    if index < len {
        let l: usize = nodes[index].left();
        if l < len {
            return maximum(nodes, l);
        } else {
            let mut p: usize = nodes[index].parent();
            while p < len {
                if index == nodes[p].right() {
                    return Some(p);
                } else {
                    index = p;
                    p = nodes[p].parent();
                }
            }
        }
    }
    None
}

/// Returns the index of smallest value in the tree starting with the
/// node at `index` or `None` if the tree is empty.
///
/// ```
/// use rtreap::bst::{minimum, insert, Node, TreeNode, NIL, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// let i: usize = minimum(&nodes, root).unwrap();
/// assert!(*nodes[i].key() == 1, "Minimum returned {} instead of 1", i);
/// ```
pub fn minimum<K, T>(nodes: &[T], mut index: usize) -> Option<usize>
where
    K: Ord + Copy,
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

/// Returns the index of largest value in the tree starting with the
/// node at `index` or `None` if the tree is empty.
///
/// ```
/// use rtreap::bst::{maximum, insert, Node, TreeNode, NIL, build};
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
    K: Ord + Copy,
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

/// Inserts a node into the tree.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{minimum, maximum, insert, TreeNode, Node, NIL, build};
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

/// Searches a vector of nodes, sorted as a red-black tree, for `key` starting from `root`.
///
/// ## Example:
///
/// ```
/// use rtreap::bst::{search, insert, Node, TreeNode, NIL, build};
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
/// use rtreap::bst::{rotate_right, insert, Node, TreeNode, NIL, build};
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
/// use rtreap::bst::{rotate_left, insert, Node, TreeNode, NIL, build};
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

/// Performs an in order traversal on the tree, starting from the node at `index`
/// and calling `callback` as each node is visited.
///
/// ## Example
///
/// ```
/// use rtreap::bst::{in_order, insert, Node, TreeNode, NIL, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// let mut x: usize = 0;
/// let y: &mut usize = &mut x;
/// let mut v: Vec<usize> = Vec::new();
///
/// in_order(&nodes, root, |n| {
///     assert!(*n >= *y);
/// });
/// ```
pub fn in_order<K, F, T>(nodes: &[T], mut index: usize, callback: F)
where
    F: Fn(&K),
    T: Node<K>,
{
    let mut prev: usize = index;
    while index < nodes.len() {
        if nodes[index].right() != prev {
            if nodes[index].left() != prev {
                while nodes[index].left() != NIL {
                    index = nodes[index].left();
                }
            }
            callback(nodes[index].key());
            if nodes[index].right() != NIL {
                index = nodes[index].right();
                loop {
                    while nodes[index].left() != NIL {
                        index = nodes[index].left();
                    }
                    callback(nodes[index].key());
                    if nodes[index].right() != NIL {
                        index = nodes[index].right();
                    } else {
                        break;
                    }
                }
            }
        }
        prev = index;
        index = nodes[index].parent();
    }
}

/// Performs an in order traversal on the tree, starting from the node at `index`
/// and calling `callback` as each node is visited.
///
/// ## Example
///
/// ```
/// use rtreap::bst::{minimum, in_order_successor, insert, Node, TreeNode, NIL, build};
///
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let (mut nodes, mut root) = build::<usize, TreeNode<usize>>(&values);
///
/// let mut index: usize = minimum(&nodes, root).unwrap();
///
/// assert!(*nodes[index].key() == 1);
///
/// while let Some(n) = in_order_successor(&nodes, index) {
///     assert!(*nodes[n].key() >= *nodes[index].key());
///     index = n;
/// }
/// ```
pub fn in_order_successor<K, T>(nodes: &[T], index: usize) -> Option<usize>
where
    K: Ord + Copy,
    T: Node<K>,
{
    successor(nodes, index)
}

pub fn pre_order<K, F, T>(nodes: &[T], mut index: usize, callback: F)
where
    F: Fn(&K),
    T: Node<K>,
{
    let mut prev = index;
    while index != NIL {
        //go down the nodes
        if nodes[index].right() != prev {
            if nodes[index].left() != prev {
                callback(nodes[index].key());
                while nodes[index].left() != NIL {
                    index = nodes[index].left();
                    callback(nodes[index].key());
                }
            }
            if nodes[index].right() != NIL {
                index = nodes[index].right();
                callback(nodes[index].key());
                loop {
                    while nodes[index].left() != NIL {
                        index = nodes[index].left();
                        callback(nodes[index].key());
                    }
                    if nodes[index].right() != NIL {
                        index = nodes[index].right();
                        callback(nodes[index].key());
                    } else {
                        break;
                    }
                }
            }
        }
        //go up the nodes
        prev = index;
        index = nodes[index].parent();
    }
}

pub fn post_order<K, F, T>(nodes: &[T], mut index: usize, callback: F)
where
    F: Fn(&K),
    T: Node<K>,
{
    let mut prev = index;
    while index != NIL {
        if nodes[index].right() != prev {
            if nodes[index].left() != prev {
                while nodes[index].left() != NIL {
                    index = nodes[index].left()
                }
            }
            if nodes[index].right() != NIL {
                index = nodes[index].right();
                loop {
                    while nodes[index].left() != NIL {
                        index = nodes[index].left()
                    }
                    if nodes[index].right() != NIL {
                        index = nodes[index].right();
                    } else {
                        break;
                    }
                }
            }
        }
        callback(nodes[index].key());
        prev = index;
        index = nodes[index].parent();
    }
}
