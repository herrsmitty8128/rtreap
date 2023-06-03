// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

use crate::error::{Error, ErrorKind, Result};
use std::cmp::Ordering;

/// Value used as a sentinel.
pub const NIL: usize = usize::MAX;

pub trait TreeNode<K>
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

#[derive(Debug, Clone, Copy)]
pub struct Node<E>
where
    Self: Sized,
{
    parent: usize,
    left: usize,
    right: usize,
    key: E,
}

impl<K> From<K> for Node<K>
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

impl<K> TreeNode<K> for Node<K>
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

pub fn build<K, T>(s: &[K]) -> (Vec<T>, usize)
where
    K: Ord + Copy,
    T: TreeNode<K> + From<K>,
{
    let mut nodes: Vec<T> = Vec::new();
    let mut root: usize = NIL;
    for i in s {
        insert(&mut nodes, &mut root, T::from(*i)).unwrap();
    }
    (nodes, root)
}

pub fn swap_remove<K, T>(nodes: &mut Vec<T>, root: &mut usize, index: usize) -> Result<T>
where
    T: TreeNode<K>,
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

/// Removes the nodes at index `dst` from the tree by replacing it with node at index `src`.
pub fn transplant<K, T>(nodes: &mut Vec<T>, root: &mut usize, dst: usize, src: usize)
where
    K: Ord + Copy,
    T: TreeNode<K>,
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
/// use rtreap::bst::{TreeNode, Node, insert, NIL, delete};
///
/// let mut root: usize = NIL;
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let mut nodes: Vec<Node<usize>> = Vec::new();
/// for n in values.iter() {
///     insert(&mut nodes, &mut root, Node::from(*n));
/// }
///
/// for i in (0..nodes.len()).rev() {
///     assert!(root != NIL);
///     assert!(!nodes.is_empty());
///     delete(&mut nodes, &mut root, i).unwrap();
/// }
///
/// assert!(nodes.is_empty(), "Failed to remove all nodes.");
/// assert!(root == NIL, "root is not NIL.");
/// ```
pub fn delete<K, T>(nodes: &mut Vec<T>, root: &mut usize, index: usize) -> Result<T>
where
    K: Ord + Copy,
    T: TreeNode<K>,
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
                transplant(nodes, root, y, nodes[y].right());
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

pub fn successor<K, T>(nodes: &Vec<T>, mut index: usize) -> Option<usize>
where
    K: Ord + Copy,
    T: TreeNode<K>,
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

pub fn predecessor<K, T>(nodes: &Vec<T>, mut index: usize) -> Option<usize>
where
    K: Ord + Copy,
    T: TreeNode<K>,
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

/// Returns the index of smallest value in the tree starting with the node at `index` or `None` if the tree is empty.
///
/// ```
/// use rtreap::bst::{minimum, insert, Node, TreeNode, NIL};
///
/// let mut root: usize = NIL;
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let mut nodes: Vec<Node<usize>> = Vec::new();
/// for n in values.iter() {
///     insert(&mut nodes, &mut root, Node::from(*n));
/// }
///
/// let i: usize = minimum(&nodes, root).unwrap();
/// assert!(*nodes[i].key() == 1, "Minimum returned {} instead of 1", i);
/// ```
pub fn minimum<K, T>(nodes: &Vec<T>, mut index: usize) -> Option<usize>
where
    K: Ord + Copy,
    T: TreeNode<K>,
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

/// Returns the index of largest value in the tree starting with the node at `index` or `None` if the tree is empty.
///
/// ```
/// use rtreap::bst::{maximum, insert, Node, TreeNode, NIL};
///
/// let mut root: usize = NIL;
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let mut nodes: Vec<Node<usize>> = Vec::new();
/// for n in values.iter() {
///     insert(&mut nodes, &mut root, Node::from(*n));
/// }
///
/// if let Some(i) = maximum(&nodes, root) {
///     assert!(*nodes[i].key() == 9, "Maximum returned {} instead of 9", i);
/// } else {
///     panic!("Maximum returned None.");
/// }
/// ```
pub fn maximum<K, T>(nodes: &Vec<T>, mut index: usize) -> Option<usize>
where
    K: Ord + Copy,
    T: TreeNode<K>,
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
/// use rtreap::bst::{minimum, maximum, insert, Node, TreeNode, NIL};
///
/// let mut root: usize = NIL;
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let mut nodes: Vec<Node<usize>> = Vec::new();
/// for n in values.iter() {
///     insert(&mut nodes, &mut root, Node::from(*n));
/// }
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
    T: TreeNode<K>,
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
/// use rtreap::bst::{search, insert, Node, TreeNode, NIL};
///
/// let mut root: usize = NIL;
/// let values: Vec<usize> = vec![5,6,3,9,7,8,4,1,2];
/// let mut nodes: Vec<Node<usize>> = Vec::new();
/// for n in values.iter() {
///     insert(&mut nodes, &mut root, Node::from(*n));
/// }
///
/// assert!(*nodes[root].key() == 5, "Invalid root");
///
/// let search_result = search(&nodes, root, &4).unwrap();
/// assert!(4 == *nodes[search_result].key(), "Search returned {} instead of 4.", search_result);
/// ```
pub fn search<K, T>(nodes: &[T], mut root: usize, key: &K) -> Option<usize>
where
    K: Ord,
    T: TreeNode<K>,
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

pub fn rotate_right<K, T>(nodes: &mut [T], root: &mut usize, node: usize)
where
    T: TreeNode<K>,
{
    let treap_size: usize = nodes.len();
    if node < treap_size {
        let l: usize = nodes[node].left();
        if l < treap_size {
            let p: usize = nodes[node].parent();
            nodes[l].set_parent(p);
            if p < treap_size {
                if node == nodes[p].left() {
                    nodes[p].set_left(l);
                } else {
                    nodes[p].set_right(l);
                }
            } else {
                *root = l;
            }
            nodes[node].set_parent(l);
            let r: usize = nodes[l].right();
            nodes[node].set_left(r);
            if r < treap_size {
                nodes[r].set_parent(node);
            }
            nodes[l].set_right(node);
        }
    }
}

pub fn rotate_left<K, T>(nodes: &mut [T], root: &mut usize, node: usize)
where
    T: TreeNode<K>,
{
    let treap_size: usize = nodes.len();
    if node < treap_size {
        let r: usize = nodes[node].right();
        if r < treap_size {
            let p: usize = nodes[node].parent();
            nodes[r].set_parent(p);
            if p < treap_size {
                if node == nodes[p].left() {
                    nodes[p].set_left(r);
                } else {
                    nodes[p].set_right(r);
                }
            } else {
                *root = r;
            }
            nodes[node].set_parent(r);
            let l: usize = nodes[r].left();
            nodes[node].set_right(l);
            if l < treap_size {
                nodes[l].set_parent(node);
            }
            nodes[r].set_left(node);
        }
    }
}

pub fn inorder<K, F, T>(nodes: &[T], mut node: usize, callback: F)
where
    F: Fn(&K),
    T: TreeNode<K>,
{
    let mut prev: usize = node;
    while node < nodes.len() {
        if nodes[node].right() != prev {
            if nodes[node].left() != prev {
                while nodes[node].left() != NIL {
                    node = nodes[node].left();
                }
            }
            callback(&nodes[node].key());
            if nodes[node].right() != NIL {
                node = nodes[node].right();
                loop {
                    while nodes[node].left() != NIL {
                        node = nodes[node].left();
                    }
                    callback(&nodes[node].key());
                    if nodes[node].right() != NIL {
                        node = nodes[node].right();
                    } else {
                        break;
                    }
                }
            }
        }
        prev = node;
        node = nodes[node].parent();
    }
}

pub fn preorder<K, F, T>(nodes: &[T], mut node: usize, callback: F)
where
    F: Fn(&K),
    T: TreeNode<K>,
{
    let mut prev = node;
    while node != NIL {
        //go down the nodes
        if nodes[node].right() != prev {
            if nodes[node].left() != prev {
                callback(&nodes[node].key());
                while nodes[node].left() != NIL {
                    node = nodes[node].left();
                    callback(&nodes[node].key());
                }
            }
            if nodes[node].right() != NIL {
                node = nodes[node].right();
                callback(&nodes[node].key());
                loop {
                    while nodes[node].left() != NIL {
                        node = nodes[node].left();
                        callback(&nodes[node].key());
                    }
                    if nodes[node].right() != NIL {
                        node = nodes[node].right();
                        callback(&nodes[node].key());
                    } else {
                        break;
                    }
                }
            }
        }
        //go up the nodes
        prev = node;
        node = nodes[node].parent();
    }
}

pub fn postorder<K, F, T>(nodes: &[T], mut node: usize, callback: F)
where
    F: Fn(&T),
    T: TreeNode<K>,
{
    let mut prev = node;
    while node != NIL {
        if nodes[node].right() != prev {
            if nodes[node].left() != prev {
                while nodes[node].left() != NIL {
                    node = nodes[node].left()
                }
            }
            if nodes[node].right() != NIL {
                node = nodes[node].right();
                loop {
                    while nodes[node].left() != NIL {
                        node = nodes[node].left()
                    }
                    if nodes[node].right() != NIL {
                        node = nodes[node].right();
                    } else {
                        break;
                    }
                }
            }
        }
        callback(&nodes[node]);
        prev = node;
        node = nodes[node].parent();
    }
}

/*

struct Trunk {
    prev: usize,
    text: &'static str,
}

fn showTrunks(trunk: &Trunk) {
    showTrunks(&trunk.prev);
    print!("{}", trunk.s);
}

fn print_nodes<K>(nodes: &[dyn TreeNode<K>], root: usize, prev: Option<Trunk>, isLeft: bool) {
    if root < nodes.len() {
        let prev_str: &'static str = "    ";
        let trunk = Trunk {
            prev,
            text: prev_str,
        };

        print_nodes(nodes, nodes[root].left, Some(trunk), true);

        if prev.is_none() {
            trunk.text = "----";
        } else if isLeft {
            trunk.text = ",---";
            prev_str = "   |";
        } else {
            trunk.text = "`---";
            prev.text = prev_str;
        }

        showTrunks(&trunk);
        print!("{}", root);

        if (prev) {
            prev.text = prev_str;
        }
        trunk.text = "   |";

        print_nodes(nodes, nodes[root].right, Some(trunk), false);
    }
}

pub fn print_bst<K>(nodes: &[TreeNode<K>], root: usize) {
    if root < nodes.len() {
        print_nodes(nodes, root, None, false);
        println!();
    }
}
*/
