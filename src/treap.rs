// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

/*!
 * An implementation of a treap, also know as a cartesian tree.
 *
 * Memory allocations are designed to use a linear model, where nodes are stored
 * consecutively in an array or vector, rather than allocating memory for each
 * node separately on the heap. This has the advantage of reducing the number of
 * allocations at a cost of possibly using more memory.
 *
 * Instead of pointers or references, usize indexes are used to indicate the location
 * of a node in the array/vector. Therefore, nodes contain the usize index of both
 * children and parent nodes. An invalid index (that is out of bounds) is treated as
 * a sentinal/terminal value by all functions. The [bst::NIL] constant is provided in this
 * module as a convenient way to help manage this. Keep in mind that you are responsible
 * for keeping track of the index of the root node in the tree.
 *
 */

use crate::{
    bst::{self, rotate_left, rotate_right},
    heap,
};
use std::cmp::Ordering;

/// A trait that defines the interface of a node in a treap. Implementors of this trait
/// are also required to also implement [bst::Node<K>] and [heap::Priority<P>].
pub trait Node<K, P>: bst::Node<K> + heap::Priority<P>
where
    Self: Sized,
    K: Ord + Copy,
    P: Ord + Copy,
{
    /// Should return am immutable reference to a tuple containing the
    /// node's key and priority values.
    fn entry(&self) -> &(K, P);
}

/// A trait that defines the interface of a treap.
#[allow(unused_variables)]
pub trait Treap<K, P, const MAX_HEAP: bool> {
    /// Inserts a new key and priority value into the treap. This function
    /// should return `Some(())` on success or `None` if the key already
    /// exists in the treap.
    fn insert(&mut self, key: K, priority: P) -> Option<()>;

    /// Searches for the element containing `key`, removes it from the treap,
    /// and returns a tuple containing its key and priority or `None`
    /// if `key` does not exist in the treap.
    fn remove(&mut self, key: &K) -> Option<(K, P)>;

    /// Searches for the element containing `key`, sets is priority to `new_priority`,
    /// and returns the old priority or `None` if `key` does not exist in the treap.
    fn update(&mut self, key: &K, new_priority: P) -> Option<P> {
        None // update does not apply to all types of treaps
    }

    /// Removes and returns the element on the top of the treap in the form of a tuple containing
    /// the removed node's key and priority or `None` if the treap is empty.
    fn top(&mut self) -> Option<(K, P)>;

    /// Returns an immutable reference to a tuple containing the key and value of the node on top
    /// of the treap without removing it or `None` if the treap is empty.
    fn peek(&self) -> Option<&(K, P)>;

    /// Performs a binary search for `key` and returns an immutable reference to a tuple
    /// containing its key and priority or `None` if the key does not exist in the treap.
    fn search(&self, key: &K) -> Option<&(K, P)>;

    /// Returns the number of entries in the treap.
    fn len(&self) -> usize;

    /// Returns true if the treap is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Constructs a treap from a slice of objects that implement the
/// `Node` trait and returns a tuple containing a vector of tree
/// nodes and the index of the root node.
///
/// ## Example:
///
/// ```
/// use rtreap::treap::{build, insert, TreapNode, Node, is_valid};
/// use rtreap::bst::NIL;
/// use std::cmp::Ordering::Greater;
/// use rand::prelude::*;
///
/// type MyNode = TreapNode<usize, usize>;
///
/// let mut values:Vec<MyNode> = Vec::new();
/// let mut treap: Vec<MyNode> = Vec::new();
/// let mut root: usize = NIL;
///
/// for i in 0..100 {
///     let node = MyNode::from((rand::random(), rand::random()));
///     values.push(node);
/// }
///
/// let (mut treap, mut root) = build(&values, Greater);
///
/// assert!(is_valid(&treap, root, Greater));
/// ```
pub fn build<K, P, N>(s: &[N], order: Ordering) -> (Vec<N>, usize)
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P> + From<N> + Copy,
{
    let mut nodes: Vec<N> = Vec::new();
    let mut root: usize = bst::NIL;
    for node in s {
        insert(&mut nodes, &mut root, order, *node);
    }
    (nodes, root)
}

/// Updates the order of the nodes in the treap starting from `index` and going up the tree to the root.
pub fn bubble_up<K, P, N>(nodes: &mut Vec<N>, root: &mut usize, order: Ordering, index: usize)
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
{
    let len: usize = nodes.len();
    while nodes[index].parent() < len
        && nodes[index]
            .priority()
            .cmp(nodes[nodes[index].parent()].priority())
            == order
    {
        let p: usize = nodes[index].parent();
        if index == nodes[p].right() {
            bst::rotate_left(nodes, root, p);
        } else {
            bst::rotate_right(nodes, root, p);
        }
    }
}

/// Inserts a new node into the treap. Returns `None` if the node's key already exists in the treap.
///
/// ## Arguments:
///
/// - nodes - A vector used to store the nodes in memory.
/// - root - The index of the root node in the vector.
/// - order - Ordering::Greater indicates a maximum treap, otherwise a minimum treap.
/// - node - The new node to insert.
///
/// ## Example:
///
/// ```
/// use rtreap::treap::{is_valid, insert, Node, TreapNode};
/// use rtreap::bst::NIL;
/// use std::cmp::Ordering::Greater;
///
/// type MyNode = TreapNode<usize, usize>;
/// let values: [usize; 9] = [1,2,3,4,5,6,7,8,9];
/// let mut treap: Vec<MyNode> = Vec::new();
/// let mut root: usize = NIL;
///
/// for v in values {
///     insert(&mut treap, &mut root, Greater, MyNode::from((v,v)));
///     assert!(is_valid(&treap, root, Greater))
/// }
/// ```
pub fn insert<K, P, N>(nodes: &mut Vec<N>, root: &mut usize, order: Ordering, node: N) -> Option<()>
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
{
    if let Ok(index) = bst::insert(nodes, root, node) {
        bubble_up(nodes, root, order, index);
        Some(())
    } else {
        None
    }
}

/*
/// Updates the order of the nodes in the treap starting from `index` and going down the tree.
pub fn push_down<K, P, N>(nodes: &mut [N], root: &mut usize, order: Ordering, index: usize)
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
{
    //while !nodes[index].is_leaf() {
    let len = nodes.len();
    while nodes[index].left() < len || nodes[index].right() < len {
        if nodes[index].left() < len
            && (nodes[index].right() >= len
                || nodes[nodes[index].left()]
                    .priority()
                    .cmp(nodes[nodes[index].right()].priority())
                    == order)
        {
            bst::rotate_right(nodes, root, index);
        } else {
            bst::rotate_left(nodes, root, index);
        }
    }
}
*/

#[inline]
fn get_child<K, P, N>(nodes: &mut [N], a: usize, order: Ordering, b: usize) -> Option<usize>
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
{
    let len: usize = nodes.len();
    if a >= len && b >= len {
        None
    } else if a >= len {
        Some(b)
    } else if b >= len {
        Some(a)
    } else {
        if nodes[a].priority().cmp(nodes[b].priority()) == order {
            Some(a)
        } else {
            Some(b)
        }
    }
}

/// Updates the order of the nodes in the treap starting from `index` and going down the tree.
pub fn push_down<K, P, N>(nodes: &mut [N], root: &mut usize, order: Ordering, index: usize)
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
{
    while let Some(child_index) = get_child(nodes, nodes[index].left(), order, nodes[index].right()) {
        if nodes[child_index].priority().cmp(nodes[index].priority()) == order {
            if child_index == nodes[index].right() {
                rotate_left(nodes, root, index);
            } else {
                rotate_right(nodes, root, index);
            }
        } else {
            break;
        }
    }
}

/// Removes and returns the element at `index` from the treap. Returns `None` if `index` is
/// out of bounds or the treap is empty.
///
/// ## Example:
///
/// ```
/// use rtreap::treap::{build, remove, insert, TreapNode, Node, is_valid};
/// use rtreap::bst::NIL;
/// use std::cmp::Ordering::Greater;
/// use rand::prelude::*;
///
/// type MyNode = TreapNode<usize, usize>;
///
/// let mut treap: Vec<MyNode> = Vec::new();
/// let mut root: usize = NIL;
///
/// for i in 0..100 {
///     let node = MyNode::from((rand::random(), rand::random()));
///     insert(&mut treap, &mut root, Greater, node);
/// }
/// 
/// assert!(is_valid(&treap, root, Greater), "Insertion did not produce a valid treap.");
///
/// while !treap.is_empty() {
///     let index = rand::thread_rng().gen_range(0..treap.len());
///     assert!(index < treap.len());
///     assert!(root < treap.len());
///     assert!(remove(&mut treap, &mut root, Greater, index).is_some(), "Treap removal failed");
///     assert!(is_valid(&treap, root, Greater), "Treap properties violated after removal of node");
/// }
/// ```
pub fn remove<K, P, N>(
    nodes: &mut Vec<N>,
    root: &mut usize,
    order: Ordering,
    index: usize,
) -> Option<N>
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
{
    let len: usize = nodes.len();
    if index < len {
        let r: usize = nodes[index].right();
        let l: usize = nodes[index].left();
        if l >= len && r >= len {    // leaf node
            if index == *root {
                *root = bst::NIL;
            } else {
                let p: usize = nodes[index].parent();
                if index == nodes[p].left() {
                    nodes[p].set_left(bst::NIL);
                } else {
                    nodes[p].set_right(bst::NIL);
                }
            }
        } else if l >= len && r < len {
            bst::transplant(nodes, root, index, r);
        } else if l < len && r >= len {
            bst::transplant(nodes, root, index, l);
        } else {
            let y: usize = bst::minimum(nodes, r).unwrap(); // should never panic
            if y != r {
                let yr = nodes[y].right();
                bst::transplant(nodes, root, y, yr);
                nodes[y].set_right(r);
                nodes[r].set_parent(y);
            }
            bst::transplant(nodes, root, index, y);
            nodes[y].set_left(l);
            nodes[l].set_parent(y);
            push_down(nodes, root, order, y);
        }
        bst::swap_remove(nodes, root, index)
    } else {
        None
    }
}

/// Modifies the priority of the element at `index` on the treap in such a way that its
/// ordering relative to other elements is changed. It returns `Some(P)`
/// containing the old priority, or None if `key` does not exist in the treap.
///
/// ## Example:
///
/// ```
/// use rtreap::treap::{build, update, insert, TreapNode, Node, is_valid};
/// use rtreap::bst::{NIL, Node as BstNode};
/// use std::cmp::Ordering::Greater;
/// use rand::prelude::*;
/// use rtreap::heap;
/// use rtreap::bst;
///
/// type MyNode = TreapNode<usize, usize>;
///
/// let mut treap: Vec<MyNode> = Vec::new();
/// let mut root: usize = NIL;
///
/// for i in 0..100 {
///     let node = MyNode::from((rand::random(), rand::random()));
///     insert(&mut treap, &mut root, Greater, node);
/// }
///
/// for index in 0..treap.len() {
///     let new_priority = rand::thread_rng().gen_range(0..treap.len());
///     assert!(update(&mut treap, &mut root, Greater, index, new_priority).is_some());
///     assert!(bst::is_valid(&treap, root), "bst::is_valid failed for index {}", index);
///     assert!(heap::is_valid(&treap, Greater, root), "heap::is_valid failed for index {}", index);
/// }
/// ```
pub fn update<K, P, N>(
    nodes: &mut Vec<N>,
    root: &mut usize,
    order: Ordering,
    index: usize,
    new_priority: P,
) -> Option<P>
where
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
    N: Node<K, P> + std::fmt::Debug,
{
    if index < nodes.len() {
        let old_priority: P = *nodes[index].priority();
        nodes[index].set_priority(new_priority);
        if new_priority.cmp(&old_priority) == order {
            bubble_up(nodes, root, order, index);
        } else {
            push_down(nodes, root, order, index);
        }
        Some(old_priority)
    } else {
        None
    }
}

/// Removes and returns the element on the top of the treap. Returns `None` if the Treap is empty.
pub fn top<K, P, N>(nodes: &mut Vec<N>, root: &mut usize, order: Ordering) -> Option<N>
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
{
    if nodes.is_empty() {
        None
    } else {
        remove(nodes, root, order, *root)
    }
}

/// Returns true if the properties of both a heap and a binary search tree hold true.
/// This function is primarly used for testing.
pub fn is_valid<K, P, N>(nodes: &Vec<N>, root: usize, order: Ordering) -> bool
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
{
    heap::is_valid(nodes, order, root) && bst::is_valid(nodes, root)
}

/// An implementation of the [Node] trait.
///
/// ## Arguments:
///
/// - `K` is a generic type that represents the node's key.
/// - `P` is a generic type that represents the node's priority.
#[derive(Debug, Clone, Copy)]
pub struct TreapNode<K, P>
where
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    parent: usize,
    left: usize,
    right: usize,
    entry: (K, P),
}

impl<K, P> From<(K, P)> for TreapNode<K, P>
where
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    /// Creates and initializes a new node with a tuplie containing a key and priority.
    fn from(entry: (K, P)) -> Self {
        Self {
            parent: bst::NIL,
            left: bst::NIL,
            right: bst::NIL,
            entry,
        }
    }
}

impl<K, P> heap::Priority<P> for TreapNode<K, P>
where
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    /// Returns an immutable reference to the node's priority.
    #[inline]
    fn priority(&self) -> &P {
        &self.entry.1
    }

    /// Sets the nodes' priority to `new_priority`.
    #[inline]
    fn set_priority(&mut self, new_priority: P) {
        self.entry.1 = new_priority;
    }
}

impl<K, P> Node<K, P> for TreapNode<K, P>
where
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    /// Returns an immutable reference to a tuple containing the node's key and priority.
    #[inline]
    fn entry(&self) -> &(K, P) {
        &self.entry
    }
}

impl<K, P> bst::Node<K> for TreapNode<K, P>
where
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    /// Returns an immutable reference to the node's key.
    #[inline]
    fn key(&self) -> &K {
        &self.entry.0
    }

    /// Returns the index of the node's left child.
    #[inline]
    fn left(&self) -> usize {
        self.left
    }

    /// Returns the index of the node's right child.
    #[inline]
    fn right(&self) -> usize {
        self.right
    }

    /// Returns the index of the node's parent.
    #[inline]
    fn parent(&self) -> usize {
        self.parent
    }

    /// Sets the index of the node's left child.
    #[inline]
    fn set_left(&mut self, l: usize) {
        self.left = l;
    }

    /// Sets the index of the node's parent.
    #[inline]
    fn set_parent(&mut self, p: usize) {
        self.parent = p;
    }

    /// Sets the index of the node's right child.
    #[inline]
    fn set_right(&mut self, r: usize) {
        self.right = r;
    }
}

pub struct Iter<'a, K, P>
where
    Self: Sized,
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    iter: std::slice::Iter<'a, TreapNode<K, P>>,
}

impl<'a, K, P> From<std::slice::Iter<'a, TreapNode<K, P>>> for Iter<'a, K, P>
where
    Self: Sized,
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    fn from(iter: std::slice::Iter<'a, TreapNode<K, P>>) -> Self {
        Iter { iter }
    }
}

impl<'a, K, P> Iterator for Iter<'a, K, P>
where
    Self: Sized,
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    type Item = &'a (K, P);
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|node| node.entry())
    }
}

/// An implementation of an ordinary treap using the [Treap] trait.
#[derive(Debug, Clone)]
pub struct BasicTreap<K, P, const MAX_HEAP: bool>
where
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    treap: Vec<TreapNode<K, P>>,
    root: usize,
    order: Ordering,
}

impl<K, P, const MAX_HEAP: bool> Default for BasicTreap<K, P, MAX_HEAP>
where
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    /// Creates a new `BasicTreap` object.
    fn default() -> Self {
        Self::new()
    }
}

impl<K, P, const MAX_HEAP: bool> BasicTreap<K, P, MAX_HEAP>
where
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    /// Creates, initializes, and returns a new [BasicTreap] object.
    pub fn new() -> Self {
        Self {
            treap: Vec::new(),
            root: bst::NIL,
            order: if MAX_HEAP {
                Ordering::Greater
            } else {
                Ordering::Less
            },
        }
    }

    pub fn iter(&self) -> Iter<'_, K, P> {
        Iter::from(self.treap.iter())
    }

    /// Constructs a new, empty treap with at least the specified capacity.
    /// The treap will be able to hold at least capacity elements without reallocating.
    /// This method is allowed to allocate for more elements than capacity.
    /// If capacity is 0, the treap will not allocate.
    /// It is important to note that although the returned treap has the minimum capacity specified, the treap will have a zero length.
    /// If it is important to know the exact allocated capacity of a treap, always use the `capacity` method after construction.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            treap: Vec::with_capacity(capacity),
            root: bst::NIL,
            order: if MAX_HEAP {
                Ordering::Greater
            } else {
                Ordering::Less
            },
        }
    }

    /// Returns the index of the root node in the underlying vector.
    pub fn root(&self) -> usize {
        self.root
    }

    /// Returns the number of elements the treap can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.treap.capacity()
    }

    /// Returns a slice containing the entire underlying vector.
    pub fn as_slice(&self) -> &[TreapNode<K, P>] {
        self.treap.as_slice()
    }

    /// Returns the sort order of the heap.
    /// [Ordering::Greater] indicates a maximum treap.
    /// [Ordering::Less] indicates a minimum treap.
    pub fn is_max_heap(&self) -> bool {
        self.order == Ordering::Greater
    }

    /// Clears the treap, removing all elements.
    /// Note that this method has no effect on the allocated capacity of the treap.
    pub fn clear(&mut self) {
        self.treap.clear()
    }

    /// Returns `true` if the correct priority is on top of the treap.
    /// Please note that this function is intended for use during testing.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::{Treap as TreapTrait, BasicTreap};
    /// use std::cmp::Ordering;
    ///
    /// let mut v: Vec<usize> = Vec::new();
    /// let mut treap: BasicTreap<usize, usize, false> = BasicTreap::new();
    /// treap.insert(1, 234);
    /// treap.insert(333, 21);
    /// treap.insert(74, 12);
    /// treap.insert(559, 32);
    /// assert!(treap.is_valid());
    /// ```
    #[doc(hidden)]
    pub fn is_valid(&self) -> bool {
        is_valid(&self.treap, self.root, self.order)
    }
}

impl<K, P, const MAX_HEAP: bool> Treap<K, P, MAX_HEAP> for BasicTreap<K, P, MAX_HEAP>
where
    K: Ord + Copy + std::fmt::Debug,
    P: Ord + Copy + std::fmt::Debug,
{
    /// Returns the number of elements in the treap.
    fn len(&self) -> usize {
        self.treap.len()
    }

    /// Returns `true` if the treap is empty.
    fn is_empty(&self) -> bool {
        self.treap.is_empty()
    }

    /// Returns an immutable reference to a tuple containing the key and priority
    /// of the node at the root of the treap, or `None` if the treap is empty.
    fn peek(&self) -> Option<&(K, P)> {
        if self.treap.is_empty() {
            None
        } else {
            Some(self.treap[self.root].entry())
        }
    }

    /// Performs a binary serach on the Treap to locate the node containing `key`
    /// and returns an immutable reference to a tuple containing its key and
    /// priority, or `None` if the key is not in the treap.
    fn search(&self, key: &K) -> Option<&(K, P)> {
        if let Some(i) = bst::search(&self.treap, self.root, key) {
            Some(self.treap[i].entry())
        } else {
            None
        }
    }

    /// Inserts a new node containing `key` and `priority` into the treap.
    ///
    /// ## Examples:
    ///
    /// ```
    /// use rtreap::treap::{Treap as TreapTrait, BasicTreap};
    ///
    /// let mut treap: BasicTreap<usize, usize, false> = BasicTreap::new();
    /// assert!(treap.insert(123, 456).is_some(), "Treap insertion failed.");
    /// ```
    fn insert(&mut self, key: K, priority: P) -> Option<()> {
        insert(
            &mut self.treap,
            &mut self.root,
            self.order,
            TreapNode::from((key, priority)),
        )
    }

    /// Removes the node containing `key` from the treap and returns a tuple
    /// containing its key and priority. Returns None if `key` does not exist
    /// in the treap.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::{BasicTreap, Treap};
    /// use rand::prelude::*;
    ///
    /// const COUNT: usize = 100;
    ///
    /// let mut treap: BasicTreap<usize, usize, true> = BasicTreap::new();
    /// let mut keys: Vec<usize> = (0..COUNT).map(|_| rand::random::<usize>()).collect();
    /// let mut priorities: Vec<usize> = (0..COUNT).map(|_| rand::random::<usize>()).collect();
    ///
    /// for i in 0..COUNT {
    ///     treap.insert(keys[i], priorities[i]);
    /// }
    ///
    /// for k in keys {
    ///     assert!(treap.is_valid());
    ///     assert!(treap.remove(&k).is_some());
    /// }
    /// ```
    fn remove(&mut self, key: &K) -> Option<(K, P)> {
        if let Some(index) = bst::search(&self.treap, self.root, key) {
            if let Some(node) = remove(&mut self.treap, &mut self.root, self.order, index) {
                return Some(*node.entry());
            }
        }
        None
    }

    /// Removes the node containing `key` from the treap and returns a tuple
    /// containing its key and priority. Returns None if `key` does not exist
    /// in the treap.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::{BasicTreap, Treap};
    /// use rand::prelude::*;
    ///
    /// const COUNT: usize = 100;
    ///
    /// let mut treap: BasicTreap<usize, usize, true> = BasicTreap::new();
    /// let mut keys: Vec<usize> = (0..COUNT).map(|_| rand::random::<usize>()).collect();
    /// let mut priorities: Vec<usize> = (0..COUNT).map(|_| rand::random::<usize>()).collect();
    ///
    /// for i in 0..COUNT {
    ///     treap.insert(keys[i], priorities[i]);
    /// }
    ///
    /// for k in keys {
    ///     let new_priority = rand::random::<usize>();
    ///     assert!(treap.update(&k, new_priority).is_some());
    ///     assert!(treap.is_valid());
    /// }
    /// ```
    fn update(&mut self, key: &K, new_priority: P) -> Option<P> {
        if let Some(index) = bst::search(&self.treap, self.root, key) {
            update(
                &mut self.treap,
                &mut self.root,
                self.order,
                index,
                new_priority,
            )
        } else {
            None
        }
    }

    /// Removes the node containing `key` from the treap and returns a tuple
    /// containing its key and priority. Returns None if `key` does not exist
    /// in the treap.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::{BasicTreap, Treap};
    /// use rand::prelude::*;
    ///
    /// const COUNT: usize = 100;
    ///
    /// let mut treap: BasicTreap<usize, usize, true> = BasicTreap::new();
    ///
    /// for i in 0..COUNT {
    ///     treap.insert(rand::random::<usize>(), rand::random::<usize>());
    /// }
    ///
    /// while !treap.is_empty() {
    ///     let begin_len = treap.len();
    ///     assert!(treap.is_valid());
    ///     assert!(treap.top().is_some());
    ///     let end_len = treap.len();
    ///     assert!(begin_len - end_len == 1);
    /// }
    /// ```
    fn top(&mut self) -> Option<(K, P)> {
        top(&mut self.treap, &mut self.root, self.order).map(|x| *x.entry())
    }
}

/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/

/// An implementation of a randomized treap.
///
/// This struct is implemented as a wrapper around a [BasicTreap] object, which automatically
/// assigns a random priority to each node with the aim of self-balancing the tree.
///
/// Nodes in this treap store both the key and priority. The key is provided as generic parameter
/// `K` but the priority is automatically assigned by using the [rand::random] function.This approach
/// has the advantage of not needing to calculate the priority for each node when making changes to
/// the treap, however, at the cost of using more memory.
///
/// The interface for this implementation is slightly different than [BasicTreap] because several
/// of the methods that are common to a treap are not applicable to a randomized treap by its nature.
/// These include `peek`, `top`, and `update`.
pub struct RandomizedTreap<K>
where
    K: Ord + Copy + std::fmt::Debug,
{
    treap: BasicTreap<K, usize, true>,
}

impl<K> Default for RandomizedTreap<K>
where
    K: Ord + Copy + std::fmt::Debug,
{
    /// Creates a new `RandomizedTreap` object.
    fn default() -> Self {
        Self::new()
    }
}

impl<K> RandomizedTreap<K>
where
    K: Ord + Copy + std::fmt::Debug,
{
    /// Creates, initializes, and returns a new [RandomizedTreap] object.
    pub fn new() -> Self {
        Self {
            treap: BasicTreap::new(),
        }
    }

    /// Constructs a new, empty treap with at least the specified capacity.
    /// The treap will be able to hold at least capacity elements without reallocating.
    /// This method is allowed to allocate for more elements than capacity.
    /// If capacity is 0, the treap will not allocate.
    /// It is important to note that although the returned treap has the minimum capacity specified, the treap will have a zero length.
    /// If it is important to know the exact allocated capacity of a treap, always use the `capacity` method after construction.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            treap: BasicTreap::with_capacity(capacity),
        }
    }

    /// Returns the index of the root node in the underlying vector.
    pub fn root(&self) -> usize {
        self.treap.root()
    }

    /// Returns the number of elements the treap can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.treap.capacity()
    }

    /// Clears the treap, removing all elements.
    /// Note that this method has no effect on the allocated capacity of the treap.
    pub fn clear(&mut self) {
        self.treap.clear()
    }

    /// Returns true if the correct priority is on top of the treap.
    /// Please note that this function is intended for use during testing.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::{Treap as TreapTrait, BasicTreap};
    /// use std::cmp::Ordering;
    ///
    /// let mut v: Vec<usize> = Vec::new();
    /// let mut treap: BasicTreap<usize, usize, false> = BasicTreap::new();
    /// treap.insert(1, 234);
    /// treap.insert(333, 21);
    /// treap.insert(74, 12);
    /// treap.insert(559, 32);
    /// assert!(treap.is_valid());
    /// ```
    #[doc(hidden)]
    pub fn is_valid(&self) -> bool {
        self.treap.is_valid()
    }

    /// Returns the number of elements in the treap.
    pub fn len(&self) -> usize {
        self.treap.len()
    }

    /// Returns `true` if the treap is empty.
    pub fn is_empty(&self) -> bool {
        self.treap.is_empty()
    }

    /// Performs a binary serach on the Treap to locate the node containing `key` and
    /// returns an immutable reference to its key, or `None` if the key is not in the treap.
    pub fn search(&self, key: &K) -> Option<&K> {
        if let Some(x) = self.treap.search(key) {
            Some(&x.0)
        } else {
            None
        }
    }

    /// Inserts a new node containing `key` into the treap.
    ///
    /// ## Examples:
    ///
    /// ```
    /// use rtreap::treap::{Treap as TreapTrait, BasicTreap};
    ///
    /// let mut treap: BasicTreap<usize, usize, false> = BasicTreap::new();
    /// assert!(treap.insert(123, 456).is_some(), "Treap insertion failed.");
    /// ```
    pub fn insert(&mut self, key: K) -> Option<()> {
        self.treap.insert(key, rand::random::<usize>())
    }

    /// Removes the node containing `key` from the treap and returns the removed node's key.
    /// Returns None if `key` does not exist in the treap.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::{BasicTreap, Treap};
    /// use rand::prelude::*;
    ///
    /// const COUNT: usize = 100;
    ///
    /// let mut treap: BasicTreap<usize, usize, true> = BasicTreap::new();
    /// let mut keys: Vec<usize> = (0..COUNT).map(|_| rand::random::<usize>()).collect();
    /// let mut priorities: Vec<usize> = (0..COUNT).map(|_| rand::random::<usize>()).collect();
    ///
    /// for i in 0..COUNT {
    ///     treap.insert(keys[i], priorities[i]);
    /// }
    ///
    /// for k in keys {
    ///     assert!(treap.is_valid());
    ///     assert!(treap.remove(&k).is_some());
    /// }
    /// ```
    pub fn remove(&mut self, key: &K) -> Option<K> {
        self.treap.remove(key).map(|x| x.0)
    }

    /// This method attempts to rebalance the tree by iterating over each node,
    /// assigning a new random priority, and updating its order relative to the
    /// other nodes in the tree.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::{RandomizedTreap, Treap};
    /// use rand::prelude::*;
    ///
    /// const COUNT: usize = 100;
    ///
    /// let mut treap: RandomizedTreap<usize> = RandomizedTreap::new();
    /// let mut keys: Vec<usize> = (0..COUNT).map(|_| rand::random::<usize>()).collect();
    ///
    /// for i in 0..COUNT {
    ///     treap.insert(keys[i]);
    /// }
    ///
    /// treap.rebalance();
    ///
    /// assert!(treap.is_valid());
    /// ```
    pub fn rebalance(&mut self) {
        for index in 0..self.len() {
            let new_priority: usize = rand::random();
            update(
                &mut self.treap.treap,
                &mut self.treap.root,
                self.treap.order,
                index,
                new_priority,
            );
        }
    }
}
