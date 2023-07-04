// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

/*!
 * Put crate documentation here...
 */

use crate::{bst, heap};
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

/// Updates the order of the nodes in the treap starting from `index` and going down the tree.
pub fn push_down<K, P, N>(nodes: &mut [N], root: &mut usize, order: Ordering, index: usize)
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
{
    while !nodes[index].is_leaf() {
        if nodes[index].left() != bst::NIL
            && (nodes[index].right() == bst::NIL
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
/// while !treap.is_empty() {
///     assert!(is_valid(&treap, root, Greater));
///     let index = rand::thread_rng().gen_range(0..treap.len());
///     remove(&mut treap, &mut root, Greater, index);
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
    if index >= nodes.len() {
        None
    } else if nodes.len() == 1 {
        *root = bst::NIL;
        Some(nodes.pop().unwrap()) // should never panic
    } else {
        push_down(nodes, root, order, index);
        let p: usize = nodes[index].parent();
        if nodes[p].left() == index {
            nodes[p].set_left(bst::NIL);
        } else {
            nodes[p].set_right(bst::NIL);
        }
        bst::swap_remove(nodes, root, index)
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
///     update(&mut treap, &mut root, Greater, index, new_priority);
///     assert!(is_valid(&treap, root, Greater));
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
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
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
    !(root >= nodes.len() || !heap::is_valid(nodes, order, root) || !bst::is_valid(nodes, root))
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
    K: Ord + Copy,
    P: Ord + Copy,
{
    parent: usize,
    left: usize,
    right: usize,
    entry: (K, P),
}

impl<K, P> From<(K, P)> for TreapNode<K, P>
where
    K: Ord + Copy,
    P: Ord + Copy,
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
    K: Ord + Copy,
    P: Ord + Copy,
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
    K: Ord + Copy,
    P: Ord + Copy,
{
    /// Returns an immutable reference to a tuple containing the node's key and priority.
    #[inline]
    fn entry(&self) -> &(K, P) {
        &self.entry
    }
}

impl<K, P> bst::Node<K> for TreapNode<K, P>
where
    K: Ord + Copy,
    P: Ord + Copy,
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

/// An implementation of an ordinary treap using the [Treap] trait.
#[derive(Debug, Clone)]
pub struct BasicTreap<K, P, const MAX_HEAP: bool>
where
    K: Ord + Copy,
    P: Ord + Copy,
{
    treap: Vec<TreapNode<K, P>>,
    root: usize,
    order: Ordering,
}

impl<K, P, const MAX_HEAP: bool> Default for BasicTreap<K, P, MAX_HEAP>
where
    K: Ord + Copy,
    P: Ord + Copy,
{
    /// Creates a new `BasicTreap` object.
    fn default() -> Self {
        Self::new()
    }
}

impl<K, P, const MAX_HEAP: bool> BasicTreap<K, P, MAX_HEAP>
where
    K: Ord + Copy,
    P: Ord + Copy,
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

    /// Shortens the underlying vector, keeping the first `len` elements and dropping the rest.
    /// If len is greater than the vector's current length, this has no effect.
    /// Note that this method has no effect on the allocated capacity of the vector.
    pub fn truncate(&mut self, len: usize) {
        self.treap.truncate(len)
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
        is_valid(&self.treap, self.root, self.order)
    }
}

impl<K, P, const MAX_HEAP: bool> Treap<K, P, MAX_HEAP> for BasicTreap<K, P, MAX_HEAP>
where
    K: Ord + Copy,
    P: Ord + Copy,
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
