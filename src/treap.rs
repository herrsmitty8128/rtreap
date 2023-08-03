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
 * a sentinal/terminal value by all functions. The [bst::bst::NIL] constant is provided in this
 * module as a convenient way to help manage this. Keep in mind that you are responsible
 * for keeping track of the index of the root node in the tree.
 *
 */

use crate::{bst, bst::BinaryNode};
use crate::{heap, heap::MutPriority, heap::Priority};
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::default::Default;
use std::hash::{Hash, Hasher};

/// Constructs a treap from a slice of objects that implement the
/// [Node] trait and returns a tuple containing a vector of tree
/// nodes and the index of the root node.
///
/// ## Example:
///
/// ```
/// use rtreap::treap::{build, insert, TreapNode, is_valid};
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
    N: BinaryNode<K> + Priority<P> + Copy,
{
    let mut nodes: Vec<N> = Vec::new();
    let mut root: usize = bst::NIL;
    for node in s {
        insert(&mut nodes, &mut root, order, *node);
    }
    (nodes, root)
}

/// Updates the order of the nodes in the treap starting from `index` and going up the tree to the root.
pub fn bubble_up<K, P, N>(nodes: &mut [N], root: &mut usize, order: Ordering, index: usize)
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: BinaryNode<K> + Priority<P>,
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
/// use rtreap::treap::{is_valid, insert, TreapNode};
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
    N: BinaryNode<K> + Priority<P>,
{
    if let Ok(index) = bst::insert(nodes, root, node) {
        bubble_up(nodes, root, order, index);
        Some(())
    } else {
        None
    }
}

#[inline]
fn get_child<K, P, N>(nodes: &mut [N], a: usize, order: Ordering, b: usize) -> Option<usize>
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: BinaryNode<K> + Priority<P>,
{
    let len: usize = nodes.len();
    if a >= len && b >= len {
        None
    } else if a >= len {
        Some(b)
    } else if b >= len {
        Some(a)
    } else {
        Some(if nodes[a].priority().cmp(nodes[b].priority()) == order {
            a
        } else {
            b
        })
    }
}

/// Updates the order of the nodes in the treap starting from `index` and going down the tree.
pub fn push_down<K, P, N>(nodes: &mut [N], root: &mut usize, order: Ordering, index: usize)
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: BinaryNode<K> + Priority<P>,
{
    while let Some(child_index) = get_child(nodes, nodes[index].left(), order, nodes[index].right())
    {
        if nodes[child_index].priority().cmp(nodes[index].priority()) == order {
            if child_index == nodes[index].right() {
                bst::rotate_left(nodes, root, index);
            } else {
                bst::rotate_right(nodes, root, index);
            }
        } else {
            break;
        }
    }
}

/// Removes and returns the node at `index` from the treap.
///
/// ## Panics:
///
/// Panics if `index` is out of bounds.
///
/// ## Example:
///
/// ```
/// use rtreap::treap::{build, remove, insert, TreapNode, is_valid};
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
///     remove(&mut treap, &mut root, Greater, index);
///     assert!(is_valid(&treap, root, Greater), "Treap properties violated after removal of node");
/// }
/// ```
pub fn remove<K, P, N>(nodes: &mut Vec<N>, root: &mut usize, order: Ordering, index: usize) -> N
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: BinaryNode<K> + Priority<P>,
{
    if let Some(i) = bst::tree_remove(nodes, root, index) {
        push_down(nodes, root, order, i);
    }
    bst::swap_remove(nodes, root, index)
}

/// Modifies the priority of the node at `index` in such a way that its
/// ordering relative to other nodes is changed. It returns `Some(P)`
/// containing the old priority, or `None` if `key` does not exist in the treap.
///
/// ## Panics:
///
/// Panics if `index` is out of bounds.
///
/// ## Example:
///
/// ```
/// use rtreap::treap::{build, update, insert, TreapNode, is_valid};
/// use rtreap::bst::{NIL, BinaryNode};
/// use std::cmp::Ordering::Greater;
/// use rand::prelude::*;
/// use rtreap::heap;
/// use rtreap::bst;
///
/// type MyNode = TreapNode<usize, usize>;
///
/// let mut treap: Vec<MyNode> = Vec::new();
/// let mut root: usize = bst::NIL;
///
/// for i in 0..100 {
///     let node = MyNode::from((rand::random(), rand::random()));
///     insert(&mut treap, &mut root, Greater, node);
/// }
///
/// for index in 0..treap.len() {
///     let new_priority = rand::thread_rng().gen_range(0..treap.len());
///     update(&mut treap, &mut root, Greater, index, new_priority);
///     assert!(bst::is_valid(&treap, root), "bst::is_valid failed for index {}", index);
///     assert!(heap::is_valid(&treap, Greater, root), "heap::is_valid failed for index {}", index);
/// }
/// ```
pub fn update<K, P, N>(
    nodes: &mut [N],
    root: &mut usize,
    order: Ordering,
    index: usize,
    new_priority: P,
) -> P
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: BinaryNode<K> + Priority<P> + MutPriority<P>,
{
    let old_priority: P = *nodes[index].priority();
    nodes[index].set_priority(new_priority);
    if new_priority.cmp(&old_priority) == order {
        bubble_up(nodes, root, order, index);
    } else {
        push_down(nodes, root, order, index);
    }
    old_priority
}

/// Removes and returns the node on the top of the treap. Returns `None` if the treap is empty.
pub fn top<K, P, N>(nodes: &mut Vec<N>, root: &mut usize, order: Ordering) -> Option<N>
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: BinaryNode<K> + Priority<P>,
{
    if nodes.is_empty() {
        None
    } else {
        Some(remove(nodes, root, order, *root))
    }
}

/// Returns true if the properties of both a heap and a binary search tree hold true.
/// This function is primarly used for testing.
#[doc(hidden)]
pub fn is_valid<K, P, N>(nodes: &[N], root: usize, order: Ordering) -> bool
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: BinaryNode<K> + Priority<P>,
{
    heap::is_valid(nodes, order, root) && bst::is_valid(nodes, root)
}

/// Merges two treaps into one. The nodes of both treaps must be contained in the same vector.
/// This function assumes that all the keys of the nodes in the left treap are less than all the
/// keys of the nodes in the right treap. Verifying this before calling this function is
/// your responsibility. If the keys overlap, then the resulting treap will violate the rules
/// of a binary search tree.
///
/// If the nodes are stored in different vectors, then [bst::extend] can be used to merge the nodes
/// of both treaps into one vector before calling this function.
///
/// ## Panics:
///
/// Panics if `left_root` or `right_root` are out of bounds.
///
/// ## Example:
///
/// ```
/// ```
pub fn merge<K, P, N>(
    nodes: &mut Vec<N>,
    left_root: usize,
    right_root: usize,
    order: Ordering,
) -> usize
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: BinaryNode<K> + Priority<P> + Default + Copy,
{
    let mut new_root: usize = nodes.len();
    nodes.push(N::default());
    nodes[new_root].set_left(left_root);
    nodes[new_root].set_right(right_root);
    nodes[left_root].set_parent(new_root);
    nodes[right_root].set_parent(new_root);
    top(nodes, &mut new_root, order);
    new_root
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
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    parent: usize,
    left: usize,
    right: usize,
    entry: (K, P),
}

impl<K, P> Default for TreapNode<K, P>
where
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    fn default() -> Self {
        Self {
            parent: bst::NIL,
            left: bst::NIL,
            right: bst::NIL,
            entry: (K::default(), P::default()),
        }
    }
}

impl<K, P> From<(K, P)> for TreapNode<K, P>
where
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    /// Creates and initializes a new node with a tuple containing a key and priority.
    fn from(entry: (K, P)) -> Self {
        Self {
            parent: bst::NIL,
            left: bst::NIL,
            right: bst::NIL,
            entry,
        }
    }
}

impl<K, P> Priority<P> for TreapNode<K, P>
where
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    /// Returns an immutable reference to the node's priority.
    #[inline]
    fn priority(&self) -> &P {
        &self.entry.1
    }
}

impl<K, P> MutPriority<P> for TreapNode<K, P>
where
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    /// Sets the nodes' priority to `new_priority`.
    #[inline]
    fn set_priority(&mut self, new_priority: P) {
        self.entry.1 = new_priority;
    }
}

impl<K, P> TreapNode<K, P>
where
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    /// Returns an immutable reference to a tuple containing the node's key and priority.
    #[inline]
    fn entry(&self) -> &(K, P) {
        &self.entry
    }
}

impl<K, P> BinaryNode<K> for TreapNode<K, P>
where
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
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
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    iter: std::slice::Iter<'a, TreapNode<K, P>>,
}

impl<'a, K, P> From<std::slice::Iter<'a, TreapNode<K, P>>> for Iter<'a, K, P>
where
    Self: Sized,
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    fn from(iter: std::slice::Iter<'a, TreapNode<K, P>>) -> Self {
        Iter { iter }
    }
}

impl<'a, K, P> Iterator for Iter<'a, K, P>
where
    Self: Sized,
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    type Item = &'a (K, P);
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|node| node.entry())
    }
}

/// An implementation of an ordinary treap using the [Treap] trait.
#[derive(Debug, Clone)]
pub struct BasicTreap<K, P, const T: bool>
where
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    treap: Vec<TreapNode<K, P>>,
    root: usize,
    order: Ordering,
}

impl<K, P, const T: bool> Default for BasicTreap<K, P, T>
where
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    /// Creates a new [BasicTreap] object.
    fn default() -> Self {
        Self::new()
    }
}

impl<K, P, const T: bool> BasicTreap<K, P, T>
where
    K: Ord + Copy + Default,
    P: Ord + Copy + Default,
{
    /// Creates, initializes, and returns a new [BasicTreap] object.
    pub fn new() -> Self {
        Self {
            treap: Vec::new(),
            root: bst::NIL,
            order: if T { Ordering::Greater } else { Ordering::Less },
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
            order: if T { Ordering::Greater } else { Ordering::Less },
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
    /// use rtreap::treap::BasicTreap;
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

    /// Returns the number of elements in the treap.
    pub fn len(&self) -> usize {
        self.treap.len()
    }

    /// Returns `true` if the treap is empty.
    pub fn is_empty(&self) -> bool {
        self.treap.is_empty()
    }

    /// Returns an immutable reference to a tuple containing the key and priority
    /// of the node at the root of the treap, or `None` if the treap is empty.
    pub fn peek(&self) -> Option<&(K, P)> {
        if self.treap.is_empty() {
            None
        } else {
            Some(self.treap[self.root].entry())
        }
    }

    /// Performs a binary serach on the Treap to locate the node containing `key`
    /// and returns an immutable reference to a tuple containing its key and
    /// priority, or `None` if the key is not in the treap.
    pub fn search(&self, key: &K) -> Option<&(K, P)> {
        bst::search(&self.treap, self.root, key).map(|i| self.treap[i].entry())
    }

    /// Inserts a new node containing `key` and `priority` into the treap.
    ///
    /// ## Examples:
    ///
    /// ```
    /// use rtreap::treap::BasicTreap;
    ///
    /// let mut treap: BasicTreap<usize, usize, false> = BasicTreap::new();
    /// assert!(treap.insert(123, 456).is_some(), "Treap insertion failed.");
    /// ```
    pub fn insert(&mut self, key: K, priority: P) -> Option<()> {
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
    /// use rtreap::treap::BasicTreap;
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
    pub fn remove(&mut self, key: &K) -> Option<(K, P)> {
        bst::search(&self.treap, self.root, key)
            .map(|i| *remove(&mut self.treap, &mut self.root, self.order, i).entry())
    }

    /// Removes the node containing `key` from the treap and returns a tuple
    /// containing its key and priority. Returns None if `key` does not exist
    /// in the treap.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::BasicTreap;
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
    pub fn update(&mut self, key: &K, new_priority: P) -> Option<P> {
        bst::search(&self.treap, self.root, key).map(|index| {
            update(
                &mut self.treap,
                &mut self.root,
                self.order,
                index,
                new_priority,
            )
        })
    }

    /// Removes the node containing `key` from the treap and returns a tuple
    /// containing its key and priority. Returns None if `key` does not exist
    /// in the treap.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::BasicTreap;
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
    pub fn top(&mut self) -> Option<(K, P)> {
        top(&mut self.treap, &mut self.root, self.order).map(|node| *node.entry())
    }

    /// 
    pub fn merge(&mut self, other: &mut Self) -> bool {
        if other.is_empty() {
            // there is nothing to do
            true
        } else if self.is_empty() {
            // copy the source into the destination
            self.treap.extend(other.treap.iter());
            self.root = other.root;
            true
        } else {
            let self_max: usize = bst::maximum(&mut self.treap, self.root).unwrap();
            let other_min: usize = bst::minimum(&mut other.treap, other.root).unwrap();
            if self.treap[self_max].key() < other.treap[other_min].key() {
                let right_root: usize = bst::extend(&mut self.treap, &other.treap, other.root);
                self.root = merge(&mut self.treap, self.root, right_root, self.order);
                true
            } else {
                let self_min: usize = bst::minimum(&mut self.treap, self.root).unwrap();
                let other_max: usize = bst::maximum(&mut other.treap, other.root).unwrap();
                if other.treap[other_max].key() < self.treap[self_min].key() {
                    let left_root: usize =
                        bst::extend(&mut self.treap, &other.treap, other.root);
                    self.root = merge(&mut self.treap, left_root, self.root, self.order);
                    true
                } else {
                    // the keys in the treaps overlap
                    false
                }
            }
        }
    }
}

/// An implementation of a randomized treap.
///
/// This struct automatically assigns a random priority to each node with the aim of self-balancing the tree.
///
/// Nodes in this treap store both the key and priority. The key is provided as generic parameter
/// `K` but the priority is automatically calculated by hashing the key with the [std::hash::Hash] function.
/// This approach has the advantage of not needing to calculate the priority for each node when making
/// changes to the treap, however, at the cost of using more memory.
///
/// The interface for this implementation is slightly different than [BasicTreap] because several
/// of the methods that are common to a treap are not applicable to a randomized treap by its nature.
/// These include `peek`, `top`, and `update`.
pub struct HashedTreap<K>
where
    K: Ord + Copy + Hash + Default,
{
    treap: Vec<TreapNode<K, u64>>,
    root: usize,
}

impl<K> Default for HashedTreap<K>
where
    K: Ord + Copy + Hash + Default,
{
    /// Creates a new `HashedTreap` object.
    fn default() -> Self {
        Self::new()
    }
}

impl<K> HashedTreap<K>
where
    K: Ord + Copy + Hash + Default,
{
    /// Creates, initializes, and returns a new [HashedTreap] object.
    pub fn new() -> Self {
        Self {
            treap: Vec::new(),
            root: bst::NIL,
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
        }
    }

    /// Returns the index of the root node in the underlying vector.
    pub fn root(&self) -> &K {
        self.treap[self.root].key()
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
    /// use rtreap::treap::BasicTreap;
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
        is_valid(&self.treap, self.root, Ordering::Greater)
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
        bst::search(&self.treap, self.root, key).map(|i| self.treap[i].key())
    }

    /// Inserts a new node containing `key` into the treap.
    ///
    /// ## Examples:
    ///
    /// ```
    /// use rtreap::treap::BasicTreap;
    ///
    /// let mut treap: BasicTreap<usize, usize, false> = BasicTreap::new();
    /// assert!(treap.insert(123, 456).is_some(), "Treap insertion failed.");
    /// ```
    pub fn insert(&mut self, key: K) -> Option<()> {
        let mut state = DefaultHasher::new();
        key.hash(&mut state);
        let priority: u64 = state.finish();
        insert(
            &mut self.treap,
            &mut self.root,
            Ordering::Greater,
            TreapNode::from((key, priority)),
        )
    }

    /// Removes the node containing `key` from the treap and returns the removed node's key.
    /// Returns None if `key` does not exist in the treap.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::BasicTreap;
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
        bst::search(&self.treap, self.root, key)
            .map(|index| *remove(&mut self.treap, &mut self.root, Ordering::Greater, index).key())
    }
}
