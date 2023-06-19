// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

/*!
 * This module implements a priority queue as a heap. It supports:
 *
 * - Maximum heaps
 * - Minimum heaps, without relying on [core::cmp::Reverse] or a custom [std::cmp::Ord] implementation
 * - Binary and d-way heaps. Any number of branches up to (usize::MAX - 1) / d are allowed, so use good judgement!
 *
 * Four generic parameters are consistently used throughout the module:
 *
 * - `P` is any type that implements the [std::cmp::Ord] trait. It is used to determine the order (or, priority) of the nodes in the tree.
 * - `N` is a node in the tree that implements the [Priority] trait and takes `P` as its generic parameter.
 * - `B` is a const usize value that represents the braching factor of the tree (2 for a binary tree, 3 for a ternary tree, etc.).
 * - `MAX_HEAP` is a const bool value that, when `true`, results in a max heap. When `false`, it results in a min heap. This parameter is only present in the [Heap] struct.
 *  
 * Use the [update] method to modify the priority of a node on the heap in such
 * a way that the element's ordering relative to other elements is changed. Modifying
 * an element's value through other means may result in inconsistencies, logic errors,
 * panics, or other unintended consequences.
*/

use std::{
    cmp::{Ord, Ordering},
    marker::PhantomData,
    ops::Index,
};

/// A trait used to standardize the interface for objects stored in a heap.
pub trait Priority<P>
where
    Self: Sized,
{
    /// Returns an immutable reference to the nodes priority.
    fn priority(&self) -> &P;

    /// Sets the nodes priority to `new_priority`.
    fn set_priority(&mut self, new_priority: P);
}


/// A struct that implements the `Priority` trait. This struct is provided for
/// convenience to make it a little easier to work with the functions in this
/// module. It is intended to be used as a wrapper for other types that 
/// implement the `Ord` and `Copy` traits.
/// 
/// ## Example:
/// 
/// ```
/// use rtreap::heap::{HeapNode, Priority};
/// 
/// type MyNode = HeapNode<usize>;
/// 
/// ```
#[derive(Debug, Clone, Copy)]
pub struct HeapNode<P>
where
    P: Ord + Copy,
{
    priority: P,
}

impl<P> PartialEq for HeapNode<P>
where
    P: Ord + Copy,
{
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl<P> From<P> for HeapNode<P>
where
    P: Ord + Copy,
{
    fn from(priority: P) -> Self {
        Self { priority }
    }
}

impl<P> Priority<P> for HeapNode<P>
where
    P: Ord + Copy,
{
    fn priority(&self) -> &P {
        &self.priority
    }

    fn set_priority(&mut self, new_priority: P) {
        self.priority = new_priority;
    }
}

/// Returns true if the correct value is on top of the heap.
/// This function is primarily used for testing.
pub fn is_valid<P, N>(heap: &[N], order: Ordering) -> bool
where
    P: Ord,
    N: Priority<P>,
{
    for i in 1..heap.len() {
        if heap[i].priority().cmp(&heap[0].priority()) == order {
            return false;
        }
    }
    true
}

/// Modifies the priority of an element on the heap in such a way that its
/// ordering relative to other elements is changed. It returns `Some(P)`
/// containing the old priority, or None if `index` is out of bounds.
///
/// ## Arguments:
///
/// - `heap` - A mutable reference to a slice of nodes sorted as a heap.
/// - `index` - The index of the node in the tree whose priority you'd like to update.
/// - `order` - A value indicating if `heap` is sorted as a min or max heap. Pass [std::cmp::Ordering::Greater] for a max heap or [std::cmp::Ordering::Less] for a min heap.
/// - `new_priority` - The new priority to assign to the node located at `index` in the `heap`.
///
/// ## Example:
///
/// ```
/// use rtreap::heap::{HeapNode, Priority, update, sort, is_valid};
/// use std::cmp::Ordering;
/// use rand::prelude::*;
///
/// type MyNode = HeapNode<usize>;
///
/// let mut heap: Vec<MyNode> = Vec::new();
/// for _ in 0..100 {
///     heap.push(MyNode::from(rand::random::<usize>()));
/// }
///
/// // sort the vector as a max heap
/// sort::<usize, MyNode, 2>(&mut heap, Ordering::Greater);
///
/// // update the priority of the node at index 23
/// update::<usize, MyNode, 2>(&mut heap, 23, Ordering::Greater, 12345).unwrap();
///
/// // verify that the heap properties still apply
/// assert!(is_valid(&mut heap, Ordering::Greater));
///
/// /// // sort the vector as a min heap
/// sort::<usize, MyNode, 2>(&mut heap, Ordering::Less);
///
/// // update the priority of the node at index 18
/// update::<usize, MyNode, 2>(&mut heap, 18, Ordering::Less, 54321).unwrap();
///
/// // verify that the heap properties still apply
/// assert!(is_valid(&mut heap, Ordering::Less));
/// ```
pub fn update<P, N, const B: usize>(
    heap: &mut [N],
    index: usize,
    order: Ordering,
    new_priority: P,
) -> Option<P>
where
    P: Ord + Copy,
    N: Priority<P>,
{
    let len: usize = heap.len();
    if index < len {
        let old_priority: P = *heap[index].priority();
        if new_priority.cmp(&old_priority) == order {
            bubble_up::<P, N, B>(heap, order, index);
        } else {
            push_down::<P, N, B>(heap, order, index);
        }
        Some(old_priority)
    } else {
        None
    }
}

/// Updates the order of the nodes in the heap starting from `index` and going down the tree.
pub fn push_down<P, N, const B: usize>(heap: &mut [N], order: Ordering, mut index: usize)
where
    P: Ord,
    N: Priority<P>,
{
    let length: usize = heap.len();
    loop {
        let first_child: usize = (index * B) + 1;
        let last_child: usize = first_child + B;
        let mut p: usize = index;
        for c in first_child..last_child.min(length) {
            if heap[c].priority().cmp(heap[p].priority()) == order {
                p = c
            };
            /*p = if heap[p].priority().cmp(heap[i].priority()) == order {
                p
            } else {
                i
            };*/
        }
        if p == index {
            break;
        }
        heap.swap(p, index);
        index = p;
    }
}

/// Removes and returns the element at `index` from the heap. Returns `None` if `index` is
/// out of bounds or the heap is empty.
///
/// ## Arguments:
///
/// - `heap` - A mutable reference to a slice of nodes sorted as a heap.
/// - `index` - The index of the node in the tree whose priority you'd like to update.
/// - `order` - A value indicating if `heap` is sorted as a min or max heap. Pass [std::cmp::Ordering::Greater] for a max heap or [std::cmp::Ordering::Less] for a min heap.
///
/// ## Example:
///
/// ```
/// use rtreap::heap::{HeapNode, Priority, insert, remove, is_valid};
/// use std::cmp::Ordering;
/// use rand::prelude::*;
///
/// type MyNode = HeapNode<usize>;
///
/// let mut heap: Vec<MyNode> = Vec::new();
/// for _ in 0..100 {
///     insert::<usize, MyNode, 2>(&mut heap, Ordering::Less, MyNode::from(rand::random::<usize>()));
/// }
///
/// // verify the length of the heap
/// assert!(heap.len() == 100);
///
/// // verify that the heap properties still apply
/// assert!(is_valid(&mut heap, Ordering::Less));
///
/// while !heap.is_empty() {
///     let index: usize = rand::thread_rng().gen_range(0..heap.len());
///     let len: usize = heap.len();
///     remove::<usize, MyNode, 2>(&mut heap, Ordering::Less, index);
///     assert!(heap.len() == len - 1);
///     assert!(is_valid(&mut heap, Ordering::Less));
/// }
/// ```
pub fn remove<P, N, const B: usize>(heap: &mut Vec<N>, order: Ordering, index: usize) -> Option<N>
where
    P: Ord,
    N: Priority<P>,
{
    let len: usize = heap.len();
    if index < len {
        let removed: N = heap.swap_remove(index);
        if index < len - 1 {
            if heap[index].priority().cmp(removed.priority()) == order {
                bubble_up::<P, N, B>(heap, order, index);
            } else {
                push_down::<P, N, B>(heap, order, index);
            }
        }
        Some(removed)
    } else {
        None
    }
}

/// Updates the order of the nodes in the heap starting from `index` and going up the tree to the root.
pub fn bubble_up<P, N, const B: usize>(heap: &mut [N], order: Ordering, mut index: usize)
where
    P: Ord,
    N: Priority<P>,
{
    while index > 0 {
        let p: usize = (index - 1) / B; // calculate the index of the parent node
        if heap[index].priority().cmp(heap[p].priority()) == order {
            heap.swap(index, p); // if the child is smaller than the parent, then swap them
        } else {
            break;
        }
        index = p;
    }
}

/// Inserts `element` into the heap.
///
/// ## Arguments:
///
/// - `heap` - A mutable reference to a slice of nodes sorted as a heap.
/// - `order` - A value indicating if `heap` is sorted as a min or max heap. Pass [std::cmp::Ordering::Greater] for a max heap or [std::cmp::Ordering::Less] for a min heap.
/// - `element` - The new element to insert into the the `heap`. The element must implement the `Priority` trait.
///
/// ## Example:
///
/// ```
/// use rtreap::heap::{HeapNode, Priority, insert, is_valid};
/// use std::cmp::Ordering;
/// use rand::prelude::*;
///
/// type MyNode = HeapNode<usize>;
///
/// let mut heap: Vec<MyNode> = Vec::new();
/// for _ in 0..100 {
///     insert::<usize, MyNode, 2>(&mut heap, Ordering::Less, MyNode::from(rand::random::<usize>()));
/// }
///
/// // verify the length of the heap
/// assert!(heap.len() == 100);
///
/// // verify that the heap properties still apply
/// assert!(is_valid(&mut heap, Ordering::Less));
/// ```
pub fn insert<P, N, const B: usize>(heap: &mut Vec<N>, order: Ordering, element: N)
where
    P: Ord,
    N: Priority<P>,
{
    let index: usize = heap.len();
    heap.push(element);
    bubble_up::<P, N, B>(heap, order, index);
}

/// Removes and returns the element on the top of the heap. Returns `None` if the heap is empty.
pub fn top<P, N, const B: usize>(heap: &mut Vec<N>, order: Ordering) -> Option<N>
where
    P: Ord,
    N: Priority<P>,
{
    if heap.is_empty() {
        None
    } else {
        let removed: N = heap.swap_remove(0);
        push_down::<P, N, B>(heap, order, 0);
        Some(removed)
    }
}

/// Performs an in-place heap sort on a slice of objects that implement the `Priority` trait.
pub fn sort<P, N, const B: usize>(heap: &mut [N], order: Ordering)
where
    P: Ord,
    N: Priority<P>,
{
    let len: usize = heap.len();
    if len > 1 {
        let parent: usize = (len - 2) / B;
        for index in (0..=parent).rev() {
            push_down::<P, N, B>(heap, order, index);
        }
    }
}

/// A minimum heap with branching factor of 2.
pub type BinaryMinHeap<P, N> = Heap<P, N, 2, false>;

/// A maximum heap with branching factor of 2.
pub type BinaryMaxHeap<P, N> = Heap<P, N, 2, true>;

/// A minimum heap with branching factor of 3.
pub type TernaryMinHeap<P, N> = Heap<P, N, 3, false>;

/// A maximum heap with branching factor of 3.
pub type TernaryMaxHeap<P, N> = Heap<P, N, 3, true>;

/// A minimum heap with branching factor of 4.
pub type QuaternaryMinHeap<P, N> = Heap<P, N, 4, false>;

/// A maximum heap with branching factor of 4.
pub type QuaternaryMaxHeap<P, N> = Heap<P, N, 4, true>;

/// A minimum heap with branching factor of 5.
pub type QuinaryMinHeap<P, N> = Heap<P, N, 5, false>;

/// A maximum heap with branching factor of 5.
pub type QuinaryMaxHeap<P, N> = Heap<P, N, 5, true>;

/// A complete binary tree in which the value of each node in the tree is either
/// less than (in the case of a minimum heap) or greater than (in the case of a
/// maximum heap) the value of each of its children. As a consequence, either the
/// smallest or largest value in the tree is always located at the root of the tree.
#[derive(Debug, Clone)]
pub struct Heap<P, N, const B: usize, const MAX_HEAP: bool>
where
    P: Ord,
    N: Priority<P>,
{
    heap: Vec<N>,
    order: Ordering,
    _p: PhantomData<P>,
}

impl<P, N, const B: usize, const MAX_HEAP: bool> Index<usize> for Heap<P, N, B, MAX_HEAP>
where
    P: Ord,
    N: Priority<P>,
{
    type Output = N;
    fn index<'a>(&'a self, index: usize) -> &'a Self::Output {
        &self.heap[index]
    }
}

impl<P, N, const B: usize, const MAX_HEAP: bool> Default for Heap<P, N, B, MAX_HEAP>
where
    P: Ord,
    N: Priority<P>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<P, N, const B: usize, const MAX_HEAP: bool> From<&[N]> for Heap<P, N, B, MAX_HEAP>
where
    P: Ord,
    N: Priority<P> + Clone,
{
    /// Builds a new Heap object from a slice of type N<P> by cloning the elements in the slice.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::{Heap, Priority, BinaryMinHeap, BinaryMaxHeap, HeapNode};
    /// use std::cmp::Ordering;
    /// use rand::prelude::*;
    ///  
    /// type MyNode = HeapNode<usize>;
    ///
    /// let mut v: Vec<MyNode> = Vec::new();
    /// for i in 0..100 {
    ///     v.push(MyNode::from(rand::thread_rng().gen_range(0..10000)))
    /// }
    ///
    /// let mut heap: BinaryMinHeap<usize, MyNode> = Heap::from(&v[..]);
    /// assert!(heap.is_valid());
    /// assert!(heap.order() == Ordering::Less);
    ///
    /// let mut heap: BinaryMaxHeap<usize, MyNode> = Heap::from(&v[..]);
    /// assert!(heap.is_valid());
    /// assert!(heap.order() == Ordering::Greater);
    ///
    /// assert!(heap.len() == v.len())
    /// ```
    fn from(s: &[N]) -> Self {
        let mut heap: Vec<N> = Vec::from(s);
        let order: Ordering = if MAX_HEAP {
            Ordering::Greater
        } else {
            Ordering::Less
        };
        sort::<P, N, B>(&mut heap, order);
        Self {
            heap,
            order,
            _p: PhantomData,
        }
    }
}

impl<P, N, const B: usize, const MAX_HEAP: bool> Heap<P, N, B, MAX_HEAP>
where
    P: Ord,
    N: Priority<P>,
{
    /// Constructs a new, empty heap.
    /// The new heap will allocate memory as elements are inserted.
    pub fn new() -> Self {
        Self {
            heap: Vec::new(),
            order: if MAX_HEAP {
                Ordering::Greater
            } else {
                Ordering::Less
            },
            _p: PhantomData,
        }
    }

    /// Constructs a new, empty heap with at least the specified capacity.
    /// The heap will be able to hold at least capacity elements without reallocating.
    /// This method is allowed to allocate for more elements than capacity.
    /// If capacity is 0, the heap will not allocate.
    /// It is important to note that although the returned heap has the minimum capacity specified, the heap will have a zero length.
    /// If it is important to know the exact allocated capacity of a heap, always use the [`Heap::capacity`] method after construction.
    /// For heap where T is a zero-sized type, there will be no allocation and the capacity will always be [`usize::MAX`].
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            heap: Vec::with_capacity(capacity),
            order: if MAX_HEAP {
                Ordering::Greater
            } else {
                Ordering::Less
            },
            _p: PhantomData,
        }
    }

    /// Moves all the elements of other into self, leaving other empty.
    pub fn append(&mut self, other: &mut Self) {
        self.heap.append(&mut other.heap);
        sort::<P, N, B>(&mut self.heap, self.order)
    }

    /// Returns the number of elements the heap can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.heap.capacity()
    }

    /// Returns a slice containing the entire underlying vector.
    pub fn as_slice(&self) -> &[N] {
        self.heap.as_slice()
    }

    /// Returns an iterator over the slice.
    /// The iterator yields all items from start to end.
    pub fn iter(&self) -> std::slice::Iter<'_, N> {
        self.heap.iter()
    }

    /// Shortens the vector, keeping the first `len` elements and dropping the rest.
    /// If len is greater than the vector's current length, this has no effect.
    /// Note that this method has no effect on the allocated capacity of the vector.
    pub fn truncate(&mut self, len: usize) {
        self.heap.truncate(len)
    }

    /// Returns the sort order of the heap.
    /// `Ordering::Greater` indicates a maximum heap.
    /// `Ordering::Less` indicates a minimum heap.
    pub fn order(&self) -> Ordering {
        self.order
    }

    /// Clears the heap, removing all elements.
    /// Note that this method has no effect on the allocated capacity of the heap.
    pub fn clear(&mut self) {
        self.heap.clear()
    }

    /// Performs a linear search (in O(n) time) to find the index of an element on the heap.
    /// Returns `None` if the element was not found.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::{Heap, BinaryMinHeap, HeapNode, Priority};
    /// use rand::prelude::*;
    ///
    /// type MyNode = HeapNode<usize>;
    ///
    /// let mut v: Vec<MyNode> = Vec::new();
    /// for i in 0..100 {
    ///     v.push(MyNode::from(rand::thread_rng().gen_range(0..10000)));
    /// }
    ///
    /// let mut heap: BinaryMinHeap<usize, MyNode> = Heap::from(&v[..]);
    ///
    /// let index = heap.find(&v[0]).expect("Did not find the node.");
    ///
    /// assert!(heap[index] == v[0]);
    /// ```
    pub fn find(&self, element: &N) -> Option<usize>
    where
        N: Priority<P> + std::cmp::PartialEq,
    {
        (0..self.heap.len()).find(|&i| self.heap[i] == *element)
    }

    /// Inserts an element into the heap.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::{Heap, HeapNode, Priority, BinaryMaxHeap};
    /// use std::cmp::Ordering;
    ///
    /// type MyNode = HeapNode<usize>;
    /// let mut heap: BinaryMaxHeap<usize, MyNode> = BinaryMaxHeap::new();
    ///
    /// heap.insert(MyNode::from(0));
    /// heap.insert(MyNode::from(2));
    /// heap.insert(MyNode::from(4));
    /// heap.insert(MyNode::from(5));
    /// heap.insert(MyNode::from(8));
    /// heap.insert(MyNode::from(10));
    ///
    /// let x = heap.peek().unwrap();
    ///
    /// assert!(*x.priority() == 10, "peek(0) returned {} instead of 10", *x.priority());
    /// ```
    pub fn insert(&mut self, element: N) {
        insert::<P, N, B>(&mut self.heap, self.order, element)
    }

    /// Returns true if the heap contains no elements.
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    /// Returns the number of elements in the heap, also referred to as its 'length'.
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    /// Returns an immutable reference to the element on top of the heap without removing it or `None` if the heap is empty.
    pub fn peek(&self) -> Option<&N> {
        if self.heap.is_empty() {
            None
        } else {
            Some(&self.heap[0])
        }
    }

    /// Removes and returns the element at `index`.
    /// Returns an error if the heap is empty or if the index is out of bounds.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::{Heap, HeapNode, Priority, BinaryMaxHeap};
    /// use rand::prelude::*;
    /// use std::cmp::Ordering;
    ///
    /// type MyNode = HeapNode<usize>;
    /// let mut v: Vec<MyNode> = Vec::new();
    /// let mut heap: BinaryMaxHeap<usize, MyNode> = BinaryMaxHeap::new();
    /// for i in 0..100 {
    ///     heap.insert(MyNode::from(rand::thread_rng().gen_range(0..10000)));
    /// }
    ///
    /// let removed_node = heap[23];
    ///
    /// let old_element = heap.remove(23).unwrap();
    /// assert!(old_element == removed_node);
    /// assert!(heap.is_valid());
    /// ```
    pub fn remove(&mut self, index: usize) -> Option<N> {
        remove::<P, N, B>(&mut self.heap, self.order, index)
    }

    /// Removes and returns the element from the top of the heap. Returns `None` if the heap is empty.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::{Heap, HeapNode, Priority, BinaryMaxHeap};
    /// use rand::prelude::*;
    /// use std::cmp::Ordering;
    ///
    /// type MyNode = HeapNode<usize>;
    /// let mut nums: [usize; 10] = [1, 0, 2, 9, 3, 8, 4, 7, 5, 6];
    /// let mut heap: BinaryMaxHeap<usize, MyNode> = BinaryMaxHeap::new();
    /// for n in nums {
    ///     heap.insert(MyNode::from(n));
    /// }
    ///
    /// assert!(*heap.top().unwrap().priority() == 9);
    /// ```
    pub fn top(&mut self) -> Option<N> {
        top::<P, N, B>(&mut self.heap, self.order)
    }

    /// Updates the value (or "priority") of the element at `index`.
    /// Returns an error if the element is not found in the heap or the index is out of bounds.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::Heap;
    /// use std::cmp::Ordering;
    ///
    /// let mut v: Vec<usize> = vec![0, 2, 4, 6, 8, 10];
    ///
    /// let mut heap: Heap<usize, false, 3> = Heap::from(&v[..]);
    ///
    /// if heap.update(3, |x| *x = 11).is_err() {
    ///     panic!();
    /// }
    ///
    /// assert!(heap.is_valid());
    /// ```
    pub fn update(&mut self, index: usize, new_priority: P) -> Option<P>
    where
        P: Ord + Copy,
    {
        update::<P, N, B>(&mut self.heap, index, self.order, new_priority)
    }

    /// Returns true if the correct value is on top of the heap.
    /// Please note that this function is intended for use during testing.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::Heap;
    /// use std::cmp::Ordering;
    ///
    /// let mut v: Vec<usize> = Vec::new();
    /// let mut heap: Heap<usize, false, 3> = Heap::from(&v[..]);
    /// assert!(heap.is_valid());
    /// ```
    #[doc(hidden)]
    pub fn is_valid(&self) -> bool {
        is_valid(&self.heap, self.order)
    }
}
