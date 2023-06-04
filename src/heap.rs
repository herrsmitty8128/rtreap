// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

/*!
 * `heap` is a Rust library containing an implementation of a minimum, maximum, d-way heap.
 *
 * It supports:
 *
 * - Maximum heaps
 * - Minimum heaps, without relying on [`core::cmp::Reverse`] or a custom [`std::cmp::Ord`] implementation
 * - Binary and d-way heaps. Any number of branches up to (usize::MAX - 1) / d are allowed, so use good judgement!
 *  
 * Use the [`Heap::update`] method to modify the value of an element on the heap in such
 * a way that the element's ordering relative to other elements is changed. Modifying
 * an element's value through other means may result in a inconsistencies, logic errors,
 * panics, or other unintended consequences.
*/

use std::cmp::{Ord, Ordering};
use crate::error::{Error, ErrorKind, Result};

/// A minimum heap with branching factor of 2.
pub type BinaryMinHeap<T> = Heap<T, false, 2>;

/// A maximum heap with branching factor of 2.
pub type BinaryMaxHeap<T> = Heap<T, true, 2>;

/// A minimum heap with branching factor of 3.
pub type TernaryMinHeap<T> = Heap<T, false, 3>;

/// A maximum heap with branching factor of 3.
pub type TernaryMaxHeap<T> = Heap<T, true, 3>;

/// A minimum heap with branching factor of 4.
pub type QuaternaryMinHeap<T> = Heap<T, false, 4>;

/// A maximum heap with branching factor of 4.
pub type QuaternaryMaxHeap<T> = Heap<T, true, 4>;

/// A minimum heap with branching factor of 5.
pub type QuinaryMinHeap<T> = Heap<T, false, 5>;

/// A maximum heap with branching factor of 5.
pub type QuinaryMaxHeap<T> = Heap<T, true, 5>;

/// A complete binary tree in which the value of each node in the tree is either
/// less than (in the case of a minimum heap) or greater than (in the case of a
/// maximum heap) the value of each of its children. As a consequence, either the
/// smallest or largest value in the tree is always located at the root of the tree.
#[derive(Debug, Clone)]
pub struct Heap<T, const MAX_HEAP: bool, const BRANCHES: usize>
where
    T: Ord + Eq + Copy,
{
    heap: Vec<T>,
    sort_order: Ordering,
}

impl<T, const MAX_HEAP: bool, const BRANCHES: usize> From<&[T]> for Heap<T, MAX_HEAP, BRANCHES>
where
    T: Ord + Eq + Copy,
{
    /// Builds a new Heap object from a slice of type T by cloning the elements in the slice.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::Heap;
    /// use std::cmp::Ordering;
    ///
    /// let mut v: Vec<usize> = vec![11, 6, 8, 5, 9, 1, 4, 2, 2, 2, 3, 4, 23, 2, 0, 77];
    ///
    /// let mut heap: Heap<usize, false, 2> = Heap::from(&v[..]);
    /// assert!(heap.is_valid());
    /// assert!(heap.sort_order() == Ordering::Less);
    ///
    /// let mut heap: Heap<usize, true, 2> = Heap::from(&v[..]);
    /// assert!(heap.is_valid());
    /// assert!(heap.sort_order() == Ordering::Greater);
    ///
    /// assert!(heap.len() == v.len())
    /// ```
    fn from(s: &[T]) -> Self {
        let mut heap: Vec<T> = Vec::from(s);
        let sort_order: Ordering = if MAX_HEAP {
            Ordering::Greater
        } else {
            Ordering::Less
        };
        Heap::<T, MAX_HEAP, BRANCHES>::heap_sort(&mut heap[..]);
        Self { heap, sort_order }
    }
}

impl<T, const MAX_HEAP: bool, const BRANCHES: usize> Heap<T, MAX_HEAP, BRANCHES>
where
    T: Ord + Eq + Copy,
{
    
    /// Constructs a new, empty heap.
    /// The new heap will allocate memory as elements are inserted.
    pub fn new() -> Self {
        Self {
            heap: Vec::new(),
            sort_order: if MAX_HEAP {
                Ordering::Greater
            } else {
                Ordering::Less
            },
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
            sort_order: if MAX_HEAP {
                Ordering::Greater
            } else {
                Ordering::Less
            },
        }
    }

    /// Moves all the elements of other into self, leaving other empty.
    pub fn append(&mut self, other: &mut Self) {
        self.heap.append(&mut other.heap);
        Self::heap_sort(&mut self.heap);
    }

    /// Returns the number of elements the heap can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.heap.capacity()
    }

    /// Returns a slice containing the entire underlying vector.
    pub fn as_slice(&self) -> &[T] {
        self.heap.as_slice()
    }

    /// Returns an iterator over the slice.
    /// The iterator yields all items from start to end.
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
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
    pub fn sort_order(&self) -> Ordering {
        self.sort_order
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
    /// use rtreap::heap::Heap;
    ///
    /// let mut v: Vec<usize> = vec![0, 2, 4, 6, 8, 10];
    ///
    /// let mut heap: Heap<usize, false, 2> = Heap::from(&v[..]);
    ///
    /// if let Some(index) = heap.find(&6) {
    ///     assert!(index == 3);
    /// } else {
    ///     panic!("Did not find the number 6.");
    /// }
    /// ```
    pub fn find(&self, element: &T) -> Option<usize> {
        (0..self.heap.len()).find(|&i| self.heap[i] == *element)
    }

    /// Inserts an element into the heap.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::Heap;
    /// use std::cmp::Ordering;
    ///
    /// let mut v: Vec<usize> = vec![0, 2, 4, 6, 8, 10];
    ///
    /// let mut heap: Heap<usize, false, 2> = Heap::from(&v[..]);
    ///
    /// heap.insert(5);
    ///
    /// if let Some(x) = heap.peek() {
    ///     assert!(*x == 0)
    /// } else {
    ///     panic!("heap.peek() returned None.")
    /// }
    /// ```
    pub fn insert(&mut self, element: T) {
        let index: usize = self.heap.len();
        self.heap.push(element);
        Self::sort_up(&mut self.heap, self.sort_order, index)
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
    pub fn peek(&self) -> Option<&T> {
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
    /// use rtreap::heap::Heap;
    /// use std::cmp::Ordering;
    ///
    /// let mut v: Vec<usize> = vec![0, 2, 4, 6, 8, 10];
    ///
    /// let mut heap: Heap<usize, false, 2> = Heap::from(&v[..]);
    ///
    /// if let Ok(old_element) = heap.remove(3) {
    ///     assert!(old_element == 6);
    ///     assert!(heap.is_valid());
    /// } else {
    ///     panic!("Heap.remove() returned an error.");
    /// }
    /// ```
    pub fn remove(&mut self, index: usize) -> Result<T> {
        if self.heap.is_empty() {
            Err(Error::new(
                ErrorKind::EmptyHeap,
                "Can not remove elements from an empty heap.",
            ))
        } else if index >= self.heap.len() {
            Err(Error::new(
                ErrorKind::IndexOutOfBounds,
                "Index is beyond the end of the heap.",
            ))
        } else {
            let removed: T = self.heap.swap_remove(index);
            if index < self.heap.len() {
                if self.heap[index].cmp(&removed) == self.sort_order {
                    Self::sort_up(&mut self.heap, self.sort_order, index);
                } else {
                    Self::sort_down(&mut self.heap, self.sort_order, index);
                }
            }
            Ok(removed)
        }
    }

    /// Removes and returns the element from the top of the heap. Returns `None` if the heap is empty.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::Heap;
    /// use std::cmp::Ordering;
    ///
    /// let mut v: Vec<usize> = vec![0, 2, 4, 6, 8, 10];
    ///
    /// let mut heap: Heap<usize, false, 2> = Heap::from(&v[..]);
    ///
    /// if let Some(smallest) = heap.top() {
    ///     assert!(smallest == 0);
    /// } else {
    ///     panic!();
    /// }
    /// ```
    pub fn top(&mut self) -> Option<T> {
        if self.heap.is_empty() {
            None
        } else {
            let removed: T = self.heap.swap_remove(0);
            Self::sort_down(&mut self.heap, self.sort_order, 0);
            Some(removed)
        }
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
    #[inline]
    pub fn update<F>(&mut self, index: usize, modifier: F) -> Result<()>
    where
        F: Fn(&mut T),
    {
        if self.heap.is_empty() {
            Err(Error::new(
                ErrorKind::EmptyHeap,
                "Can not remove elements from an empty heap.",
            ))
        } else if index >= self.heap.len() {
            Err(Error::new(
                ErrorKind::IndexOutOfBounds,
                "Index is beyond the end of the heap.",
            ))
        } else {
            modifier(&mut self.heap[index]);
            if index == 0
                || self.heap[index].cmp(&self.heap[(index - 1) / BRANCHES]) != self.sort_order
            {
                Self::sort_down(&mut self.heap, self.sort_order, index);
            } else {
                Self::sort_up(&mut self.heap, self.sort_order, index);
            }
            Ok(())
        }
    }

    /// Sorts the heap by iterating down the tree starting at `index`.
    ///
    /// ## Panics:
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::Heap;
    /// use std::cmp::Ordering;
    ///
    /// let mut heap: Vec<usize> = vec![0, 1, 2, 3, 4, 5];
    ///
    /// // remove the element located at index 0
    /// let index: usize = 0;
    /// heap.swap_remove(index);
    /// Heap::<usize, false, 3>::sort_down(&mut heap, Ordering::Less, index);
    /// assert!(heap[0] == 1);
    /// ```
    pub fn sort_down(heap: &mut [T], sort_order: Ordering, mut index: usize)
    where
        T: Ord,
    {
        let length: usize = heap.len();
        loop {
            let first_child: usize = (index * BRANCHES) + 1;
            let last_child: usize = first_child + BRANCHES;
            let mut priority: usize = index;
            for i in first_child..last_child.min(length) {
                priority = if heap[priority].cmp(&heap[i]) == sort_order {
                    priority
                } else {
                    i
                };
            }
            if priority == index {
                break;
            }
            heap.swap(priority, index);
            index = priority;
        }
    }

    /// Sorts the heap by iterating up the tree starting at `index`.
    ///
    /// ## Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::Heap;
    /// use std::cmp::Ordering;
    ///
    /// let mut heap: Vec<usize> = vec![0, 2, 4, 6, 8, 10];
    /// let index: usize = heap.len();
    /// heap.push(5);
    /// Heap::<usize, false, 3>::sort_up(&mut heap, Ordering::Less, index);
    /// assert!(heap[0] == 0);
    /// ```
    pub fn sort_up(heap: &mut [T], sort_order: Ordering, mut index: usize)
    where
        T: Ord,
    {
        while index > 0 {
            let p: usize = (index - 1) / BRANCHES; // calculate the index of the parent node
            if heap[index].cmp(&heap[p]) == sort_order {
                heap.swap(index, p); // if the child is smaller than the parent, then swap them
            } else {
                break;
            }
            index = p;
        }
    }

    /// Performs an in-place heap sort.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::heap::Heap;
    /// use std::cmp::Ordering;
    ///
    /// let mut heap: Vec<usize> = vec![8, 66, 9, 55, 7, 0, 14, 6, 37, 2];
    /// Heap::<usize, false, 3>::heap_sort(&mut heap);
    /// assert!(heap[0] == 0);
    /// ```
    pub fn heap_sort(heap: &mut [T])
    where
        T: Ord,
    {
        let len: usize = heap.len();
        if len > 1 {
            let sort_order: Ordering = if MAX_HEAP {
                Ordering::Greater
            } else {
                Ordering::Less
            };
            let parent: usize = (len - 2) / BRANCHES;
            for index in (0..=parent).rev() {
                Self::sort_down(heap, sort_order, index);
            }
        }
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
        for i in 1..self.heap.len() {
            if self.heap[i].cmp(&self.heap[0]) == self.sort_order {
                return false;
            }
        }
        true
    }
}
