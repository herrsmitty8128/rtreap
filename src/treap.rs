// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

/*!
 * Put crate documentation here...
 */

use crate::{bst, heap};
use std::cmp::Ordering;

pub trait Node<K, P>: bst::Node<K> + heap::Priority<P>
where
    Self: Sized,
    K: Ord + Copy,
    P: Ord + Copy,
{
    fn entry(&self) -> &(K, P);
}

#[allow(unused_variables)]
pub trait Treap<K, P, const MAX_HEAP: bool> {
    fn insert(&mut self, key: K, priority: P) -> Option<()>;
    fn remove(&mut self, key: &K) -> Option<(K, P)>;
    fn update(&mut self, key: &K, new_priority: P) -> Option<P> {
        None // update does not apply to all types of treaps
    }
    fn top(&mut self) -> Option<(K, P)>;
    fn peek(&self) -> Option<&(K, P)>;
    fn search(&self, key: &K) -> Option<&(K, P)>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

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
        Some(nodes.pop().unwrap()) // treap.pop() should never panic
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

pub fn update<K, P, N>(
    nodes: &mut Vec<N>,
    root: &mut usize,
    order: Ordering,
    key: &K,
    new_priority: P,
) -> Option<P>
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
{
    if let Some(index) = bst::search(nodes, *root, key) {
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

/// Returns true if the properties of a heap and a bst hold true.
pub fn is_valid<K, P, N>(nodes: &Vec<N>, root: usize, order: Ordering) -> bool
where
    K: Ord + Copy,
    P: Ord + Copy,
    N: Node<K, P>,
{
    !(root >= nodes.len() || !heap::is_valid(nodes, order, root) || !bst::is_valid(nodes, root))
}

#[derive(Debug, Clone, Copy)]
struct TreapNode<K, P>
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
    #[inline]
    fn priority(&self) -> &P {
        &self.entry.1
    }

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
    #[inline]
    fn key(&self) -> &K {
        &self.entry.0
    }

    #[inline]
    fn left(&self) -> usize {
        self.left
    }

    #[inline]
    fn right(&self) -> usize {
        self.right
    }

    #[inline]
    fn parent(&self) -> usize {
        self.parent
    }

    #[inline]
    fn set_left(&mut self, l: usize) {
        self.left = l;
    }

    #[inline]
    fn set_parent(&mut self, p: usize) {
        self.parent = p;
    }

    #[inline]
    fn set_right(&mut self, r: usize) {
        self.right = r;
    }
}

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
    fn default() -> Self {
        Self::new()
    }
}

impl<K, P, const MAX_HEAP: bool> BasicTreap<K, P, MAX_HEAP>
where
    K: Ord + Copy,
    P: Ord + Copy,
{
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

    /// Returns true if the correct priority is on top of the treap.
    /// Please note that this function is intended for use during testing.
    ///
    /// ## Example:
    ///
    /// ```
    /// use rtreap::treap::Treap as TreapTrait;
    /// use rtreap::treap::basic::Treap;
    /// use std::cmp::Ordering;
    ///
    /// let mut v: Vec<usize> = Vec::new();
    /// let mut treap: Treap<usize, usize, false> = Treap::new();
    /// treap.insert(1, 234);
    /// treap.insert(333, 21);
    /// treap.insert(74, 12);
    /// treap.insert(559, 32);
    /// assert!(treap.heap_is_valid());
    /// ```
    #[doc(hidden)]
    pub fn heap_is_valid(&self) -> bool {
        is_valid(&self.treap, self.root, self.order)
    }

    /*pub fn inorder<F>(&self, n: usize, callback: F)
    where
        F: Fn(&K),
    {
        bst::in_order(&self.treap, n, callback);
    }*/
}

impl<K, P, const MAX_HEAP: bool> Treap<K, P, MAX_HEAP> for BasicTreap<K, P, MAX_HEAP>
where
    K: Ord + Copy,
    P: Ord + Copy,
{
    fn len(&self) -> usize {
        self.treap.len()
    }

    fn is_empty(&self) -> bool {
        self.treap.is_empty()
    }

    fn peek(&self) -> Option<&(K, P)> {
        if self.treap.is_empty() {
            None
        } else {
            Some(self.treap[self.root].entry())
        }
    }

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
    /// use rtreap::treap::Treap as TreapTrait;
    /// use rtreap::treap::basic::Treap;
    ///
    /// let mut treap: Treap<usize, usize, false> = Treap::new();
    /// assert!(treap.insert(123, 456).is_ok(), "Treap insertion failed.");
    /// ```
    fn insert(&mut self, key: K, priority: P) -> Option<()> {
        insert(
            &mut self.treap,
            &mut self.root,
            self.order,
            TreapNode::from((key, priority)),
        )
    }

    /*pub fn iter(&self) -> std::slice::Iter<'_, BasicNode<K, P>> {
        self.treap.iter()
    }*/

    fn remove(&mut self, key: &K) -> Option<(K, P)> {
        if let Some(index) = bst::search(&self.treap, self.root, key) {
            if let Some(node) = remove(&mut self.treap, &mut self.root, self.order, index) {
                return Some(*node.entry());
            }
        }
        None
    }

    fn update(&mut self, key: &K, new_priority: P) -> Option<P> {
        update(
            &mut self.treap,
            &mut self.root,
            self.order,
            key,
            new_priority,
        )
    }

    fn top(&mut self) -> Option<(K, P)> {
        top(&mut self.treap, &mut self.root, self.order).map(|x| *x.entry())
    }
}
