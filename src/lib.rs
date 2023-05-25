// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

/*!
 * Put crate documentation here...
 */

use std::cmp::Ordering;

#[derive(Debug, Copy, Clone)]
pub enum ErrorKind {
    RotationError,
    IndexOutOfBounds,
}

impl std::fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            ErrorKind::IndexOutOfBounds => f.write_str("Index out of bounds"),
            ErrorKind::RotationError => f.write_str("Rotation error"),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Error {
    kind: ErrorKind,
    message: &'static str,
}

impl Error {
    pub fn new(kind: ErrorKind, message: &'static str) -> Self {
        Self { kind, message }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{} {}", self.kind.to_string(), self.message))
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// Value used as a sentinel.
pub const NIL: usize = usize::MAX;

#[derive(Debug, Copy, Clone)]
pub struct Node<K, P>
where
    K: Copy + Eq + PartialEq + Ord,
    P: Copy + Eq + PartialEq + Ord,
{
    parent: usize,
    left: usize,
    right: usize,
    key: K,
    priority: P,
}

impl<K, P> Node<K, P>
where
    K: Copy + Eq + PartialEq + Ord,
    P: Copy + Eq + PartialEq + Ord,
{
    pub fn new(key: K, priority: P) -> Self {
        Self {
            parent: NIL,
            left: NIL,
            right: NIL,
            key,
            priority,
        }
    }

    pub fn is_leaf(&self) -> bool {
        if self.left == NIL && self.right == NIL {
            true
        } else {
            false
        }
    }

    pub fn is_root(&self) -> bool {
        self.parent == NIL
    }
}

#[derive(Debug, Clone)]
pub struct Treap<K, P>
where
    K: Copy + Eq + PartialEq + Ord,
    P: Copy + Eq + PartialEq + Ord,
{
    treap: Vec<Node<K, P>>,
    root: usize,
}

impl<K, P> Treap<K, P>
where
    K: Copy + Eq + PartialEq + Ord,
    P: Copy + Eq + PartialEq + Ord,
{
    pub fn new() -> Self {
        Self {
            treap: Vec::new(),
            root: NIL,
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            treap: Vec::with_capacity(capacity),
            root: NIL,
        }
    }

    pub fn len(&self) -> usize {
        self.treap.len()
    }

    pub fn is_empty(&self) -> bool {
        self.treap.is_empty()
    }

    pub fn peek(&self) -> Option<&P> {
        if self.treap.is_empty() {
            None
        } else {
            Some(&self.treap[self.root].priority)
        }
    }

    pub fn search(&self, key: &K) -> Option<usize> {
        let mut n: usize = self.root;
        while n < self.treap.len() {
            match self.treap[n].key.cmp(key) {
                Ordering::Equal => return Some(n),
                Ordering::Less => n = self.treap[n].left,
                Ordering::Greater => n = self.treap[n].right,
            };
        }
        None
    }

    fn rotate_right(&mut self, n: usize) {
        let treap_size: usize = self.treap.len();
        if n < treap_size {
            let l: usize = self.treap[n].left;
            if l < treap_size {
                let p: usize = self.treap[n].parent;
                self.treap[l].parent = p;
                // fix the parent node pointer
                if p < treap_size {
                    if n == self.treap[p].left {
                        self.treap[p].left = l;
                    } else {
                        self.treap[p].right = l;
                    }
                } else {
                    self.root = l;
                }
                self.treap[n].parent = l;

                let r: usize = self.treap[l].right;
                self.treap[n].left = r;
                if r < treap_size {
                    self.treap[r].parent = n;                
                }

                self.treap[l].right = n;
            }
        }
    }

    fn rotate_left(&mut self, n: usize) {
        let treap_size: usize = self.treap.len();
        if n < treap_size {
            let r: usize = self.treap[n].right;
            if r < treap_size {
                let p: usize = self.treap[n].parent;
                self.treap[r].parent = p;
                if p < treap_size {
                    if n == self.treap[p].left {
                        self.treap[p].left = r;
                    } else {
                        self.treap[p].right = r;
                    }
                } else {
                    self.root = r;
                }
                self.treap[n].parent = r;

                let l: usize = self.treap[r].left;
                self.treap[n].right = l;
                if l < treap_size {
                    self.treap[l].parent = n;                
                }
                
                self.treap[r].left = n;
            }
        }
    }
    
    pub fn insert(&mut self, key: K, priority: P) -> Result<()> {
        let new_node: usize = self.treap.len();
        self.treap.push(Node::new(key, priority));
        if self.treap.len() == 1 {
            self.root = new_node;
        } else {
            let mut node: usize = self.root;
            let mut parent: usize = NIL;
            while node != NIL {
                parent = node;
                node = if self.treap[node].key <= key {
                    self.treap[node].left
                } else {
                    self.treap[node].right
                };
            }
            if key <= self.treap[parent].key {
                self.treap[parent].left = new_node;
            } else {
                self.treap[parent].right = new_node;
            }
            self.treap[new_node].parent = parent;
            while self.treap[new_node].parent != NIL
                && self.treap[new_node].priority < self.treap[self.treap[new_node].parent].priority
            {
                let p: usize = self.treap[new_node].parent;
                if new_node == self.treap[p].left {
                    self.rotate_right(p);
                } else {
                    self.rotate_left(p);
                }
            }
        }
        Ok(())
    }

    fn swap_remove(&mut self, index: usize) -> Node<K, P> {
        let c: usize = self.treap.len() - 1; // get the index of the last node
        let p: usize = self.treap[c].parent; // get the index of the parent of the last node
        if c != index && p < self.treap.len() {
            let parent: &mut Node<K, P> = &mut self.treap[p]; // reference to the parent
            if parent.left == c {
                parent.left = index;
            } else {
                parent.right = index;
            }
        }
        self.treap.swap_remove(index)
    }

    fn private_remove(&mut self, n: usize) -> Result<Node<K, P>> {
        if n >= self.treap.len() {
            Err(Error::new(
                ErrorKind::IndexOutOfBounds,
                "Index does not exist.",
            ))
        } else if self.treap.len() == 1 {
            self.root = NIL;
            Ok(self.treap.pop().expect("Should never reach this point."))
        } else {
            while !self.treap[n].is_leaf() {
                if self.treap[n].left != NIL
                    && (self.treap[n].right == NIL
                        || self.treap[self.treap[n].left].priority
                            > self.treap[self.treap[n].right].priority)
                {
                    self.rotate_right(n);
                } else {
                    self.rotate_left(n);
                }
            }
            let p: usize = self.treap[n].parent;
            if self.treap[p].left == n {
                self.treap[p].left = NIL;
            } else {
                self.treap[p].right = NIL;
            }
            Ok(self.swap_remove(n))
        }
    }

    pub fn update(&mut self) -> Result<()> {
        Ok(())
    }

    pub fn remove(&mut self, key: &K) -> Option<Node<K, P>> {
        if let Some(index) = self.search(key) {
            self.private_remove(index).ok()
        } else {
            None
        }
    }

    pub fn top(&mut self) -> Option<Node<K, P>> {
        if self.treap.is_empty() {
            None
        } else {
            self.private_remove(self.root).ok()
        }
    }
}
