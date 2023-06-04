// Copyright (c) 2023 herrsmitty8128
// Distributed under the MIT software license, see the accompanying
// file LICENSE.txt or http://www.opensource.org/licenses/mit-license.php.

#[derive(Debug, Copy, Clone)]
pub enum ErrorKind {
    RotationError,
    IndexOutOfBounds,
    InsertionFailed,
    EmptyHeap,
}

impl std::fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            ErrorKind::InsertionFailed => f.write_str("Insertion failed."),
            ErrorKind::IndexOutOfBounds => f.write_str("Index out of bounds"),
            ErrorKind::RotationError => f.write_str("Rotation error"),
            ErrorKind::EmptyHeap => f.write_str("Heap is empty."),
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
        f.write_fmt(format_args!("{} {}", self.kind, self.message))
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;
