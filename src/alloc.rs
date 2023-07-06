

pub fn allocate<T>(bits: usize) -> &Box<[T]> {
    match bits {
        1 => &Box<[T; 2]>::new(),
        2 => &Box<[T; 4]>::new(),
        3 => &Box<[T; 8]>::new(),
        4 => &Box<[T; 16]>::new(),
        5 => &Box<[T; 32]>::new(),
        6 => &Box<[T; 64]>::new(),
        7 => &Box<[T; 128]>::new(),
        8 => &Box<[T; 256]>::new(),
    }
}