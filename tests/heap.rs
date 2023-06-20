#[cfg(test)]
pub mod test {

    use rand::prelude::*;
    use rtreap::heap::{Heap, HeapNode};

    const COUNT: usize = 10000;

    #[test]
    pub fn test_min_heap() {
        test_heap::<3, false>();
    }

    #[test]
    pub fn test_max_heap() {
        test_heap::<3, true>();
    }

    pub fn test_heap<const B: usize, const H: bool>() {
        type MyNode = HeapNode<usize>;
        //let mut v: Vec<usize> = vec![0; COUNT];
        let mut heap: Heap<usize, MyNode, B, H> = Heap::<usize, MyNode, B, H>::new();
        for _ in 0..COUNT {
            heap.insert(MyNode::from(rand::thread_rng().gen_range(0..10000)));
        }
        //rand::thread_rng().fill(&mut v[..]);

        assert!(
            COUNT == heap.len(),
            "Not all elements were loaded by from()."
        );

        assert!(heap.is_valid());

        while !heap.is_empty() {
            heap.top();
            assert!(heap.is_valid(), "heap.top() failed");
        }

        for _ in 0..COUNT {
            heap.insert(MyNode::from(rand::random::<usize>()));
            assert!(heap.is_valid(), "heap.insert() failed");
        }

        while !heap.is_empty() {
            let len: usize = heap.len();
            heap.remove(rand::thread_rng().gen_range(0..len)).unwrap();
            assert!(heap.is_valid(), "heap.remove() failed");
        }

        for _ in 0..COUNT {
            heap.insert(MyNode::from(rand::random::<usize>()));
            assert!(heap.is_valid(), "heap.insert() failed");
        }

        for _ in 0..COUNT {
            let len: usize = heap.len();
            heap.update(rand::thread_rng().gen_range(0..len), rand::random::<usize>());
            assert!(heap.is_valid(), "heap.update() failed");
        }

        let mut prev_choice: usize = usize::MAX;

        for _ in 0..COUNT {
            let choice: usize = rand::thread_rng().gen_range(0..4);

            match choice {
                0 => {
                    // insert
                    let n = MyNode::from(rand::random::<usize>());
                    heap.insert(n);
                }
                1 => {
                    // extract
                    heap.top();
                }
                2 => {
                    // remove
                    if !heap.is_empty() {
                        let len: usize = heap.len();
                        heap.remove(rand::thread_rng().gen_range(0..len)).unwrap();
                    }
                }
                _ => {
                    // update
                    let len: usize = heap.len();
                    if !heap.is_empty() {
                        heap.update(rand::thread_rng().gen_range(0..len), rand::random::<usize>());
                    }
                }
            }

            assert!(
                heap.is_valid(),
                "### Your choice of {} was a bad one. prev_choice = {} ###",
                choice,
                prev_choice
            );

            prev_choice = choice;
        }
    }
}
