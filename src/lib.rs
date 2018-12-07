//! This crate provide generic cartesian product iterator, 
//! combination iterator, and permutation iterator.
//! 
//! # Three main functionalities
//! - Cartesian product
//! - Combination
//! - Permutation
//! 
//! # Two different style on every functionality
//! This crate provide two implementation style
//! - Iterator style
//! - Callback function style
//! 
//! # Easily share result
//! - Every functionalities can take Rc<RefCell<>> to store result.
//! - An iterator that return owned value.
//! - Every callback style function can take Arc<RwLock<>> to store result.
//! 
//! # Easy usage
//! Three built-in traits that add cart_prod, combination, and permutation functionality
//! to slice/array, Rc<RefCell<&mut[T]>>, and more. 
//! 
//! # Unreach raw performance with unsafe
//! Every functionalities can take raw mutable pointer to store result.
//! 
//! # Example
//! - Getting k-permutation where k is 3 and n is 5.
//! ```
//! use permutator::{Combination, Permutation};
//! let mut data = &[1, 2, 3, 4, 5];
//! let mut counter = 1;
//! data.combination(3).for_each(|mut c| {
//!     c.permutation().for_each(|p| {
//!         println!("k-permutation@{}={:?}", counter, p);
//!         counter += 1;
//!     });
//! });
//! ```
//! - Cartesian product of set of 3, 4, and 5 respectively
//! ```
//! use permutator::{CartesianProductIterator, cartesian_product};
//! let mut domains : &[&[i32]]= &[&[1, 2], &[3, 4, 5], &[6, 7, 8, 9]];
//! println!("=== Cartesian product iterative style ===");
//! CartesianProductIterator::new(domains).into_iter().for_each(|p| {
//!     println!("{:?}", p);
//! });
//! println!("=== cartesian product callback style ===");
//! cartesian_product(domains, |p| {
//!     // `p` is borrowed a ref to internal variable inside cartesian_product function.
//!     println!("{:?}", p);
//! });
//! ```
//! - Easy sharable result
//! ```
//!    use std::cell::RefCell;
//!    use std::rc::Rc;
//!    use std::time::Instant;
//!    use permutator::CartesianProduct;
//!    
//!    let mut counter = 0;
//!    let timer = Instant::now();
//!    let data : &[&[u8]]= &[&[1, 2], &[3, 4, 5, 6], &[7, 8, 9]];
//!    let mut result = vec![&data[0][0]; data.len()];
//!    let shared = Rc::new(RefCell::new(result.as_mut_slice()));
//!
//!    (data, Rc::clone(&shared)).cart_prod().for_each(|_| {
//!        println!("{:?}", &*shared.borrow());
//!        // and notify result borrower(s) that new product is available.
//! 
//!        counter += 1;
//!    });
//!
//!    println!("Total {} products done in {:?}", counter, timer.elapsed());
//! ```
//! - Unsafely share result example
//! ```
//!    use std::time::Instant;
//!    use permutator::Permutation;
//!
//!    let data : &[i32] = &[1, 2, 3, 4, 5];
//!    let mut counter = 0;
//!    let k = 3;
//!    let mut result : Vec<&i32> = vec![&data[0]; k];
//!    // `result` can be share safely anywhere
//!    let shared = result.as_mut_slice() as *mut [&i32];
//!    // `shared` can be share as long as `result` is alive
//!    let timer = Instant::now();
//!    // unsafe statement may be omit because the permutation trait
//!    // hid it internally. However, keep in mind that it rely
//!    // on a pointer so every operation is still considered unsafe.
//!    unsafe {
//!        (data, k, shared).permutation().for_each(|_| {
//!            println!("{:?}", &*shared);
//!            // and notify result borrower(s) that new permutation is available.
//! 
//!            counter += 1;
//!        });
//!
//!        println!("Total {} combination done in {:?}", counter, timer.elapsed());
//!    }
//! ```
//! # See
//! - [Github repository for more examples](https://github.com/NattapongSiri/permutator)
//! 
//! # Found a bug ?
//! Open issue at [Github](https://github.com/NattapongSiri/permutator)

extern crate num;

use num::{PrimInt, Unsigned};
use std::cell::RefCell;
use std::collections::{VecDeque};
use std::iter::{ExactSizeIterator, Product, Iterator};
use std::rc::Rc;
use std::sync::{Arc, RwLock};

pub mod copy;

/// Calculate all possible cartesian combination size.
/// It is always equals to size.pow(degree).
/// # Parameters
/// - `size` is a size of data to generate a cartesian product
/// - `degree` is a number of combination of data.
/// # Examples
/// ```
/// use permutator::get_cartesian_size;
/// 
/// get_cartesian_size(3, 2); // return 9.
/// get_cartesian_size(3, 3); // return 27.
/// ```
/// # See
/// [get_cartesian_for](fn.get_cartesian_for.html)
pub fn get_cartesian_size(size: usize, degree: usize) -> usize {
    size.pow(degree as u32)
}

/// Get a cartesian product at specific location.
/// If `objects` is [1, 2, 3] and degree is 2 then 
/// all possible result is [1, 1], [1, 2], [1, 3],
/// [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3]
/// 
/// # Parameters
/// - `objects` is a slice of an object.
/// - `degree` is a degree of cartesian size.
/// - `i` is a specific location to get a combination.
/// 
/// # Examples
/// ```
/// use permutator::get_cartesian_for;
/// 
/// let nums = [1, 2, 3];
/// get_cartesian_for(&nums, 2, 0); // Return Ok([1, 1])
/// get_cartesian_for(&nums, 2, 3); // Return Ok([2, 1])
/// get_cartesian_for(&nums, 2, 8); // Return Ok([3, 3])
/// get_cartesian_for(&nums, 2, 9); // Return Err("Parameter `i` is out of bound")
/// get_cartesian_for(&nums, 4, 0); // Return Err("Parameter `degree` cannot be larger than size of objects")
/// ```
pub fn get_cartesian_for<T>(objects: &[T], degree: usize, i: usize) -> Result<Vec<&T>, &str> {
    if i >= get_cartesian_size(objects.len(), degree) {
        return Err("Parameter `i` is out of bound")
    }

    if objects.len() < degree {
        return Err("Parameter `degree` cannot be larger than size of objects")
    }

    let w_len = objects.len();
    let mut result = VecDeque::new();
    let mut idx = i;

    (0..degree).for_each(|_| {
        let x = idx % w_len;
        result.push_front(&objects[x]);
        idx /= w_len;
    });

    return Ok(Vec::from(result))
}

/// Calculate all possible number of permutation.
/// It's equals to size!/(size - 1).
/// 
/// # Parameters
/// - `size` a size of data set to generate a permutation.
/// - `degree` number of data set repetition.
/// 
/// # Examples
/// ```
/// use permutator::get_permutation_size;
/// 
/// get_permutation_size(3, 2); // return = 6
/// get_permutation_size(4, 2); // return = 12
/// ```
/// 
/// # See
/// [get_permutation_for](fn.get_permutation_for.html)
pub fn get_permutation_size(size: usize, degree: usize) -> usize {
    divide_factorial(size, size - degree)
}

/// Get permutation at specific location.
/// If `objects` is [1, 2, 3, 4] and `degree` is 2 then 
/// all possible permutation will be [1, 2], [1, 3],
/// [1, 4], [2, 1], [2, 3], [2, 4], [3, 1], [3, 2],
/// [3, 4], [4, 1], [4, 2], [4, 3].
/// 
/// # Parameters
/// - `objects` a set of data that is a based for permutation.
/// - `degree` number of element per each location.
/// - `x` is a location to get a permutation
/// 
/// # Examples
/// ```
/// use permutator::get_permutation_for;
/// 
/// let nums = [1, 2, 3, 4];
/// get_permutation_for(&nums, 2, 0); // return Result([1, 2])
/// get_permutation_for(&nums, 3, 0); // return Result([1, 2, 3])
/// get_permutation_for(&nums, 2, 5); // return Result([2, 4])
/// get_permutation_for(&nums, 2, 11); // return Result([4, 3])
/// get_permutation_for(&nums, 2, 12); // return Err("parameter x is outside a possible length")
/// get_permutation_for(&nums, 5, 0); // return Err("Insufficient number of object in parameters objects for given parameter degree")
/// ```
pub fn get_permutation_for<T>(objects: &[T], degree: usize, x: usize) -> Result<Vec<&T>, &str> {
    let mut next_x = x;
    // hold ordered result for purpose of calculating slot
    let mut states = Vec::<usize>::with_capacity(degree);
    // a slot available for next result to check if it fit in.
    let mut slots = vec!(0; degree);
    // actual result to return to caller.
    let mut result = Vec::new();
    
    if objects.len() < degree {
        return Err("Insufficient number of object in parameters objects for given parameter degree")
    }

    if x >= divide_factorial(objects.len(), objects.len() - degree) {
        return Err("parameter x is outside a possible length");
    }

    for i in 1..degree + 1 {
        let div = divide_factorial(objects.len() - i, objects.len() - degree);
        // raw index that need to be adjusted before adding to result.
        let mut idx = next_x / div;
        // update x for next set of value calculation.
        next_x = next_x % div;

        if i > 1 {
            let mut counter = idx; // hold slot allocation simulation
            
            for (j, slot) in slots.iter().enumerate() {
                if counter < *slot {
                    // found slot that can fit the value
                    idx += j; // offset value for all previous slot(s)
                    result.push(&objects[idx]);
                    break;
                } else {
                    counter -= slot; // take all the slot
                }
            }

            if result.len() < i {
                // no slot found, appending to result
                idx = idx + i - 1; // offset for all previous slot(s)
                result.push(&objects[idx]);
            } 

            let mut insert_point = None;
            
            // Find where the last value were inserted if result is in ordered.
            for j in 0..states.len() {
                if idx < states[j] { // found place to insert value
                    insert_point = Some(j);
                    break;
                }
            }

            if let Some(j) = insert_point {
                // insert value at insertion point
                states.insert(j, idx);
            } else {
                // the value is larger than entire result.
                states.push(idx); // append value to state as largest one.
            }
            
            slots[0] = states[0]; // update first state

            for j in 1..slots.len() { // update slot info
                if j < states.len() { // found slot required an update
                    // slot size is equals to current state - previous state - 1.
                    slots[j] = states[j] - states[j - 1] - 1; 
                } else { // all slots with associated state updated
                    break;
                }
            }
        } else {
            // First element.
            result.push(&objects[idx]);
            states.push(idx);
            slots[0] = idx - 0;
        }
    }

    Ok(result)
}

/// Core algorithm to generate cartesian product.
/// # Parameters
/// - `n` - the size of domains.
/// For product on self, it equals to how many time to create product on self.
/// - `set_len` - the closure to get length of each domain.
/// - `assign_res` - the closure to store product into result
/// - `cb` - the closure to get call on each generated product.
/// # Execution sequence of closure.
/// Each step in sequence is performed sequentially. 
/// It won't advance if the closure in given step isn't return.
/// 1. `assign_res` once
/// 2. `cb` once
/// 3. `set_len` multiple times until it found at least a domain
/// that doesn't exhausted, otherwise, terminate function.
/// 4. go back to step 1 
#[inline(always)]
fn _cartesian_product_core(
    n : usize, 
    set_len : impl Fn(usize) -> usize, 
    mut assign_res : impl FnMut(usize, usize), 
    mut cb : impl FnMut() )
{
    assert!(n > 0, "Cannot create cartesian product with number of domain == 0");

    let mut more = true;
    let mut i = 0;
    let mut c = vec![0; n];
    let n = n - 1;
    while more {
        assign_res(i, c[i]);

        if i == n {
            c[i] += 1;
            cb();
        }

        if i < n {
            i += 1;
        }

        while c[i] == set_len(i) { // c[i] reach the length of set[i]
            c[i] = 0;
            
            if i == 0 {
                more = false;
                break;
            }

            i -= 1;
            c[i] += 1;
        }

    }
}

/// Create a cartesian product over given slice. The result will be a slice
/// of borrowed `T`. 
/// 
/// # Parameters
/// - `sets` A slice of slice(s) contains `T` elements.
/// - `cb` A callback function. It will be called on each product.
/// 
/// # Return
/// A function return a slice of borrowed `T` element out of parameter `sets`.
/// It return value as parameter of callback function `cb`.
/// 
/// # Examples
/// To print all cartesian product between [1, 2, 3] and [4, 5, 6].
/// ```
///    use permutator::cartesian_product;
/// 
///    cartesian_product(&[&[1, 2, 3], &[4, 5, 6]], |product| {
///        // First called will receive [1, 4] then [1, 5] then [1, 6]
///        // then [2, 4] then [2, 5] and so on until [3, 6].
///        println!("{:?}", product);
///    });
/// ```
pub fn cartesian_product<'a, T, F>(
    sets : &'a [&[T]], 
    mut cb : F)
where T : 'a,
      for<'r> F : FnMut(&'r [&'a T]) + 'a
{
    let mut result = vec![&sets[0][0]; sets.len()];
    let copied = result.as_slice() as *const [&T];
    unsafe {
        // It'd safe to use pointer here because internally,
        // the callback will be called after result mutation closure
        // and it will wait until the callback function return to 
        // resume mutate the result again.
        _cartesian_product_core(
            sets.len(), 
            #[inline(always)] |i| {
                sets[i].len()
            }, 
            #[inline(always)] |i, c| {
                result[i] = &sets[i][c];
            }, 
            #[inline(always)] || {
                cb(&*copied);
            });
    }
}

/// Similar to safe [cartesian_product function](fn.cartesian_product.html) 
/// except the way it return the product.
/// It return result through mutable pointer to result assuming the
/// pointer is valid. It'll notify caller on each new result via empty
/// callback function.
/// # Parameters
/// - `sets` A raw sets of data to get a cartesian product.
/// - `result` A mutable pointer to slice of length equals to `sets.len()`
/// - `cb` A callback function  which will be called after new product
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Unsafe
/// This function is unsafe because it may dereference a dangling pointer,
/// may cause data race if multiple threads read/write to the same memory,
/// and all of those unsafe Rust condition will be applied here.
/// # Rationale
/// The safe [cartesian_product function](fn.cartesian_product.html) 
/// return value in callback parameter. It limit the lifetime of return 
/// product to be valid only inside it callback. To use it outside 
/// callback scope, it need to copy the value which will have performance 
/// penalty. Therefore, jeopardize it own goal of being fast. This 
/// function provide alternative way that sacrifice safety for performance.
/// 
/// # Example
/// The scenario is we want to get cartesian product from single source of data
/// then distribute the product to two workers which read each combination
/// then do something about it, which in this example, simply print it.
/// ```
///    use permutator::unsafe_cartesian_product;
///    use std::fmt::Debug;
///    // All shared data consumer will get call throught this trait
///    trait Consumer {
///        fn consume(&self); // need to be ref due to rule of only ref mut is permit at a time
///    }
/// 
///    struct Worker1<'a, T : 'a> {
///        data : &'a[&'a T] // Store ref to cartesian product.
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
///        fn consume(&self) {
///            // read new share cartesian product and do something about it, in this case simply print it.
///            println!("Work1 has {:?}", self.data);
///        }
///    }
///
///    struct Worker2<'a, T : 'a> {
///        data : &'a[&'a T] // Store ref to cartesian product.
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
///        fn consume(&self) {
///            // read new share cartesian product and do something about it, in this case simply print it.
///            println!("Work2 has {:?}", self.data);
///        }
///    }
///
///    unsafe fn start_cartesian_product_process<'a>(data : &'a[&'a[i32]], cur_result : *mut [&'a i32], consumers : Vec<Box<Consumer + 'a>>) {
///        unsafe_cartesian_product(data, cur_result, || {
///            consumers.iter().for_each(|c| {
///                c.consume();
///            })
///        });
///    }
/// 
///    let data : &[&[i32]] = &[&[1, 2], &[3, 4, 5], &[6]];
///    let mut result = vec![&data[0][0]; data.len()];
///
///    unsafe {
///
///        let shared = result.as_mut_slice() as *mut [&i32];
///        let worker1 = Worker1 {
///            data : &result
///        };
///        let worker2 = Worker2 {
///            data : &result
///        };
///        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
///        start_cartesian_product_process(data, shared, consumers);
///    }
/// ```
/// # See
/// - [cartesian_product function](fn.cartesian_product.html)
pub unsafe fn unsafe_cartesian_product<'a, T>(sets : &'a[&[T]], result : *mut [&'a T], cb : impl FnMut()) {
    _cartesian_product_core(
        sets.len(), 
        #[inline(always)] |i| {
            sets[i].len()
        }, 
        #[inline(always)] |i, c| {
            (*result)[i] = &sets[i][c];
        }, cb);
}

/// Similar to safe [cartesian_product function](fn.cartesian_product.html) 
/// except the way it return the product.
/// It return result through Rc<RefCell<>> to mutable slice of result.
/// It'll notify caller on each new result via empty callback function.
/// # Parameters
/// - `sets` A raw sets of data to get a cartesian product.
/// - `result` An Rc<RefCell<>> contains mutable slice of length equals to `sets.len()`
/// - `cb` A callback function  which will be called after new product
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Rationale
/// The safe [cartesian product function](fn.cartesian_product.html) return value in
/// callback parameter. It limit the lifetime of return combination to be
/// valid only inside it callback. To use it outside callback scope, it
/// need to copy the value which will have performance penalty. Therefore,
/// jeopardize it own goal of being fast. This function provide alternative
/// safe way to share result which is roughly 50% slower to unsafe counterpart.
/// The performance is on par with using [CartesianProduct](struct.CartesianProductIterator.html#method.next_into_cell)
/// iterator.
/// 
/// # Example
/// The scenario is we want to get cartesian product from single source of data
/// then distribute the product to two workers which read each combination
/// then do something about it, which in this example, simply print it.
/// ```
///    use permutator::cartesian_product_cell;
///    use std::fmt::Debug;
///    use std::rc::Rc;
///    use std::cell::RefCell;
/// 
///    // All shared data consumer will get call throught this trait
///    trait Consumer {
///        fn consume(&self); // need to be ref due to rule of only ref mut is permit at a time
///    }
/// 
///    struct Worker1<'a, T : 'a> {
///        data : Rc<RefCell<&'a mut[&'a T]>> // Store ref to cartesian product.
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
///        fn consume(&self) {
///            // read new share cartesian product and do something about it, in this case simply print it.
///            println!("Work1 has {:?}", self.data.borrow());
///        }
///    }
///
///    struct Worker2<'a, T : 'a> {
///        data : Rc<RefCell<&'a mut[&'a T]>> // Store ref to cartesian product.
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
///        fn consume(&self) {
///            // read new share cartesian product and do something about it, in this case simply print it.
///            println!("Work2 has {:?}", self.data.borrow());
///        }
///    }
///
///    fn start_cartesian_product_process<'a>(data : &'a[&'a[i32]], cur_result : Rc<RefCell<&'a mut [&'a i32]>>, consumers : Vec<Box<Consumer + 'a>>) {
///        cartesian_product_cell(data, cur_result, || {
///            consumers.iter().for_each(|c| {
///                c.consume();
///            })
///        });
///    }
/// 
///    let data : &[&[i32]] = &[&[1, 2], &[3, 4, 5], &[6]];
///    let mut result = vec![&data[0][0]; data.len()];
///
///    let shared = Rc::new(RefCell::new(result.as_mut_slice()));
///    let worker1 = Worker1 {
///        data : Rc::clone(&shared)
///    };
///    let worker2 = Worker2 {
///        data : Rc::clone(&shared)
///    };
///    let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
///    start_cartesian_product_process(data, shared, consumers);
/// ```
/// # See
/// - [cartesian_product function](fn.cartesian_product.html)
pub fn cartesian_product_cell<'a, T>(sets : &'a[&[T]], result : Rc<RefCell<&'a mut [&'a T]>>, cb : impl FnMut()) {
    _cartesian_product_core(
        sets.len(), 
        #[inline(always)] |i| {
            sets[i].len()
        }, 
        #[inline(always)] |i, c| {
            result.borrow_mut()[i] = &sets[i][c];
        }, cb);
}

/// Similar to safe [cartesian_product function](fn.cartesian_product.html) 
/// except the way it return the product.
/// It return result through Rc<RefCell<>> to mutable slice of result.
/// It'll notify caller on each new result via empty callback function.
/// # Parameters
/// - `sets` A raw sets of data to get a cartesian product.
/// - `result` An Rc<RefCell<>> contains mutable slice of length equals to `sets.len()`
/// - `cb` A callback function  which will be called after new product
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Rationale
/// The safe [cartesian product function](fn.cartesian_product.html) return value in
/// callback parameter. It limit the lifetime of return combination to be
/// valid only inside it callback. To use it outside callback scope, it
/// need to copy the value which will have performance penalty. Therefore,
/// jeopardize it own goal of being fast. This function provide alternative
/// safe way to share result which is roughly 50% slower to unsafe counterpart.
/// The performance is on roughly 15%-20% slower than [CartesianProduct](struct.CartesianProductIterator.html)
/// iterator in uncontrol test environment.
/// 
/// # Example
/// The scenario is we want to get cartesian product from single source of data
/// then distribute the product to two workers which read each combination
/// then do something about it, which in this example, simply print it.
/// ```
///    use std::thread;
///    use std::sync::{Arc, RwLock};
///    use std::sync::mpsc;
///    use std::sync::mpsc::{Receiver, SyncSender};
///    use permutator::cartesian_product_sync;
///  
///    fn start_cartesian_product_process<'a>(data : &'a[&[i32]], cur_result : Arc<RwLock<Vec<&'a i32>>>, notifier : Vec<SyncSender<Option<()>>>, release_recv : Receiver<()>) {
///        use std::time::Instant;
///        let timer = Instant::now();
///        let mut counter = 0;
///        cartesian_product_sync(data, cur_result, || {
///            notifier.iter().for_each(|n| {
///                n.send(Some(())).unwrap(); // notify every thread that new data available
///            });
///
///            for _ in 0..notifier.len() {
///                release_recv.recv().unwrap(); // block until all thread reading data notify on read completion
///            }
///
///            counter += 1;
///        });
///
///        notifier.iter().for_each(|n| {n.send(None).unwrap()}); // notify every thread that there'll be no more data.
///
///        println!("Done {} combinations with 2 workers in {:?}", counter, timer.elapsed());
///    }
///    let k = 7;
///    let data : &[&[i32]]= &[&[1, 2, 3], &[4, 5], &[6]];
///    let result = vec![&data[0][0]; k];
///    let result_sync = Arc::new(RwLock::new(result));
///
///    // workter thread 1
///    let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
///    let (main_send, main_recv) = mpsc::sync_channel(0);
///    let t1_local = main_send.clone();
///    let t1_dat = Arc::clone(&result_sync);
///    thread::spawn(move || {
///        while let Some(_) = t1_recv.recv().unwrap() {
///            let result : &Vec<&i32> = &*t1_dat.read().unwrap();
///            // println!("Thread1: {:?}", result);
///            t1_local.send(()).unwrap(); // notify generator thread that reference is no longer need.
///        }
///        println!("Thread1 is done");
///    });
/// 
///    // worker thread 2
///    let (t2_send, t2_recv) = mpsc::sync_channel::<Option<()>>(0);
///    let t2_dat = Arc::clone(&result_sync);
///    let t2_local = main_send.clone();
///    thread::spawn(move || {
///        while let Some(_) = t2_recv.recv().unwrap() {
///            let result : &Vec<&i32> = &*t2_dat.read().unwrap();
///            // println!("Thread2: {:?}", result);
///            t2_local.send(()).unwrap(); // notify generator thread that reference is no longer need.
///        }
///        println!("Thread2 is done");
///    });
///
///    // main thread that generate result
///    thread::spawn(move || {
///        start_cartesian_product_process(data, result_sync, vec![t1_send, t2_send], main_recv);
///    }).join().unwrap();
/// ```
/// # See
/// - [cartesian_product function](fn.cartesian_product.html)
pub fn cartesian_product_sync<'a, T>(sets : &'a[&[T]], result : Arc<RwLock<Vec<&'a T>>>, cb : impl FnMut()) {
    _cartesian_product_core(
        sets.len(), 
        #[inline(always)] |i| {
            sets[i].len()
        }, 
        #[inline(always)] |i, c| {
            result.write().unwrap()[i] = &sets[i][c];
        }, cb);
}

/// Create a cartesian product over itself. The result will be a slice
/// of borrowed `T`. 
/// 
/// # Parameters
/// - `set` A slice of slice(s) contains `T` elements.
/// - `n` How many time to create a product over `set`
/// - `cb` A callback function. It will be called on each product.
/// 
/// # Return
/// A function return a slice of borrowed `T` element out of parameter `sets`.
/// It return value as parameter of callback function `cb`.
/// 
/// # Examples
/// To print all cartesian product between [1, 2, 3] and [4, 5, 6].
/// ```
///    use permutator::self_cartesian_product;
/// 
///    self_cartesian_product(&[1, 2, 3], 3, |product| {
///        // First called will receive [1, 4] then [1, 5] then [1, 6]
///        // then [2, 4] then [2, 5] and so on until [3, 6].
///        println!("{:?}", product);
///    });
/// ```
pub fn self_cartesian_product<'a, T, F>(set : &'a [T], n : usize, mut cb : F)
where T : 'a,
      for<'r> F : FnMut(&'r [&'a T]) + 'a
{
    let mut result = vec![&set[0]; n];

    let copied = result.as_slice() as *const [&T];

    unsafe {
        // It'd safe to use pointer here because internally,
        // the callback will be called after result mutation closure
        // and it will wait until the callback function return to 
        // resume mutate the result again.
        _cartesian_product_core(
            n, 
            #[inline(always)] |_| {
                set.len()
            }, 
            #[inline(always)]  |i, c| {
                result[i] = &set[c];
            }, 
            #[inline(always)] || {
                cb(&*copied);
            });
    }
}

/// Similar to safe [self_cartesian_product function](fn.self_cartesian_product.html) 
/// except the way it return the product.
/// It return result through mutable pointer to result assuming the
/// pointer is valid. It'll notify caller on each new result via empty
/// callback function.
/// # Parameters
/// - `set` A raw sets of data to get a cartesian product.
/// - `n` How many time to create a product on `set` parameter.
/// - `result` A mutable pointer to slice of length equals to `sets.len()`
/// - `cb` A callback function  which will be called after new product
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Unsafe
/// This function is unsafe because it may dereference a dangling pointer,
/// may cause data race if multiple threads read/write to the same memory,
/// and all of those unsafe Rust condition will be applied here.
/// # Rationale
/// The safe [self_cartesian_product function](fn.self_cartesian_product.html) 
/// return value in callback parameter. It limit the lifetime of return 
/// product to be valid only inside it callback. To use it outside 
/// callback scope, it need to copy the value which will have performance 
/// penalty. Therefore, jeopardize it own goal of being fast. This 
/// function provide alternative way that sacrifice safety for performance.
/// 
/// # Example
/// The scenario is we want to get cartesian product from single source of data
/// then distribute the product to two workers which read each combination
/// then do something about it, which in this example, simply print it.
/// ```
///    use permutator::unsafe_self_cartesian_product;
///    use std::fmt::Debug;
///    // All shared data consumer will get call throught this trait
///    trait Consumer {
///        fn consume(&self); // need to be ref due to rule of only ref mut is permit at a time
///    }
/// 
///    struct Worker1<'a, T : 'a> {
///        data : &'a[&'a T] // Store ref to cartesian product.
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
///        fn consume(&self) {
///            // read new share cartesian product and do something about it, in this case simply print it.
///            println!("Work1 has {:?}", self.data);
///        }
///    }
///
///    struct Worker2<'a, T : 'a> {
///        data : &'a[&'a T] // Store ref to cartesian product.
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
///        fn consume(&self) {
///            // read new share cartesian product and do something about it, in this case simply print it.
///            println!("Work2 has {:?}", self.data);
///        }
///    }
///
///    unsafe fn start_cartesian_product_process<'a>(data : &'a[i32], n : usize, cur_result : *mut [&'a i32], consumers : Vec<Box<Consumer + 'a>>) {
///        unsafe_self_cartesian_product(data, n, cur_result, || {
///            consumers.iter().for_each(|c| {
///                c.consume();
///            })
///        });
///    }
/// 
///    let data : &[i32] = &[1, 2, 3];
///    let n = 3;
///    let mut result = vec![&data[0]; n];
///
///    unsafe {
///
///        let shared = result.as_mut_slice() as *mut [&i32];
///        let worker1 = Worker1 {
///            data : &result
///        };
///        let worker2 = Worker2 {
///            data : &result
///        };
///        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
///        start_cartesian_product_process(data, n, shared, consumers);
///    }
/// ```
/// # See
/// - [cartesian_product function](fn.cartesian_product.html)
pub unsafe fn unsafe_self_cartesian_product<'a, T>(set : &'a[T], n : usize, result : *mut [&'a T], cb : impl FnMut()) {
    _cartesian_product_core(
        n, 
        #[inline(always)] |_| {
            set.len()
        }, 
        #[inline(always)]  |i, c| {
            (*result)[i] = &set[c];
        }, cb);
}

/// Similar to safe [cartesian_product function](fn.self_cartesian_product.html) 
/// except the way it return the product.
/// It return result through Rc<RefCell<>> to mutable slice of result.
/// It'll notify caller on each new result via empty callback function.
/// # Parameters
/// - `set` A raw sets of data to get a cartesian product.
/// - `n` How many time to create a product of `set` parameter
/// - `result` An Rc<RefCell<>> contains mutable slice of length equals to `sets.len()`
/// - `cb` A callback function  which will be called after new product
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Rationale
/// The safe [cartesian product function](fn.cartesian_product.html) return value in
/// callback parameter. It limit the lifetime of return combination to be
/// valid only inside it callback. To use it outside callback scope, it
/// need to copy the value which will have performance penalty. Therefore,
/// jeopardize it own goal of being fast. This function provide alternative
/// safe way to share result which is roughly 50% slower to unsafe counterpart.
/// The performance is on par with using [CartesianProduct](struct.CartesianProductIterator.html#method.next_into_cell)
/// iterator.
/// 
/// # Example
/// The scenario is we want to get cartesian product from single source of data
/// then distribute the product to two workers which read each combination
/// then do something about it, which in this example, simply print it.
/// ```
///    use permutator::self_cartesian_product_cell;
///    use std::fmt::Debug;
///    use std::rc::Rc;
///    use std::cell::RefCell;
/// 
///    // All shared data consumer will get call throught this trait
///    trait Consumer {
///        fn consume(&self); // need to be ref due to rule of only ref mut is permit at a time
///    }
/// 
///    struct Worker1<'a, T : 'a> {
///        data : Rc<RefCell<&'a mut[&'a T]>> // Store ref to cartesian product.
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
///        fn consume(&self) {
///            // read new share cartesian product and do something about it, in this case simply print it.
///            println!("Work1 has {:?}", self.data.borrow());
///        }
///    }
///
///    struct Worker2<'a, T : 'a> {
///        data : Rc<RefCell<&'a mut[&'a T]>> // Store ref to cartesian product.
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
///        fn consume(&self) {
///            // read new share cartesian product and do something about it, in this case simply print it.
///            println!("Work2 has {:?}", self.data.borrow());
///        }
///    }
///
///    fn start_cartesian_product_process<'a>(data : &'a[i32], n : usize, cur_result : Rc<RefCell<&'a mut [&'a i32]>>, consumers : Vec<Box<Consumer + 'a>>) {
///        self_cartesian_product_cell(data, n, cur_result, || {
///            consumers.iter().for_each(|c| {
///                c.consume();
///            })
///        });
///    }
/// 
///    let data : &[i32] = &[1, 2, 3];
///    let n = 3;
///    let mut result = vec![&data[0]; n];
///
///    let shared = Rc::new(RefCell::new(result.as_mut_slice()));
///    let worker1 = Worker1 {
///        data : Rc::clone(&shared)
///    };
///    let worker2 = Worker2 {
///        data : Rc::clone(&shared)
///    };
///    let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
///    start_cartesian_product_process(data, n, shared, consumers);
/// ```
/// # See
/// - [cartesian_product function](fn.cartesian_product.html)
pub fn self_cartesian_product_cell<'a, T>(set : &'a[T], n : usize, result : Rc<RefCell<&'a mut [&'a T]>>, cb : impl FnMut()) {
    _cartesian_product_core(
        n, 
        #[inline(always)] |_| {
            set.len()
        }, 
        #[inline(always)]  |i, c| {
            result.borrow_mut()[i] = &set[c];
        }, cb);
}

/// Similar to safe [self_cartesian_product function](fn.self_cartesian_product.html) 
/// except the way it return the product.
/// It return result through Arc<RwLock<>> to mutable slice of result.
/// It'll notify caller on each new result via empty callback function.
/// # Parameters
/// - `set` A raw set of data to get a cartesian product.
/// - `n` how many times to do the product of `set` parameter
/// - `result` An Arc<RwLock<>> contains mutable slice of length equals to parameter `n`
/// - `cb` A callback function  which will be called after new product
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Rationale
/// The safe [cartesian product function](fn.self_cartesian_product.html) return value in
/// callback parameter. It limit the lifetime of return combination to be
/// valid only inside it callback. To use it outside callback scope, it
/// need to copy the value which will have performance penalty. Therefore,
/// jeopardize it own goal of being fast. This function provide alternative
/// safe way to share result which is roughly 50% slower to unsafe counterpart.
/// The performance is on roughly 15%-20% slower than [SelfCartesianProduct](struct.SelfCartesianProductIterator.html)
/// iterator in uncontrol test environment.
/// 
/// # Example
/// The scenario is we want to get cartesian product from single source of data
/// then distribute the product to two workers which read each combination
/// then do something about it, which in this example, simply print it.
/// ```
///    use std::thread;
///    use std::sync::{Arc, RwLock};
///    use std::sync::mpsc;
///    use std::sync::mpsc::{Receiver, SyncSender};
///    use permutator::self_cartesian_product_sync;
///  
///    fn start_cartesian_product_process<'a>(data : &'a[i32], n : usize, cur_result : Arc<RwLock<Vec<&'a i32>>>, notifier : Vec<SyncSender<Option<()>>>, release_recv : Receiver<()>) {
///        use std::time::Instant;
///        let timer = Instant::now();
///        let mut counter = 0;
///        self_cartesian_product_sync(data, n, cur_result, || {
///            notifier.iter().for_each(|n| {
///                n.send(Some(())).unwrap(); // notify every thread that new data available
///            });
///
///            for _ in 0..notifier.len() {
///                release_recv.recv().unwrap(); // block until all thread reading data notify on read completion
///            }
///
///            counter += 1;
///        });
///
///        notifier.iter().for_each(|n| {n.send(None).unwrap()}); // notify every thread that there'll be no more data.
///
///        println!("Done {} combinations with 2 workers in {:?}", counter, timer.elapsed());
///    }
/// 
///    let data : &[i32]= &[1, 2, 3];
///    let n = 3;
///    let result = vec![&data[0]; n];
///    let result_sync = Arc::new(RwLock::new(result));
///
///    // workter thread 1
///    let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
///    let (main_send, main_recv) = mpsc::sync_channel(0);
///    let t1_local = main_send.clone();
///    let t1_dat = Arc::clone(&result_sync);
///    thread::spawn(move || {
///        while let Some(_) = t1_recv.recv().unwrap() {
///            let result : &Vec<&i32> = &*t1_dat.read().unwrap();
///            // println!("Thread1: {:?}", result);
///            t1_local.send(()).unwrap(); // notify generator thread that reference is no longer need.
///        }
///        println!("Thread1 is done");
///    });
/// 
///    // worker thread 2
///    let (t2_send, t2_recv) = mpsc::sync_channel::<Option<()>>(0);
///    let t2_dat = Arc::clone(&result_sync);
///    let t2_local = main_send.clone();
///    thread::spawn(move || {
///        while let Some(_) = t2_recv.recv().unwrap() {
///            let result : &Vec<&i32> = &*t2_dat.read().unwrap();
///            // println!("Thread2: {:?}", result);
///            t2_local.send(()).unwrap(); // notify generator thread that reference is no longer need.
///        }
///        println!("Thread2 is done");
///    });
///
///    // main thread that generate result
///    thread::spawn(move || {
///        start_cartesian_product_process(data, n, result_sync, vec![t1_send, t2_send], main_recv);
///    }).join().unwrap();
/// ```
/// # See
/// - [cartesian_product function](fn.cartesian_product.html)
pub fn self_cartesian_product_sync<'a, T>(set : &'a[T], n : usize, result : Arc<RwLock<Vec<&'a T>>>, cb : impl FnMut()) {
    _cartesian_product_core(
        n, 
        #[inline(always)] |_| {
            set.len()
        }, 
        #[inline(always)]  |i, c| {
            result.write().unwrap()[i] = &set[c];
        }, cb);
}

/// # Deprecated
/// This combination family is now deprecated.
/// Consider using [large_combination function](fn.large_combination.html)
/// instead. This is because current implementation need to copy every ref
/// on every iteration which is inefficient. 
/// On uncontroll test environment, this iterator take 2.41s to iterate over
/// 30,045,015 combinations. The [large_combination function](fn.large_combination.html)
/// took only 208.84ms. Beside speed, it also theoritically support up to 2^32 elements.
/// If no more efficient implementation is available for some certain time period,
/// this function will be officially mark with #[deprecated].
/// 
/// Generate a combination out of given `domain`.
/// It call `cb` to several times to return each combination.
/// It's similar to [struct GosperCombination](struct.GosperCombinationIterator.html) but
/// slightly faster in uncontrol test environment.
/// # Parameters
/// - `domain` is a slice containing the source data, AKA 'domain'
/// - `r` is a size of each combination, AKA 'range' size
/// - `cb` is a callback function that will get call several times.
/// Each call will have a slice of combination pass as callback parameter.
/// # Returns
/// The function will return combination via callback function. It will
/// keep calling until no further combination can be found then it
/// return control to called.
/// # Example
/// ```
/// use permutator::combination;
/// combination(&[1, 2, 3, 4, 5], 3, |c| {
///     // called multiple times.
///     // Each call have [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4]
///     // [1, 2, 5], [1, 3, 5], [2, 3, 5], [1, 4, 5], [2, 4, 5],
///     // and [3, 4, 5] respectively.
///     println!("{:?}", c);
/// });
/// ```
/// # Limitation
/// Gosper algorithm need to know the MSB (most significant bit).
/// The current largest known MSB data type is u128.
/// This make the implementation support up to 128 elements slice.
/// # See
/// - [GosperCombination](struct.GospoerCombination.html)
pub fn combination<T>(domain: &[T], r : usize, mut cb : impl FnMut(&[&T]) -> ()) {
    let (mut combination, mut map) = create_k_set(domain, r);
    cb(&combination);

    while let Some(_) = swap_k((&mut combination, &mut map), domain) {
        cb(&combination);
    }
}

/// # Deprecated
/// See [combination function](fn.combination.html) for reason of
/// deprecation
/// 
/// Similar to safe [combination function](fn.combination.html) except 
/// the way it return the combination.
/// It return result through mutable pointer to result assuming the
/// pointer is valid. It'll notify caller on each new result via empty
/// callback function.
/// # Parameters
/// - `domain` A raw data to get combination.
/// - `r` A size of each combination.
/// - `result` A mutable pointer to slice of length equals to `r`
/// - `cb` A callback function  which will be called after new combination
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Unsafe
/// This function is unsafe because it may dereference a dangling pointer,
/// may cause data race if multiple threads read/write to the same memory,
/// and all of those unsafe Rust condition will be applied here.
/// # Rationale
/// The safe [combination function](fn.combination.html) return value in
/// callback parameter. It limit the lifetime of return combination to be
/// valid only inside it callback. To use it outside callback scope, it
/// need to copy the value which will have performance penalty. Therefore,
/// jeopardize it own goal of being fast. This function provide alternative
/// way that sacrifice safety for performance.
/// # Example
/// The scenario is we want to get combination from single source of data
/// then distribute the combination to two workers which read each combination
/// then do something about it, which in this example, simply print it.
/// 
/// ```
///    use permutator::unsafe_combination;
///    use std::fmt::Debug;
///    // define a trait that represent a data consumer
///    trait Consumer {
///        fn consume(&self); // cannot mut data because rule of no more than 1 ref mut at a time.
///    }
/// 
///    struct Worker1<'a, T : 'a> {
///        data : &'a[&'a T] // A reference to each combination
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
///        fn consume(&self) {
///            // Read data then do something about it. In this case, simply print it.
///            println!("Work1 has {:?}", self.data); 
///        }
///    }
/// 
///    struct Worker2<'a, T : 'a> {
///        data : &'a[&'a T] // A reference to each combination
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
///        fn consume(&self) {
///            // Read data then do something about it. In this case, simply print it.
///            println!("Work2 has {:?}", self.data);
///        }
///    }
///
///    unsafe fn start_combination_process<'a>(data : &'a[i32], cur_result : *mut [&'a i32], k : usize, consumers : Vec<Box<Consumer + 'a>>) {
///        unsafe_combination(data, k, cur_result, || {
///            consumers.iter().for_each(|c| {
///                c.consume();
///            })
///        });
///    }
///    let k = 3;
///    let data = &[1, 2, 3, 4, 5];
///    let mut result = vec![&data[0]; k];
///
///    unsafe {
///
///        let shared = result.as_mut_slice() as *mut [&i32];
///        let worker1 = Worker1 {
///            data : &result
///        };
///        let worker2 = Worker2 {
///            data : &result
///        };
///        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
///        start_combination_process(data, shared, k, consumers);
///    }
/// ```
/// # See
/// - [combination function](fn.combination.html)
pub unsafe fn unsafe_combination<'a, T>(domain: &'a[T], r : usize, result : *mut [&'a T], mut cb : impl FnMut() -> ()) {
    let mut mask = 0u128;
    unsafe_create_k_set(domain, r, result, &mut mask);
    cb();

    while let Some(_) = swap_k((&mut *result, &mut mask), domain) {
        cb();
    }
}

/// # Deprecated
/// See [combination function](fn.combination.html) for reason of
/// deprecation
/// 
/// Similar to [combination function](fn.combination.html) except 
/// the way it return the combination.
/// It return result through Rc<RefCell<>> to mutable slice of result.
/// It'll notify caller on each new result via empty callback function.
/// # Parameters
/// - `domain` A raw data to get combination.
/// - `r` A size of each combination.
/// - `result` An Rc<RefCell<>> to mutable slice of length equals to `r`
/// - `cb` A callback function  which will be called after new combination
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Rationale
/// The safe [combination function](fn.combination.html) return value in
/// callback parameter. It limit the lifetime of return combination to be
/// valid only inside it callback. To use it outside callback scope, it
/// need to copy the value which will have performance penalty. Therefore,
/// jeopardize it own goal of being fast. This function provide alternative
/// safe way to share result which is roughly 50% slower to unsafe counterpart.
/// The performance is on par with using 
/// [GosperCombinationIterator with next_into_cell function](struct.GosperCombinationIterator.html#method.next_into_cell).
/// # Example
/// The scenario is we want to get combination from single source of data
/// then distribute the combination to two workers which read each combination
/// then do something about it, which in this example, simply print it.
/// 
/// ```
///    use permutator::combination_cell;
///    use std::fmt::Debug;
///    use std::rc::Rc;
///    use std::cell::RefCell;
/// 
///    // define a trait that represent a data consumer
///    trait Consumer {
///        fn consume(&self); // cannot mut data because rule of no more than 1 ref mut at a time.
///    }
/// 
///    struct Worker1<'a, T : 'a> {
///        data : Rc<RefCell<&'a mut[&'a T]>> // A reference to each combination
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
///        fn consume(&self) {
///            // Read data then do something about it. In this case, simply print it.
///            println!("Work1 has {:?}", self.data.borrow()); 
///        }
///    }
/// 
///    struct Worker2<'a, T : 'a> {
///        data : Rc<RefCell<&'a mut[&'a T]>> // A reference to each combination
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
///        fn consume(&self) {
///            // Read data then do something about it. In this case, simply print it.
///            println!("Work2 has {:?}", self.data.borrow());
///        }
///    }
///
///    fn start_combination_process<'a>(data : &'a[i32], cur_result : Rc<RefCell<&'a mut[&'a i32]>>, k : usize, consumers : Vec<Box<Consumer + 'a>>) {
///        combination_cell(data, k, cur_result, || {
///            consumers.iter().for_each(|c| {
///                c.consume();
///            })
///        });
///    }
///    let k = 3;
///    let data = &[1, 2, 3, 4, 5];
///    let mut result = vec![&data[0]; k];
///
///    let shared = Rc::new(RefCell::new(result.as_mut_slice()));
///    let worker1 = Worker1 {
///        data : Rc::clone(&shared)
///    };
///    let worker2 = Worker2 {
///        data : Rc::clone(&shared)
///    };
///    let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
///    start_combination_process(data, shared, k, consumers);
/// ```
/// # See
/// - [combination function](fn.combination.html)
pub fn combination_cell<'a, T>(domain: &'a[T], r : usize, result : Rc<RefCell<&'a mut [&'a T]>>, mut cb : impl FnMut() -> ()) {
    let mut mask = 0u128;
    create_k_set_in_cell(domain, r, &result, &mut mask);
    cb();

    while let Some(_) = swap_k_in_cell((&result, &mut mask), domain) {
        cb();
    }
}

/// # Deprecated
/// See [combination function](fn.combination.html) for reason of
/// deprecation
/// 
/// Similar to [combination function](fn.combination.html) except 
/// the way it return the combination.
/// It return result through Rc<RefCell<>> to mutable slice of result.
/// It'll notify caller on each new result via empty callback function.
/// # Parameters
/// - `domain` A raw data to get combination.
/// - `r` A size of each combination.
/// - `result` An Rc<RefCell<>> to mutable slice of length equals to `r`
/// - `cb` A callback function  which will be called after new combination
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Rationale
/// The [combination function](fn.combination.html) return value in
/// callback parameter. It limit the lifetime of return combination to be
/// valid only inside it callback. To use it on different thread, it
/// need to copy the value which will have performance penalty. 
/// This function provide alternative way to share data between thread.
/// It will write new result into Arc<RwLock<>> of Vec owned inside RwLock.
/// Since it write data directly into Vec, other threads won't know that
/// new data is wrote. The combination generator thread need to notify
/// other threads via channel. This introduce another problem. 
/// Since combination generator write data directly into shared memory address,
/// it need to know if all other threads are done using the data. 
/// Otherwise, in worst case, combination generator thread may dominate all other
/// threads and hold write lock until it done generate every value.
/// To solve such issue, combination generator thread need to get notified
/// when each thread has done using the data.
/// # Example
/// The scenario is we want to get combination from single source of data
/// then distribute the combination to two workers which read each combination
/// then do something about it, which in this example, simply print it.
/// 
/// ```
///    use permutator::combination_sync;
///    use std::fmt::Debug;
///    use std::sync::{Arc, RwLock};
///    use std::sync::mpsc;
///    use std::sync::mpsc::{Receiver, SyncSender};
///    use std::thread;
/// 
///    fn start_combination_process<'a>(data : &'a[i32], cur_result : Arc<RwLock<Vec<&'a i32>>>, k : usize, notifier : Vec<SyncSender<Option<()>>>, release_recv : Receiver<()>) {
///        use std::time::Instant;
///        let timer = Instant::now();
///        let mut counter = 0;
///        combination_sync(data, k, cur_result, || {
///            notifier.iter().for_each(|n| {
///                n.send(Some(())).unwrap(); // notify every thread that new data available
///            });
///
///            for _ in 0..notifier.len() {
///                release_recv.recv().unwrap(); // block until all thread reading data notify on read completion
///            }
///
///            counter += 1;
///        });
///
///        notifier.iter().for_each(|n| {n.send(None).unwrap()}); // notify every thread that there'll be no more data.
///
///        println!("Done {} combinations with 2 workers in {:?}", counter, timer.elapsed());
///    }
///    let k = 3;
///    let data = &[1, 2, 3, 4, 5];
///    let result = vec![&data[0]; k];
///    let result_sync = Arc::new(RwLock::new(result));
///
///    // workter thread 1
///    let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
///    let (main_send, main_recv) = mpsc::sync_channel(0);
///    let t1_local = main_send.clone();
///    let t1_dat = Arc::clone(&result_sync);
///    thread::spawn(move || {
///        while let Some(_) = t1_recv.recv().unwrap() {
///            let result : &Vec<&i32> = &*t1_dat.read().unwrap();
///            println!("Thread1: {:?}", result);
///            t1_local.send(()).unwrap(); // notify generator thread that reference is no longer neeed.
///        }
///        println!("Thread1 is done");
///    });
///
///    // worker thread 2
///    let (t2_send, t2_recv) = mpsc::sync_channel::<Option<()>>(0);
///    let t2_dat = Arc::clone(&result_sync);
///    let t2_local = main_send.clone();
///    thread::spawn(move || {
///        while let Some(_) = t2_recv.recv().unwrap() {
///            let result : &Vec<&i32> = &*t2_dat.read().unwrap();
///            println!("Thread2: {:?}", result);
///            t2_local.send(()).unwrap(); // notify generator thread that reference is no longer neeed.
///        }
///        println!("Thread2 is done");
///    });
///
///    // main thread that generate result
///    thread::spawn(move || {
///        start_combination_process(data, result_sync, k, vec![t1_send, t2_send], main_recv);
///    }).join().unwrap();
/// ```
/// # See
/// - [combination function](fn.combination.html)
pub fn combination_sync<'a, T>(domain: &'a[T], r : usize, result : Arc<RwLock<Vec<&'a T>>>, mut cb : impl FnMut() -> ()) {
    let mut mask = 0u128;
    create_k_set_sync(domain, r, &result, &mut mask);
    cb();

    while let Some(_) = swap_k_sync((&result, &mut mask), domain) {
        cb();
    }
}

/// A core logic that generate a combination
/// 
/// # Parameters
/// 1. slice of T - Source of combination
/// 2. usize - size of combination.
/// 3. closure - function to generate a first result.
/// It tooks ref mut of cursor, ref of domain, and the size of combination.
/// It return object to store result.
/// 4. closure - function that set each element of result to some value.
/// It tooks index of result, an index of domain, and a ref mut object to store result
/// 5. closure - function that got call on each new combination.
/// 
/// # Panic
/// It panic when size of combination is larger that length of source. 
fn _core_large_combination<'a, T : 'a, R : 'a>(
    // source of combination
    domain : &'a [T], 
    // combination size
    r : usize, 
    // A closure that took ref mut of cursor, ref of domain, and the size of combination. It return object to store result
    // It take ownership of result from environment and move it into this function.
    first_result_fn : impl FnOnce(&mut Vec<usize>, &'a [T], usize) -> R, 
    // A closure that took index of result, an index of domain, and object to store result
    mut next_result_fn : impl FnMut(usize, usize, &mut R), 
    // A callback function that get once on each new combination.
    // The new combination is sent as ref as function paramter.
    mut cb : impl FnMut(&R)) 
{
    /// Move cursor and update result
    #[inline(always)]
    fn move_cur_res<'a, T, R>(c : &mut [usize], domain : &'a [T], result : &mut R, next_result_fn : &mut FnMut(usize, usize, &mut R)) {
        let n = c.len();
        let max = domain.len();
        let mut i = c.len() - 1;
        
        if c[i] < max - n + i {
            c[i] += 1;
            next_result_fn(i, c[i], result);
        } else {
            // find where to start reset cursor
            while c[i] >= max - n + i {
                i -= 1;
            }

            c[i] += 1;
            next_result_fn(i, c[i], result);
            i += 1;
            // reset all cursor from `i + 1`
            (i..c.len()).for_each(|i| {
                c[i] = c[i - 1] + 1;
                next_result_fn(i, c[i], result);
            });
        }
    }

    assert_ne!(r, 0, "The combination size cannot be 0");
    assert!(domain.len() >= r, "The combination size cannot be larger than size of data");

    let mut c : Vec<usize> = Vec::new();
    let mut result = first_result_fn(&mut c, domain, r);
    cb(&result);
    let n = r - 1;
    c[n] += 1;

    if c[n] < domain.len() {
        next_result_fn(n, c[n], &mut result);
        cb(&result);
    } else {
        return;
    }

    while c[0] < domain.len() - r {

        // move cursor and update result
        move_cur_res(&mut c, domain, &mut result, &mut next_result_fn);
        cb(&result);
    }
}

/// Generate a r-combination from given domain and call callback function
/// on each combination.
/// 
/// # Parameter
/// 1. `domain : &[T]` - A slice contain a domain to generate r-combination
/// 2. `r : usize` - A size of combination
/// 3. `cb : FnMut(&[&T])` - A callback that return each combination
/// 
/// # Panic
/// It panic when `r` > `domain.len()`
pub fn large_combination<'a, T, F>(domain: &'a [T], r : usize, mut cb : F)
    where T : 'a,
          for<'r> F : FnMut(&'r[&'a T]) + 'a
{
    let mut result : Vec<&T> = Vec::with_capacity(r);
    _core_large_combination(domain, 
        r, 
        #[inline(always)]
        |c, domain, r| {
            (0..r).for_each(|i| {
                result.push(&domain[i]);
                c.push(i);
            });

            result
        }, 
        #[inline(always)]
        |i, j, result| {
            result[i] = &domain[j];
        }, 
        #[inline(always)]
        |result| {
            cb(result);
        }
    );
}

/// Generate a r-combination from given domain and call callback function
/// on each combination. The result will be return into ref mut pointer.
/// 
/// # Parameter
/// 1. `domain : &[T]` - A slice contain a domain to generate r-combination
/// 2. `r : usize` - A size of combination
/// 3. `result : *mut [&T]` - A mutable pointer to store result
/// 4. `cb : FnMut()` - A callback that notify caller on each combination
/// 
/// # Panic
/// - It panic when `r > domain.len()` or `r > result.len()`
/// 
/// # Rationale
/// This function took *mut [&T] to store result. It allow caller to easily share
/// result outside callback function without copying/cloning each result.
/// It sacrifice safety for performance.
/// 
/// # Safety
/// - It doesn't check whether the pointer is valid or not.
/// - It doesn't free memory occupied by result.
/// - It may cause data race
/// - Mutating `result` may cause undesired behavior.
/// - Storing `result` will get overwritten when new combination is return.
/// - All other unsafe Rust condition may applied.
pub unsafe fn unsafe_large_combination<'a, T : 'a>(domain: &'a [T], r : usize, result : *mut [&'a T], mut cb : impl FnMut()) {
    _core_large_combination(domain, 
        r, 
        #[inline(always)]
        |c, domain, r| {
            let result = &mut *result;
            (0..r).for_each(|i| {
                result[i] = &domain[i];
                c.push(i);
            });

            result
        }, 
        #[inline(always)]
        |i, j, result| {
            result[i] = &domain[j];
        }, 
        #[inline(always)]
        |_| {
            cb();
        }
    );
}

/// Generate a r-combination from given domain and call callback function
/// on each combination. The result will be return into Rc<RefCell<>>.
/// 
/// # Parameter
/// 1. `domain : &[T]` - A slice contain a domain to generate r-combination
/// 2. `r : usize` - A size of combination
/// 3. 'result : Rc<RefCell<&mut [&T]>>` - A result container object.
/// 4. `cb : FnMut()` - A callback that notify caller on each combination
/// 
/// # Panic
/// It panic when `r > domain.len()` or `r > result.borrow().len()`
/// 
/// # Rationale
/// It allow easily safe sharing of result to some degree with minor
/// performance overhead and some some usage constraint.
/// - `result` will get overwritten on each new combination.
/// - Storing `result` will get overwritten when new combination is return.
pub fn large_combination_cell<'a, T : 'a>(domain: &'a[T], r : usize, result : Rc<RefCell<&'a mut [&'a T]>>, mut cb : impl FnMut() -> ()) {
    _core_large_combination(domain, 
        r, 
        #[inline(always)]
        |c, domain, r| {
            (0..r).for_each(|i| {
                result.borrow_mut()[i] = &domain[i];
                c.push(i);
            });

            result
        }, 
        #[inline(always)]
        |i, j, result| {
            result.borrow_mut()[i] = &domain[j];
        }, 
        #[inline(always)]
        |_| {
            cb();
        }
    );
}

/// Generate a r-combination from given domain and call callback function
/// on each combination. The result will be return into Arc<RwLock<>>.
/// 
/// # Parameter
/// 1. `domain : &[T]` - A slice contain a domain to generate r-combination
/// 2. `r : usize` - A size of combination
/// 3. 'result : Arc<RwLock<Vec<&T>>>` - A result container object.
/// 4. `cb : FnMut()` - A callback that notify caller on each combination
/// 
/// # Panic
/// It panic when `r > domain.len()` or `r > result.read().unwrap().len()`
/// 
/// # Rationale
/// It allow easily safe sharing of result with other thread to some degree 
/// with minor performance overhead and some some usage constraint.
/// - `result` will get overwritten on each new combination.
/// - Storing `result` will get overwritten when new combination is return.
pub fn large_combination_sync<'a, T : 'a>(domain: &'a[T], r : usize, result : Arc<RwLock<Vec<&'a T>>>, mut cb : impl FnMut() -> ()) {
    _core_large_combination(domain, 
        r, 
        #[inline(always)]
        |c, domain, r| {
            {
                let mut writer = result.write().unwrap();
                (0..r).for_each(|i| {
                    writer[i] = &domain[i];
                    c.push(i);
                });
            }

            result
        }, 
        #[inline(always)]
        |i, j, result| {
            result.write().unwrap()[i] = &domain[j];
        }, 
        #[inline(always)]
        |_| {
            cb();
        }
    );
}

/// A core heap permutation algorithm.
/// # Parameters
/// - `n` size of entire data
/// - `swap` a closure to swap the data
/// - `cb` a callback function that get call on each permutation
/// # Closure execution sequence
/// 1. `swap` once
/// 2. `cb` once
/// 3. go to step 1 until permutation is `n` times
fn _heap_permutation_core(n : usize, mut swap : impl FnMut(usize, usize), mut cb : impl FnMut()) {
    let mut c = vec![0; n];
    let mut i = 0;
    while i < n {
        if c[i] < i {
            if i & 1 == 0 { // equals to mod 2 because it take only 0 and 1 aka last bit
                swap(0, i);
            } else {
                swap(c[i], i);
            }

            cb();
            c[i] += 1;
            i = 0;
        } else {
            c[i] = 0;
            i += 1;
        }
    }
}

/// Heap permutation which permutate variable `d` in place and call `cb` function
/// for each permutation done on `d`. 
/// 
/// # Parameter
/// - `d` a data to be permuted.
/// - `cb` a callback function that will be called several times for each permuted value.
/// 
/// # Example
/// ```
/// use permutator::heap_permutation;
/// heap_permutation(&mut [1, 2, 3], |p| {
///     // call multiple times. It'll print [2, 1, 3], [3, 1, 2], 
///     // [1, 3, 2], [2, 3, 1], and [3, 2, 1] respectively.
///     println!("{:?}", p);
/// });
/// ```
/// # See
/// - [k_permutation_sync](fn.k_permutation_sync.html) for example of 
/// how to implement multi-thread data sync
/// - The [HeapPermutationIterator struct](struct.HeapPermutationIterator.html)
/// provide alternate way of getting permutation but in iterative way.
/// # Warning
/// The permutation is done in place which mean the parameter `d` will be
/// mutated.
/// 
/// # Notes
/// 1. The value passed to callback function will equals to value inside parameter `d`.
pub fn heap_permutation<'a, T>(d : &'a mut [T], mut cb : impl FnMut(&[T]) -> () + 'a) {
    let copied = d as *const [T];
    unsafe {
        // It'd safe because the mutation on `d` will be done
        // before calling `cb` closure and until `cb` closure is return
        // the mutation closure won't get call.
        _heap_permutation_core(
            d.len(), 
            #[inline(always)] |from, to| {
                d.swap(from, to);
            }, 
            #[inline(always)] || {
                cb(&*copied)
            });
    }
}

/// Heap permutation which permutate variable `d` in place and call `cb` function
/// for each permutation done on `d`.
/// 
/// # Parameter
/// - `d` an Rc<RefCell<>> to mutable slice data to be permuted.
/// - `cb` a callback function that will be called several times for each permuted value.
/// 
/// # Example
/// ```
/// use permutator::heap_permutation_cell;
/// use std::rc::Rc;
/// use std::cell::RefCell;
/// let data : &mut[i32] = &mut [1, 2, 3];
/// let sharable = Rc::new(RefCell::new(data));
/// heap_permutation_cell(&sharable, || {
///     // call other functions/objects that use `sharable` variable.
/// });
/// ```
/// 
/// # Warning
/// The permutation is done in place which mean the parameter `d` will be
/// mutated.
/// 
/// # Notes
/// 1. The value passed to callback function will equals to value inside parameter `d`.
pub fn heap_permutation_cell<T>(d : &Rc<RefCell<&mut [T]>>, cb : impl FnMut() -> ()) {
    // need borrow expr outside function call because if the expr is
    // put inline within the function call, Rust runtime hold borrowed `d`
    // for an entire function call
    let n = d.borrow().len(); 
    _heap_permutation_core(
        n, 
        #[inline(always)] |from, to| {
            d.borrow_mut().swap(from, to);
        }, 
        cb
    );
}

/// Heap permutation which permutate variable `d` in place and call `cb` function
/// for each permutation done on `d`.
/// 
/// # Parameter
/// - `d` an Rc<RefCell<>> to mutable slice data to be permuted.
/// - `cb` a callback function that will be called several times for each permuted value.
/// 
/// # Warning
/// The permutation is done in place which mean the parameter `d` will be
/// mutated.
/// 
/// # Notes
/// 1. The value passed to callback function will equals to value inside parameter `d`.
pub fn heap_permutation_sync<T>(d : &Arc<RwLock<Vec<T>>>, cb : impl FnMut() -> ()) {
    // need read lock expr outside function call because if the expr is
    // put inline within the function call, Rust runtime obtain the lock
    // for an entire function call
    let n = d.read().unwrap().len();
    _heap_permutation_core(
        n, 
        #[inline(always)] |from, to| {
            d.write().unwrap().swap(from, to);
        }, 
        cb
    );
}

/// A macro that perform core logic of k-permutation.
/// 
/// # Parameters
/// 1. `k` - The size of each permutation.
/// 2. `n` - The total length of data
/// 3. `swap_fn` - The closure that perform data swap
/// 4. `cb` - The callback function that will return each permutation.
#[allow(unused)]
macro_rules! _k_permutation_core {
    ($k : expr, $n : expr, $swap_fn : expr, $permute_fn : expr, $cb : expr) => {
        if $n < $k {
            panic!("Cannot create k-permutation of size {} for data of length {}", $k, $n);
        } else if $k == 0 {
            // k = 0 mean mean permutation frame size is 0, it cannot have permutation
            return
        }

        $cb;
        $permute_fn; // generate all possible permutation for initial subset

        while let Some(_) = $swap_fn { // repeatly swap element
            $cb;
            $permute_fn; // generate all possible permutation per each subset
        }
    };
}


/// Generate k-permutation over slice of `d`. For example: d = &[1, 2, 3]; k = 2.
/// The result will be [1, 2], [2, 1], [1, 3], [3, 1], [2, 3], [3, 2]
/// 
/// The implementation calculate each combination by [large_combination function](fn.large_combination.html)
/// then apply Heap's algorithm. There's [KPermutationIterator struct](struct.KPermutationIterator.html) 
/// that also generate KPermutationIterator but in iterative style. 
/// The performance of this function is slightly faster than 
/// [KPermutationIterator struct](struct.KPermutationIterator.html) by about 15%-20%
/// tested in uncontrol environment.
/// 
/// # Examples
/// The example below will generate 4-permutation over 6 data items.
/// The first combination will be used to generate all permutation first.
/// So the first three result will be [1, 2, 3, 4], [2, 1, 3, 4], [3, 1, 2, 4]
/// as per Heap permutation algorithm.
/// After all permutation for [1, 2, 3, 4] is calculated, it'll use Gospel
/// algorithm to find next combination which is [1, 2, 3, 5] then 
/// permutate it until every permutation is done.
/// It'll keep repeating above process until last combination, which is
/// [3, 4, 5, 6], is completely permuted then the function will return.
/// 
/// ```
///    use permutator::k_permutation;
///    use std::time::{Instant};
/// 
///    let data = [1, 2, 3, 4, 5, 6];
///    let mut counter = 0;
///    let timer = Instant::now();
/// 
///    k_permutation(&data, 4, |permuted| {
///        // uncomment line below to print all k-permutation
///        // println!("{}:{:?}", counter, permuted);
///        counter += 1;
///    });
///    println!("Done {} permuted in {:?}", counter, timer.elapsed());
///    ```
/// # Panic
/// This function panic when `k == 0` or `k > d.len()`
/// 
/// # Notes
/// 1. This function doesn't support jumping into specific nth permutation because
/// the permutation is out of lexicographic order per Heap's algorithm limitation.
/// For jumping into specific position, it require lexicographic ordered permutation.
/// 2. This function take callback function to speed up permutation processing.
/// It will call the callback right in the middle of Heap's loop then continue 
/// the loop.
/// 3. This function use single thread.
/// 
/// # See
/// - [Heap's algorithm in Wikipedia page, October 9, 2018](https://en.wikipedia.org/wiki/Heap%27s_algorithm)
pub fn k_permutation<'a, T, F>(d : &'a [T], k : usize, mut cb : F)
    where T : 'a,
          for<'r> F : FnMut(&'r [&'a T]) + 'a
{
    assert_ne!(k, 0);
    assert!(k <= d.len());

    large_combination(d, k, move |result| {
        cb(result);

        heap_permutation(&mut result.to_owned(), |r| cb(r));
    });
}

/// Similar to safe [k_permutation function](fn.k_permutation.html) except 
/// the way it return the permutation.
/// It return result through mutable pointer to result assuming the
/// pointer is valid. It'll notify caller on each new result via empty
/// callback function.
/// # Parameters
/// - `d` A raw data to get k-permutation.
/// - `k` A size of each permutation.
/// - `result` A mutable pointer to slice of length equals to `k`
/// - `cb` A callback function  which will be called after new combination
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Unsafe
/// This function is unsafe because it may dereference a dangling pointer,
/// may cause data race if multiple threads read/write to the same memory,
/// and all of those unsafe Rust condition will be applied here.
/// # Rationale
/// The safe [k_permutation function](fn.k_permutation.html) return value in
/// callback parameter. It limit the lifetime of return combination to be
/// valid only inside it callback. To use it outside callback scope, it
/// need to copy the value which will have performance penalty. Therefore,
/// jeopardize it own goal of being fast. This function provide alternative
/// way that sacrifice safety for performance.
/// 
/// # Example
/// The scenario is we want to get k-permutation from single source of data
/// then distribute the permutation to two workers which read each permutation
/// then do something about it, which in this example, simply print it.
/// 
/// ```
///    use permutator::unsafe_k_permutation;
///    use std::fmt::Debug;
///    // define a trait that represent a data consumer
///    trait Consumer {
///        fn consume(&self); // cannot mut data because rule of no more than 1 ref mut at a time.
///    }
/// 
///    struct Worker1<'a, T : 'a> {
///        data : &'a[&'a T] // A reference to each k-permutation
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
///        fn consume(&self) {
///            // Read data then do something about it. In this case, simply print it.
///            println!("Work1 has {:?}", self.data); 
///        }
///    }
/// 
///    struct Worker2<'a, T : 'a> {
///        data : &'a[&'a T] // A reference to each k-permutation
///    }
/// 
///    impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
///        fn consume(&self) {
///            // Read data then do something about it. In this case, simply print it.
///            println!("Work2 has {:?}", self.data);
///        }
///    }
///
///    unsafe fn start_k_permutation_process<'a>(data : &'a[i32], cur_result : *mut [&'a i32], k : usize, consumers : Vec<Box<Consumer + 'a>>) {
///        unsafe_k_permutation(data, k, cur_result, || {
///            consumers.iter().for_each(|c| {
///                c.consume();
///            })
///        });
///    }
///    let k = 3;
///    let data = &[1, 2, 3, 4, 5];
///    let mut result = vec![&data[0]; k];
///
///    unsafe {
///
///        let shared = result.as_mut_slice() as *mut [&i32];
///        let worker1 = Worker1 {
///            data : &result
///        };
///        let worker2 = Worker2 {
///            data : &result
///        };
///        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
///        start_k_permutation_process(data, shared, k, consumers);
///    }
/// ```
/// # Note
/// Performancewise, k_permutation is faster than unsafe_k_permutation. 
/// The unsafe function is only faster when caller need to clone the result.
/// # See
/// - [k_permutation function](fn.k_permutation.html)
pub unsafe fn unsafe_k_permutation<'a, T>(d : &'a [T], k : usize, result : *mut [&'a T], mut cb : impl FnMut() -> ()) {
    assert_eq!(k, (*result).len());

    unsafe_large_combination(d, k, result, || {
        cb();

        // save combination
        let buffer = (*result).to_owned();
        
        // permute the combination in place
        heap_permutation(&mut *result, |_| {
            cb();
        });

        // restore combination so next combination is properly produce
        buffer.iter().enumerate().for_each(|(i, t)| (*result)[i] = *t)
    });
}

/// Similar to safe [k_permutation function](fn.k_permutation.html) except 
/// the way it return the permutation.
/// It return result through mutable pointer to result assuming the
/// pointer is valid. It'll notify caller on each new result via empty
/// callback function.
/// # Parameters
/// - `d` A raw data to get k-permutation.
/// - `k` A size of each permutation.
/// - `result` A mutable pointer to slice of length equals to `k`
/// - `cb` A callback function  which will be called after new combination
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Rationale
/// The safe [k_permutation function](fn.k_permutation.html) return value in
/// callback parameter. It limit the lifetime of return combination to be
/// valid only inside it callback. To use it outside callback scope, it
/// need to copy the value which will have performance penalty. Therefore,
/// jeopardize it own goal of being fast. This function provide alternative
/// safe way to share the permutation with some minor performance cost.
/// This function is about 50% slower than the unsafe counterpart.
/// It's throughput is slightly slower than using a 
/// [next_into_cell](struct.KPermutationIterator.html#method.next_into_cell) by
/// 15%-20% in uncontrol test environment.
/// 
/// # Example
/// The scenario is we want to get k-permutation from single source of data
/// then distribute the combination to two workers which read each permutation
/// then do something about it, which in this example, simply print it.
/// 
/// ```
///    use permutator::k_permutation_cell;
///    use std::fmt::Debug;
///    use std::rc::Rc;
///    use std::cell::RefCell;
/// 
///    trait Consumer {
///        fn consume(&self);
///    }
///    struct Worker1<'a, T : 'a> {
///        data : Rc<RefCell<&'a mut[&'a T]>>
///    }
///    impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
///        fn consume(&self) {
///            println!("Work1 has {:?}", self.data.borrow());
///        }
///    }
///    struct Worker2<'a, T : 'a> {
///        data : Rc<RefCell<&'a mut[&'a T]>>
///    }
///    impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
///        fn consume(&self) {
///            println!("Work2 has {:?}", self.data.borrow());
///        }
///    }
///
///    fn start_k_permutation_process<'a>(data : &'a[i32], cur_result : Rc<RefCell<&'a mut [&'a i32]>>, k : usize, consumers : Vec<Box<Consumer + 'a>>) {
///        k_permutation_cell(data, k, cur_result, || {
///            consumers.iter().for_each(|c| {
///                c.consume();
///            })
///        });
///    }
///    let k = 3;
///    let data = &[1, 2, 3, 4, 5];
///    let mut result = vec![&data[0]; k];
///    let shared = Rc::new(RefCell::new(result.as_mut_slice()));
///
///    let worker1 = Worker1 {
///        data : Rc::clone(&shared)
///    };
///    let worker2 = Worker2 {
///        data : Rc::clone(&shared)
///    };
///    let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
///    start_k_permutation_process(data, shared, k, consumers);
/// ```
/// # Panic
/// Panic if `k == 0` or `k > d.len()`
/// 
/// # See
/// - [k_permutation function](fn.k_permutation.html)
pub fn k_permutation_cell<'a, T>(d : &'a [T], k : usize, result : Rc<RefCell<&'a mut [&'a T]>>, mut cb : impl FnMut() -> ()) {
    assert_ne!(k, 0);
    assert_eq!(k, result.borrow().len());
    large_combination_cell(d, k, Rc::clone(&result), || {
        cb();

        // save combination
        let origin = (*result).borrow().to_owned();
        
        // permute the combination in place
        heap_permutation_cell(&result, || {
            cb();
        });

        // restore combination so next combination is properly produce
        origin.iter().enumerate().for_each(|(i, t)| result.borrow_mut()[i] = *t)
    });
}

/// Similar to safe [k_permutation function](fn.k_permutation.html) except 
/// the way it return the permutation.
/// It return result through mutable pointer to result assuming the
/// pointer is valid. It'll notify caller on each new result via empty
/// callback function.
/// # Parameters
/// - `d` A raw data to get k-permutation.
/// - `k` A size of each permutation.
/// - `result` A mutable pointer to slice of length equals to `k`
/// - `cb` A callback function  which will be called after new combination
/// in `result` is set.
/// # Return
/// This function return result through function's parameter `result` and
/// notify caller that new result is available through `cb` callback function.
/// # Rationale
/// The [k_permutation function](fn.k_permutation.html) return value in
/// callback parameter. It limit the lifetime of return combination to be
/// valid only inside it callback. To use it outside callback scope, it
/// need to copy the value which will have performance penalty. Therefore,
/// jeopardize it own goal of being fast. 
/// This function provide alternative way to share data between thread.
/// It will write new result into Arc<RwLock<>> of Vec owned inside RwLock.
/// Since it write data directly into Vec, other threads won't know that
/// new data is wrote. The combination generator thread need to notify
/// other threads via channel. This introduce another problem. 
/// Since combination generator write data directly into shared memory address,
/// it need to know if all other threads are done using the data. 
/// Otherwise, in worst case, combination generator thread may dominate all other
/// threads and hold write lock until it done generate every value.
/// To solve such issue, combination generator thread need to get notified
/// when each thread has done using the data.
/// 
/// # Example
/// The scenario is we want to get k-permutation from single source of data
/// then distribute the combination to two workers which read each permutation
/// then do something about it, which in this example, simply print it.
/// 
/// ```
/// use permutator::k_permutation_sync;
/// use std::sync::{Arc, RwLock};
/// use std::sync::mpsc;
/// use std::sync::mpsc::{SyncSender, Receiver};
/// use std::thread;
/// 
/// fn start_k_permutation_process<'a>(data : &'a[i32], cur_result : Arc<RwLock<Vec<&'a i32>>>, k : usize, notifier : Vec<SyncSender<Option<()>>>, release_recv : Receiver<()>) {
///     use std::time::Instant;
///     let timer = Instant::now();
///     let mut counter = 0;
///     k_permutation_sync(data, k, cur_result, || {
///         notifier.iter().for_each(|n| {
///             n.send(Some(())).unwrap(); // notify every thread that new data available
///         });
///
///         for _ in 0..notifier.len() {
///             release_recv.recv().unwrap(); // block until all thread reading data notify on read completion
///         }
///
///         counter += 1;
///     });
///
///     notifier.iter().for_each(|n| {n.send(None).unwrap()}); // notify every thread that there'll be no more data.
///
///     println!("Done {} combinations with 2 workers in {:?}", counter, timer.elapsed());
/// }
/// let k = 3;
/// let data = &[1, 2, 3, 4, 5];
/// let result = vec![&data[0]; k];
/// let result_sync = Arc::new(RwLock::new(result));
/// 
/// // workter thread 1
/// let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
/// let (main_send, main_recv) = mpsc::sync_channel(0);
/// let t1_local = main_send.clone();
/// let t1_dat = Arc::clone(&result_sync);
/// thread::spawn(move || {
///     while let Some(_) = t1_recv.recv().unwrap() {
///         let result : &Vec<&i32> = &*t1_dat.read().unwrap();
///         println!("Thread1: {:?}", result);
///         t1_local.send(()).unwrap(); // notify generator thread that reference is no longer neeed.
///     }
///     println!("Thread1 is done");
/// });
///
/// // worker thread 2
/// let (t2_send, t2_recv) = mpsc::sync_channel::<Option<()>>(0);
/// let t2_dat = Arc::clone(&result_sync);
/// let t2_local = main_send.clone();
/// thread::spawn(move || {
///     while let Some(_) = t2_recv.recv().unwrap() {
///         let result : &Vec<&i32> = &*t2_dat.read().unwrap();
///         println!("Thread2: {:?}", result);
///         t2_local.send(()).unwrap(); // notify generator thread that reference is no longer neeed.
///     }
///     println!("Thread2 is done");
/// });
///
/// // main thread that generate result
/// thread::spawn(move || {
///     start_k_permutation_process(data, result_sync, k, vec![t1_send, t2_send], main_recv);
/// }).join().unwrap();
/// ```
/// # See
/// - [k_permutation function](fn.k_permutation.html)
pub fn k_permutation_sync<'a, T>(d : &'a [T], k : usize, result : Arc<RwLock<Vec<&'a T>>>, mut cb : impl FnMut() -> ()) {
    assert_ne!(k, 0);
    assert_eq!(k, result.read().unwrap().len());
    large_combination_sync(d, k, Arc::clone(&result), || {
        cb();

        // save combination
        let origin = (*result).read().unwrap().to_owned();
        
        // permute the combination in place
        heap_permutation_sync(&result, || {
            cb();
        });

        // restore combination so next combination is properly produce
        origin.iter().enumerate().for_each(|(i, t)| result.write().unwrap()[i] = *t)
    });
}

/// A lexicographic ordered permutation based on ["Algoritm X" published by
/// Donald E. Knuth.](http://www.cs.utsa.edu/~wagner/knuth/fasc2b.pdf) page 20.
/// The sample implementation in C++ can be found in [Kevin Lynch 
/// repository.](https://gist.github.com/klynch/807973/cf05e785a68a5ae8b6a3381752583b97186f6140)
/// He implemented Algorithm X in an structured iterator style.
/// The discussion on how to implement "Algorithm X" in structured fashion in 
/// discussed [here](https://stackoverflow.com/questions/37079307/untying-knuths-knots-how-to-restructure-spaghetti-code)
/// The implementation here is inspired by the post from stackoverflow.
/// 
/// # Parameters
/// - d : &[T] - a data to be permuted
/// - result_fn : FnMut(usize, usize) - Function/Closure that responsible for
/// assign a data into result container. The first parameter is an index of result
/// to be re-assigned. The second parameter is an index of data to be assigned to result.
/// - t : FnMut(usize) -> bool - a function defined by "Algorithm X" that get called
/// by current "prefix" to check if such "prefix" need to be kept. If true, the
/// "prefix" will be kept. If false, the entire sub-tree with this "prefix" will be skip.
/// The parameter will be usize which is max bound of current result. The "prefix"
/// therefore shall be a subslice of range 0 till given parameter. For example,
/// result[0..k]
/// - cb : FnMut() - Callback function that shall return result to caller
fn _x_permutation_core<T>(d : &[T], mut result_fn : impl FnMut(usize, usize), mut t : impl FnMut(usize) -> bool, mut cb : impl FnMut()) {
    /// Return tuple of (a, k, l, n) where 
    /// - a is a Vec<usize>, array holding index of permuted.
    /// - k is usize and l is Vec<usize>
    /// Init value is k = 1
    /// - l is a Vec<usize>
    /// Init l[k] = k + 1 where 0 <= k < n
    /// l[n] = 0
    /// - n is usize, a length of data
    /// - perm is Vec<&T>, holding permuted value
    /// - u is Vec<usize>, holding undo vec 
    #[inline(always)]
    fn init<T>(d : &[T]) -> (Vec<usize>, usize, Vec<usize>, usize, Vec<usize>) {
        // l[k] = k + 1 where 0 <= k < n
        let mut l : Vec<usize> = (0..d.len()).map(|k| k + 1).collect();
        let a : Vec<usize> = (0..=d.len()).map(|v| v).collect();
        let n = d.len();
        let u = vec![0; n + 1];
        
        // l[n] = 0
        l.push(0);
        let k = 1;

        (a, k, l, n, u)
    };

    /// Return tuple of (p, q) where
    /// p = 0 and q = l[0]
    #[inline(always)]
    fn enter(l : &[usize]) -> (usize, usize) {
        return (0, l[0])
    }

    // "Algo X" X1
    let (mut a, mut k, mut l, n, mut u) = init(d);
    // "Algo X" X2
    let (mut p, mut q) = enter(&l);

    loop { 
        // "Algo X" X3
        // perm[k - 1] = &d[q - 1];
        result_fn(k - 1, q - 1);
        a[k] = q;

        if t(k) { // part of "Algo X" X3
            if k == n { // part of "Algo X" X3
                cb(); // visit part of "Algo X" X3

                loop { // condition of "Algo X" X5
                    // "Algo X" X6
                    k -= 1;

                    if k == 0 {
                        return;
                    } else {
                        p = u[k];
                        q = a[k];
                        l[p] = q;

                        // "Algo X" X5
                        p = q;
                        q = l[p];

                        if q != 0 {
                            break;
                        }
                    }
                }
            } else {
                // "Algo X" X4
                u[k] = p;
                l[p] = l[q];
                k += 1;

                // "Algo X" X2
                let (new_p, new_q) = enter(&l);
                p = new_p;
                q = new_q;
            }
        } else {
            // "Algo X" X5
            loop {
                p = q;
                q = l[p];

                if q != 0 {
                    break;
                }
                
                // "Algo X" X6
                k -= 1;

                if k == 0 {
                    return;
                } else {
                    p = u[k];
                    q = a[k];
                    l[p] = q;
                }
            }
        }
    }
}

/// A lexicographic ordered permutation based on ["Algoritm X" published by
/// Donald E. Knuth.](http://www.cs.utsa.edu/~wagner/knuth/fasc2b.pdf) page 20.
/// 
/// If order is not important, consider using [heap permutation](fn.heap_permutation.html)
/// function instead. This function is 3 times slower than [heap 
/// permutation](fn.heap_permutation.html) in uncontroll test environment.
/// 
/// The algorithm work by simulate tree traversal where some branch can be 
/// skip altogether. This is archive by provided `t` function that take 
/// slice of partial result as parameter. If the partial result needed to be skip,
/// return false. Otherwise, return true and the algorithm will call this function
/// again when the branch is descended deeper. For example: First call to `t` may
/// contain [1]. If `t` return true, it will be called again with [1, 2]. If it
/// return true, and there's leaf node, cb will be called with [1, 2]. On the other hand,
/// if `t` is called with [1, 3] and it return false, it won't call the callback.
/// If `t` is called with [4] and it return false, it won't try to traverse deeper even
/// if there're [4, 5], or [4, 6]. It will skip altogether and call `t` with [7].
/// The process goes on until every branch is traversed.
/// 
/// # Example
/// Get all lexicalgraphic ordered permutation
/// ```Rust
/// use permutator::x_permutation;
/// 
/// let data = vec![1, 2, 3, 4];
/// let mut counter = 0;
///
/// x_permutation(&data, |_| true, |p| {
///     println!("{:?}", p);
///     counter += 1;
/// });
///
/// assert_eq!(factorial(data.len()), counter);
/// ```
/// Skip all permutation that has `1` in first element. 
/// ```Rust
/// use permutator::x_permutation;
/// 
/// let data : Vec<u8> = vec![1, 2, 3, 4];
/// let mut counter = 0;
///
/// x_permutation(&data, |f| {
///     *f[0] != 1u8 // filter all permutation that start with 1
/// }, |p| {
///     println!("{:?}", p);
///     counter += 1;
/// });
///
/// assert_eq!(factorial(data.len()) - factorial(data.len() - 1), counter);
/// ```
/// Multi-threads permutation example
/// ```Rust
/// use std::sync::{Arc, RwLock};
/// use permutator::{get_permutation_for, x_permutation};
/// 
/// let mut data : Vec<u8> = (0..5u8).map(|v| v).collect();
/// let threads = 2usize;
/// let chunk = data.len() / threads; // split data into 3 threads.
/// let complete_count = Arc::new(RwLock::new(0u64));
/// let total_counter = Arc::new(RwLock::new(0u64));
/// for i in 0..threads {
///     let u_bound = match i {
///         j if j == threads - 1 => data.len() as u8, // last thread do all the rest
///         _ => (chunk * (i + 1)) as u8
///     };
///     let l_bound = (chunk * i) as u8;
///     let perm = get_permutation_for(&data, data.len(), l_bound as usize).unwrap();
///     let t_dat : Vec<u8> = perm.iter().map(|v| **v).collect(); // need to move to each thread
///     let t_counter = Arc::clone(&complete_count); // thread completed count
///     let loc_counter = Arc::clone(&total_counter); // count number of permutation
///     thread::spawn(move || {
///         let mut counter = 0u64;
///         x_permutation(&t_dat, |v| {
///             *v[0] >= l_bound && *v[0] < u_bound
///         }, |_p| {
///             counter += 1;
///         });
///
///         *loc_counter.write().unwrap() += counter;
///         println!("Done {} in local thread", counter);
///         *t_counter.write().unwrap() += 1;
///     });
/// }
///
/// let main = thread::spawn(move || {
///     let timer = Instant::now();
///     loop {
///         if *complete_count.read().unwrap() != (threads as u64) {
///             thread::sleep(Duration::from_millis(100));
///         } else {
///             println!("Done {} x_permutation {} threads in {:?}", &*total_counter.read().unwrap(), threads, timer.elapsed());
///             break;
///         }
///     }
/// });
///
/// main.join().unwrap();
/// ```
/// 
/// # Parameters
/// - d : &[T] - A data to get a permutation.
/// - t : FnMut(&[&T]) -> bool - A function for checking whether to traverse the branch.
/// It shall return true if the branch need to be traversed.
/// - cb : FnMut(&[&T]) - A callback function that return result to caller.
pub fn x_permutation<T>(d : &[T], mut t : impl FnMut(&[&T]) -> bool, mut cb : impl FnMut(&[&T])) {
    let mut perm : Vec<&T> = (0..d.len()).map(|i| &d[i]).collect();
    let perm_ptr = &perm as *const Vec<&T>;
    _x_permutation_core(
        d, 
        |i, j| {
            perm[i] = &d[j];
        }, |k| -> bool {
            unsafe { // should be safe as it got called after it mutated
                t(&(*perm_ptr)[0..k])
            }
        }, || { // should be safe as it got called after it mutated
            unsafe {
                cb(&(*perm_ptr))
            }
        }
    )
}

/// A lexicographic ordered permutation based on ["Algoritm X" published by
/// Donald E. Knuth.](http://www.cs.utsa.edu/~wagner/knuth/fasc2b.pdf) page 20.
/// 
/// If order is not important, consider using [heap permutation](fn.heap_permutation_cell.html)
/// function instead. This function is 3 times slower than heap [heap 
/// permutation](fn.heap_permutation_cell.html) in uncontroll test environment.
/// 
/// The algorithm work by simulate tree traversal where some branch can be 
/// skip altogether. This is archive by provided `t` function that take 
/// slice of partial result as parameter. If the partial result needed to be skip,
/// return false. Otherwise, return true and the algorithm will call this function
/// again when the branch is descended deeper. For example: First call to `t` may
/// contain [1]. If `t` return true, it will be called again with [1, 2]. If it
/// return true, and there's leaf node, cb will be called with [1, 2]. On the other hand,
/// if `t` is called with [1, 3] and it return false, it won't call the callback.
/// If `t` is called with [4] and it return false, it won't try to traverse deeper even
/// if there're [4, 5], or [4, 6]. It will skip altogether and call `t` with [7].
/// The process goes on until every branch is traversed.
/// 
/// # Example
/// See [x_permutation document](fn.x_permutation.html) for example.
/// It's the same except the way it return result.
/// 
/// # Parameters
/// - d : &[T] - A data to get a permutation.
/// - result : Rc<RefCell<&mut [&T]>> - A result container.
/// The result will be overwritten on each call to callback. 
/// - t : FnMut(&[&T]) -> bool - A function for checking whether to traverse the branch.
/// It shall return true if the branch need to be traversed.
/// - cb : FnMut() - A callback function that notify caller that new result is available.
pub fn x_permutation_cell<'a, T>(d : &'a [T], result : Rc<RefCell<&mut [&'a T]>>,mut t : impl FnMut(&[&T]) -> bool, mut cb : impl FnMut()) {
    assert_eq!(result.borrow().len(), d.len(), "`result` shall has length equals to `d`");
    { // init result
        let mut mutable_res = result.borrow_mut();
        (0..d.len()).for_each(|i| mutable_res[i] = &d[i]);
    }
    
    _x_permutation_core(
        d, 
        |i, j| {
            result.borrow_mut()[i] = &d[j];
        }, |k| -> bool {
            t(&result.borrow()[0..k])
        }, || { // should be safe as it got called after it mutated
            cb()
        }
    )
}

/// A lexicographic ordered permutation based on ["Algoritm X" published by
/// Donald E. Knuth.](http://www.cs.utsa.edu/~wagner/knuth/fasc2b.pdf) page 20.
/// 
/// If order is not important, consider using [heap permutation](fn.heap_permutation_sync.html)
/// function instead. This function is 3 times slower than heap [heap 
/// permutation](fn.heap_permutation_sync.html) in uncontroll test environment.
/// 
/// The algorithm work by simulate tree traversal where some branch can be 
/// skip altogether. This is archive by provided `t` function that take 
/// slice of partial result as parameter. If the partial result needed to be skip,
/// return false. Otherwise, return true and the algorithm will call this function
/// again when the branch is descended deeper. For example: First call to `t` may
/// contain [1]. If `t` return true, it will be called again with [1, 2]. If it
/// return true, and there's leaf node, cb will be called with [1, 2]. On the other hand,
/// if `t` is called with [1, 3] and it return false, it won't call the callback.
/// If `t` is called with [4] and it return false, it won't try to traverse deeper even
/// if there're [4, 5], or [4, 6]. It will skip altogether and call `t` with [7].
/// The process goes on until every branch is traversed.
/// 
/// # Example
/// See [x_permutation document](fn.x_permutation.html) for example.
/// It's the same except the way it return result.
/// 
/// # Parameters
/// - d : &[T] - A data to get a permutation.
/// - result : Arc<RwLock<Vec<&T>>> - A result container.
/// The result will be overwritten on each call to callback. 
/// - t : FnMut(&[&T]) -> bool - A function for checking whether to traverse the branch.
/// It shall return true if the branch need to be traversed.
/// - cb : FnMut() - A callback function that notify caller that new result is available.
pub fn x_permutation_sync<'a, T>(d : &'a [T], result : Arc<RwLock<Vec<&'a T>>>,mut t : impl FnMut(&[&T]) -> bool, mut cb : impl FnMut()) {
    assert_eq!(result.read().unwrap().len(), d.len(), "`result` shall has length equals to `d`");
    { // init result
        let mut mutable_res = result.write().unwrap();
        (0..d.len()).for_each(|i| mutable_res[i] = &d[i]);
    }
    
    _x_permutation_core(
        d, 
        |i, j| {
            result.write().unwrap()[i] = &d[j];
        }, |k| -> bool {
            t(&result.read().unwrap()[0..k])
        }, || { // should be safe as it got called after it mutated
            cb()
        }
    )
}

/// A lexicographic ordered permutation based on ["Algoritm X" published by
/// Donald E. Knuth.](http://www.cs.utsa.edu/~wagner/knuth/fasc2b.pdf) page 20.
/// 
/// If order is not important, consider using [heap permutation](fn.unsafe_heap_permutation.html)
/// function instead. This function is 3 times slower than heap [heap 
/// permutation](fn.unsafe_heap_permutation.html) in uncontroll test environment.
/// 
/// The algorithm work by simulate tree traversal where some branch can be 
/// skip altogether. This is archive by provided `t` function that take 
/// slice of partial result as parameter. If the partial result needed to be skip,
/// return false. Otherwise, return true and the algorithm will call this function
/// again when the branch is descended deeper. For example: First call to `t` may
/// contain [1]. If `t` return true, it will be called again with [1, 2]. If it
/// return true, and there's leaf node, cb will be called with [1, 2]. On the other hand,
/// if `t` is called with [1, 3] and it return false, it won't call the callback.
/// If `t` is called with [4] and it return false, it won't try to traverse deeper even
/// if there're [4, 5], or [4, 6]. It will skip altogether and call `t` with [7].
/// The process goes on until every branch is traversed.
/// 
/// # Example
/// See [x_permutation document](fn.x_permutation.html) for example.
/// It's the same except the way it return result.
/// 
/// # Parameters
/// - d : &[T] - A data to get a permutation.
/// - result : *mut [&T] - A result container.
/// The result will be overwritten on each call to callback. 
/// - t : FnMut(&[&T]) -> bool - A function for checking whether to traverse the branch.
/// It shall return true if the branch need to be traversed.
/// - cb : FnMut() - A callback function that notify caller that new result is available.
/// 
/// # Safety
/// This function is unsafe to used. This function store result into raw pointer thus all 
/// unsafe Rust condition may applied. For example, it may seg fault if pointer is invalid. 
/// It may cause datarace. It may leak memory.
/// 
/// # Rationale
/// This function permit sharing data to other without cost by sacrifice the safety.
/// For safely share result in single thread, consider using 
/// [x_permutation_cell](fn.x_permutation_cell.html). For safely share result in
/// multi-threads, consider using [x_permutation_sync](fn.x_permutation_sync.html).
/// Both functions have some cost due to additional safety check.
pub unsafe fn unsafe_x_permutation<'a, T>(d : &'a [T], result : *mut [&'a T], mut t : impl FnMut(&[&T]) -> bool, mut cb : impl FnMut()) {
    assert_eq!((*result).len(), d.len(), "`result` shall has length equals to `d`");
    (0..d.len()).for_each(|i| (*result)[i] = &d[i]);
    
    _x_permutation_core(
        d, 
        |i, j| {
            (*result)[i] = &d[j];
        }, |k| -> bool {
            t(&(*result)[0..k])
        }, || { // should be safe as it got called after it mutated
            cb()
        }
    )
}

/// A trait that add reset function to an existing Iterator.
/// It mean that the `next` or `next_into_cell` call will start returning
/// the first element again
pub trait IteratorReset {
    /// Reset an iterator. It make an iterator start from the beginning again.
    fn reset(&mut self);
}

/// Core algorithm of `next` function for all `CartesianProduct` iterator
/// family.
/// 
/// # Parameters
/// 1. `i` - ref mut usize which is cursor pointed to domain inside domains
/// 2. `c` - ref mut Vec of usize which is cursor of each domain
/// 3. `exhausted` - boolean which if true mean iterator is exhausted
/// 4. `n` - number of domains
/// 5. `domain_len` - is a closure that take usize and return size of 
/// the domain at given usize
#[inline(always)]
fn _cartesian_next_core<'a>(
    i : &mut usize, 
    c : &mut Vec<usize>, 
    exhausted : &mut bool,
    n : usize,
    domain_len : impl Fn(usize) -> usize,
    mut into_result : impl FnMut(usize, usize) + 'a) 
{
    // move and set `result` and `c` up until all `domains` processed
    while *i < n && ! *exhausted {
        // if current domain is exhausted.
        if c[*i] == domain_len(*i) {
            // reset all exhausted domain in `result` and `c`
            let mut k = *i;

            // reset all exhausted until either found non-exhausted or reach first domain
            while c[k] == domain_len(k) && k > 0 {
                c[k] = 1;
                into_result(k, 0);
                k -= 1;
            }

            if k == 0 && c[k] == domain_len(k) {
                // if first domain is also exhausted then flag it.
                *exhausted = true;
            } else {
                // otherwise advance c[k] and set result[k] to next value
                // self.result[k] = &self.domains[k][self.c[k]];
                into_result(k, c[k]);
                c[k] += 1;
            }
        } else {
            // non exhausted domain, advance `c` and set result
            // self.result[self.i] = &self.domains[self.i][self.c[self.i]];
            into_result(*i, c[*i]);
            c[*i] += 1;
        }
        *i += 1;
    }
}

/// Generate a cartesian product between given domains in an iterator style.
/// The struct implement `Iterator` trait so it can be used in `Iterator` 
/// style. The struct provide [into_iter()](#method.into_iter()) function 
/// that return itself.
/// 
/// # Example
/// ```
///    use permutator::CartesianProductIterator;
///    use std::time::Instant;
///    let data : &[&[usize]] = &[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]];
///    let cart = CartesianProductIterator::new(&data);
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    for p in cart {
///        // println!("{:?}", p);
///        counter += 1;
///    }
/// 
///    // or functional style like the line below
///    // cart.into_iter().for_each(|p| {/* do something iterative style */});
///
///    assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
///    println!("Total {} products done in {:?}", counter, timer.elapsed());
/// ```
pub struct CartesianProductIterator<'a, T> where T : 'a {
    c : Vec<usize>,
    domains : &'a [&'a [T]],
    exhausted : bool,
    i : usize,

    result : Vec<&'a T>
}

impl<'a, T> CartesianProductIterator<'a, T> where T : 'a {
    /// Create a new Cartesian product iterator that create a product between
    /// each domain inside `domains`.
    /// # Parameters
    /// - `domains` A slice of domains to create a cartesian product between
    /// each domain inside it.
    /// # Return
    /// An object that can be iterate over in iterator style.
    pub fn new(domains : &'a[&[T]]) -> CartesianProductIterator<'a, T> {

        CartesianProductIterator {
            c : vec![0; domains.len()],
            domains : domains,
            exhausted : false,
            i : 0,

            result : vec![&domains[0][0]; domains.len()]
        }
    }

    /// Consume itself and return without modify it.
    /// Typical usecase is `for p in ref_to_this.into_iter() {}`
    /// or `ref_to_this.into_iter().for_each(|p| {/* Do something with product */});`
    pub fn into_iter(self) -> Self {
        self
    }
}

impl<'a, T> Iterator for CartesianProductIterator<'a, T> {
    type Item = Vec<&'a T>;

    /// Each iteration return a new Vec contains borrowed element inside
    /// an Option. The result can be collected by using `collect` method
    /// from `Iterator` trait.
    /// 
    /// Return None when exhausted.
    fn next(&mut self) -> Option<Vec<&'a T>> {
        let domains = self.domains;
        let result = &mut self.result;
        _cartesian_next_core(
            &mut self.i, 
            &mut self.c, 
            &mut self.exhausted,
            domains.len(),
            #[inline(always)]
            |k| {
                domains[k].len()
            },
            #[inline(always)]
            |i, j| {
                result[i] = &domains[i][j];
            }
        );

        if self.exhausted {
            None
        } else {
            self.i -= 1; // rewind `i` back to last domain
            Some(result.to_owned())
        }
    }
}

impl<'a, T> IteratorReset for CartesianProductIterator<'a, T> {
    fn reset(&mut self) {
        self.c = vec![0; self.domains.len()];
        self.exhausted = false;
        self.i = 0;
    }
}

impl<'a, T> ExactSizeIterator for CartesianProductIterator<'a, T> {
    fn len(&self) -> usize {
        self.domains.iter().fold(1, |cum, d| {cum * d.len()})
    }
}

/// Generate a cartesian product between given domains into Rc<RefCell<&mut [&T]>>
/// in an iterator style.
/// The struct implement `Iterator` trait so it can be used as `Iterator`. 
/// The struct provide [into_iter()](#method.into_iter()) function 
/// that return itself.
/// 
/// # Example
/// - Iterator style usage
/// ```
///    use permutator::CartesianProductCellIter;
///    use std::cell::RefCell;
///    use std::rc::Rc;
///    use std::time::Instant;
///    let data : Vec<&[usize]> = vec![&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]];
///    let mut result : Vec<&usize> = vec![&data[0][0]; data.len()];
///    let shared = Rc::new(RefCell::new(result.as_mut_slice()));
///    let cart = CartesianProductCellIter::new(&data, Rc::clone(&shared));
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    for _ in cart {
///        println!("{:?}", &*shared.borrow());
///        counter += 1;
///    }
/// 
///    // or functional style like the line below
///    // cart.into_iter().for_each(|_| {/* do something iterative style */});
///
///    assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
///    println!("Total {} products done in {:?}", counter, timer.elapsed());
/// ```
pub struct CartesianProductCellIter<'a, T> where T : 'a {
    c : Vec<usize>,
    domains : &'a [&'a [T]],
    exhausted : bool,
    i : usize,

    result : Rc<RefCell<&'a mut [&'a T]>>
}

impl<'a, T> CartesianProductCellIter<'a, T> {
    pub fn new(data : &'a [&'a [T]], result : Rc<RefCell<&'a mut [&'a T]>>) -> CartesianProductCellIter<'a, T> {
        CartesianProductCellIter {
            c : vec![0; data.len()],
            domains : data,
            exhausted : false,
            i : 0,

            result : result
        }
    }

    pub fn into_iter(self) -> Self {
        self
    }
}

impl<'a, T> Iterator for CartesianProductCellIter<'a, T> where T : 'a {
    type Item = ();

    /// Mimic iterator `next` function but return value into Rc<RefCell<>> that
    /// contains mutable slice. It also return an empty Option to tell caller
    /// to distinguish if it's put new value or the iterator itself is exhausted.
    /// # Paramerter
    /// - `result` An Rc<RefCell<>> contains a mutable slice with length equals
    /// to number of `domains` given in [CartesianProductIterator::new()](struct.CartesianProductIterator.html#method.new).
    /// The value inside result will be updated everytime this function is called
    /// until the function return None. The performance using this function is
    /// on part with [cartesian_cell function](fn.cartesian_product_cell.html) on uncontrol
    /// test environment.
    /// # Return
    /// New cartesian product between each `domains` inside `result` parameter 
    /// and also return `Some(())` if result is updated or `None` when there's
    /// no new result.
    fn next(&mut self) -> Option<()> {
        let mut result = self.result.borrow_mut();
        let domains = self.domains;
        _cartesian_next_core(
            &mut self.i, 
            &mut self.c, 
            &mut self.exhausted,
            domains.len(),
            #[inline(always)]
            |k| {
                domains[k].len()
            },
            #[inline(always)]
            |i, j| {
                result[i] = &domains[i][j];
            }
        );

        if self.exhausted {
            None
        } else {
            self.i -= 1; // rewind `i` back to last domain
            
            Some(())
        }
    }
}

impl<'a, T> IteratorReset for CartesianProductCellIter<'a, T> {
    fn reset(&mut self) {
        self.c.iter_mut().for_each(|c| {*c = 0});
        self.exhausted = false;
        self.i = 0;
    }
}

impl<'a, T> ExactSizeIterator for CartesianProductCellIter<'a, T> {
    fn len(&self) -> usize {
        self.domains.iter().fold(1, |cum, d| {cum * d.len()})
    }
}

/// An unsafe way to generate a cartesian product between given domains 
/// into *mut [&T] in an iterator style.
/// The struct implement `Iterator` trait so it can be used as `Iterator`. 
/// The struct provide [into_iter()](#method.into_iter()) function 
/// that return itself.
/// 
/// # Unsafe
/// It took mutable pointer to slice in 
/// [object instantiation](struct.CartesianProductRefIter.html#method.new)
/// and convert it upon creation into mutable borrowed slice.
/// All unsafe Rust conditions, therefore, applied to entire usage
/// of this struct.
/// 
/// # Rationale
/// It uses unsafe to take a mutable pointer to store the result
/// to avoid the cost of using Rc<RefCell<>>. 
/// In uncontroll test environment, this struct perform a complete
/// iteration over 12,960 products in about 110ms where 
/// [CartesianProductCellIter](struct.CartesianProductCellIter.html)
/// took about 130ms.
/// This function is very much alike 
/// [unsafe_cartesian_product function](fn.unsafe_cartesian_product.html)
/// but took `Iterator` approach.
/// 
/// # Example
/// - Iterator style usage
/// ```
///    use permutator::CartesianProductRefIter;
///    use std::time::Instant;
///    let data : Vec<&[usize]> = vec![&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]];
///    let mut result : Vec<&usize> = vec![&data[0][0]; data.len()];
///    unsafe {
///         let cart = CartesianProductRefIter::new(&data, result.as_mut_slice() as *mut [&usize]);
///         let mut counter = 0;
///         let timer = Instant::now();
///
///         for _ in cart {
///             println!("{:?}", result);
///         counter += 1;
///         }
/// 
///         // or functional style like the line below
///         // cart.into_iter().for_each(|_| {/* do something iterative style */});
///
///         assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
///         println!("Total {} products done in {:?}", counter, timer.elapsed());
///    }
/// ```
pub struct CartesianProductRefIter<'a, T> where T : 'a {
    c : Vec<usize>,
    domains : &'a [&'a [T]],
    exhausted : bool,
    i : usize,

    result : &'a mut [&'a T]
}

impl<'a, T> CartesianProductRefIter<'a, T> {
    /// Create an iterator with mutable pointer to store the product.
    /// It is unsafe because it convert mutable pointer into mutable borrowed value 
    /// upon creating the object.
    /// 
    /// # Parameter
    /// - `data` a borrowed slice contains borrowed slices. It's
    /// domains of cartesian product operation.
    /// - `result` a mutable pointer pointed to the slice that
    /// will be used to store the cartesian product result.
    /// The length of the slice shall equals to len of data.
    /// 
    /// # Return
    /// Each iteration return empty Option and store actual result into
    /// `result` given when construct this `Iterator`.
    pub unsafe fn new(data : &'a [&'a [T]], result : *mut [&'a T]) -> CartesianProductRefIter<'a, T> {
        CartesianProductRefIter {
            c : vec![0; data.len()],
            domains : data,
            exhausted : false,
            i : 0,

            result : &mut *result
        }
    }

    pub fn into_iter(self) -> Self {
        self
    }
}

impl<'a, T> Iterator for CartesianProductRefIter<'a, T> where T : 'a {
    type Item = ();

    /// Mimic iterator `next` function but return value into Rc<RefCell<>> that
    /// contains mutable slice. It also return an empty Option to tell caller
    /// to distinguish if it's put new value or the iterator itself is exhausted.
    /// # Paramerter
    /// - `result` An Rc<RefCell<>> contains a mutable slice with length equals
    /// to number of `domains` given in [CartesianProductIterator::new()](struct.CartesianProductIterator.html#method.new).
    /// The value inside result will be updated everytime this function is called
    /// until the function return None. The performance using this function is
    /// on part with [cartesian_cell function](fn.cartesian_product_cell.html) on uncontrol
    /// test environment.
    /// # Return
    /// New cartesian product between each `domains` inside `result` parameter 
    /// and also return `Some(())` if result is updated or `None` when there's
    /// no new result.
    fn next(&mut self) -> Option<()> {
        let result = &mut self.result;
        let domains = self.domains;
        _cartesian_next_core(
            &mut self.i, 
            &mut self.c, 
            &mut self.exhausted,
            domains.len(),
            #[inline(always)]
            |k| {
                domains[k].len()
            },
            #[inline(always)]
            |i, j| {
                result[i] = &domains[i][j];
            }
        );

        if self.exhausted {
            None
        } else {
            self.i -= 1; // rewind `i` back to last domain
            
            Some(())
        }
    }
}

impl<'a, T> IteratorReset for CartesianProductRefIter<'a, T> {
    fn reset(&mut self) {
        self.c.iter_mut().for_each(|c| {*c = 0});
        self.exhausted = false;
        self.i = 0;
    }
}

impl<'a, T> ExactSizeIterator for CartesianProductRefIter<'a, T> {
    fn len(&self) -> usize {
        self.domains.iter().fold(1, |cum, d| {cum * d.len()})
    }
}

/// A core logic of `next` function of `GosperCombination` iterator family.
/// 
/// # Parameters
/// 1. `map` - a ref mut pointed to gosper map
/// 2. `into_result` - closure that take two usizes. First usize is
/// incremented on each call by 1. Second usize is index of which
/// data that is mapped by gosper's map.
#[inline(always)]
fn _gosper_next_core(map : &mut u128, mut into_result : impl FnMut(usize, usize)) {
    let mut i = 0;
    let mut j = 0;
    let mut mask = *map;
    while mask > 0 {
        if mask & 1 == 1 {
            into_result(i, j);
            i += 1;
        }

        mask >>= 1;
        j += 1;
    }

    stanford_combination(map);
}

/// # Deprecated
/// This iterator family is now deprecated.
/// Consider using [LargeCombinationIterator](struct.LargeCombinationIterator.html)
/// instead. This is because current implementation need to copy every ref
/// on every iteration which is inefficient. 
/// On uncontroll test environment, this iterator take 18.98s to iterate over
/// 30,045,015 combinations. The [LargeCombinationIterator](struct.LargeCombinationIterator.html)
/// took only 2.77s.
/// If no more efficient implementation is available for some certain time period,
/// this function will be officially mark with #[deprecated].
/// 
/// Create a combination iterator.
/// It use Gosper's algorithm to pick a combination out of
/// given data. The produced combination provide no lexicographic
/// order.
/// 
/// The returned combination will be a reference into given data.
/// Each combination return from iterator will be a new Vec.
/// It's safe to hold onto a combination or `collect` it.
/// 
/// # Examples
/// Given slice of [1, 2, 3, 4, 5]. It will produce following
/// combinations:
/// [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4], [1, 2, 5],
/// [1, 3, 5], [2, 3, 5], [1, 4, 5], [2, 4, 5], [3, 4, 5]
/// Here's an example of code printing above combination.
/// ```
///    use permutator::GosperCombinationIterator;
///    use std::time::{Instant};
///    let gosper = GosperCombinationIterator::new(&[1, 2, 3, 4, 5], 3);
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    for combination in gosper {
///        println!("{}:{:?}", counter, combination);
///        counter += 1;
///    }
///
///    println!("Total {} combinations in {:?}", counter, timer.elapsed());
/// ```
/// # Limitation
/// Gosper algorithm need to know the MSB (most significant bit).
/// The current largest known MSB data type is u128.
/// This make the implementation support up to 128 elements slice.
/// 
/// # See
/// - [Gospel's algorithm in Wikipedia page, October 9, 2018](https://en.wikipedia.org/wiki/Combinatorial_number_system#Applications)
pub struct GosperCombinationIterator<'a, T> where T : 'a {
    data : &'a [T], // data to generate a combination
    len : usize, // total possible number of combination.
    r : usize, // a size of combination.
    x : u128, // A binary map to generate combination
}

impl<'a, T> GosperCombinationIterator<'a, T> {
    /// Create new combination generator using Gosper's algorithm.
    /// `r` shall be smaller than data.len(). 
    /// 
    /// Note: It perform no check on given parameter. 
    /// If r is larger than length of data then iterate over it
    /// will not occur. The iteration will be end upon enter.
    pub fn new(data : &[T], r : usize) -> GosperCombinationIterator<T> {
        let mut x : u128 = 1;
        x <<= r;
        x -= 1;
        let n = data.len();
        GosperCombinationIterator {
            data : data,
            len : divide_factorial(n, multiply_factorial(n - r, r)),
            r : r,
            x : x
        }
    }

    /// Total number of combinations this iterate can return.
    /// It will equals to n!/((n-r)!*r!)
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn reset(&mut self) {
        self.x = 1;
        self.x <<= self.r;
        self.x -= 1;
    }
}

impl<'a, T> IntoIterator for GosperCombinationIterator<'a, T> {
    type Item = Vec<&'a T>;
    type IntoIter = CombinationIterator<'a, T>;

    fn into_iter(self) -> CombinationIterator<'a, T> {
        CombinationIterator {
            data : self.data,
            r : self.r,
            x : self.x
        }
    }
}

/// # Deprecated
/// 
/// An iterator return from [struct GosperCombination](struct.GosperCombinationIterator.html)
/// or from [trait Combination](trait.Combination.html) over slice or vec of data.
pub struct CombinationIterator<'a, T> where T : 'a {
    data : &'a [T], // original data
    r : usize, // len of each combination
    x : u128, // Gosper binary map
}

impl<'a, T> Iterator for CombinationIterator<'a, T> {
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Vec<&'a T>> {
        let mut combination : Vec<&T> = Vec::new();

        if 128 - self.x.leading_zeros() as usize > self.data.len() {
            return None
        } 

        // stanford_combination(&mut self.x);
        let data = self.data;
        let map = &mut self.x;
        _gosper_next_core(map, 
            #[inline(always)]
            |_, j| {
                combination.push(&data[j]);
            }
        );

        return Some(combination)
    }
}

impl<'a, T> IteratorReset for CombinationIterator<'a, T> {
    fn reset(&mut self) {
        self.x = 1;
        self.x <<= self.r;
        self.x -= 1;
    }
}

impl<'a, T> ExactSizeIterator for CombinationIterator<'a, T> {
    fn len(&self) -> usize {
        let n = self.data.len();
        divide_factorial(n, multiply_factorial(n - self.r, self.r))
    }
}

/// # Deprecated
/// This iterator family is now deprecated.
/// Consider using [LargeCombinationCellIter](struct.LargeCombinationCellIter.html)
/// instead. This is because current implementation need to copy every ref
/// on every iteration which is inefficient. 
/// On uncontroll test environment, this iterator take 2.49s to iterate over
/// 30,045,015 combinations. The [LargeCombinationCellIter](struct.LargeCombinationCellIter.html)
/// took only 446.39ms.
/// 
/// Create a combination iterator.
/// It use Gosper's algorithm to pick a combination out of
/// given data. The produced combination provide no lexicographic
/// order.
/// 
/// The returned combination will be a reference into given data.
/// Each combination return from iterator by storing into given
/// Rc<RefCell<&mut [&T]>> along with empty Option.
/// 
/// # Examples
/// Given slice of [1, 2, 3, 4, 5]. It will produce following
/// combinations:
/// [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4], [1, 2, 5],
/// [1, 3, 5], [2, 3, 5], [1, 4, 5], [2, 4, 5], [3, 4, 5]
/// Here's an example of code printing above combination.
/// ```
///    use permutator::{GosperCombinationCellIter};
///    use std::cell::RefCell;
///    use std::rc::Rc;
///    use std::time::{Instant};
///    let data = &[1, 2, 3, 4, 5];
///    let mut result : &mut[&i32] = &mut [&data[0]; 3];
///    let shared = Rc::new(RefCell::new(result));
///    let mut gosper = GosperCombinationCellIter::new(&[1, 2, 3, 4, 5], 3, Rc::clone(&shared));
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    for _ in gosper {
///        println!("{}:{:?}", counter, shared);
///        counter += 1;
///    }
///
///    println!("Total {} combinations in {:?}", counter, timer.elapsed());
/// ```
/// 
/// # Limitation
/// Gosper algorithm need to know the MSB (most significant bit).
/// The current largest known MSB data type is u128.
/// This make the implementation support up to 128 elements slice.
/// 
/// # See
/// - [Gospel's algorithm in Wikipedia page, October 9, 2018](https://en.wikipedia.org/wiki/Combinatorial_number_system#Applications)
pub struct GosperCombinationCellIter<'a, T> where T : 'a {
    data : &'a [T], // data to generate a combination
    len : usize, // total possible number of combination.
    r : usize, // a size of combination.
    x : u128, // A binary map to generate combination

    result : Rc<RefCell<&'a mut [&'a T]>>
}

impl<'a, T> GosperCombinationCellIter<'a, T> {
    /// Create new combination generator using Gosper's algorithm.
    /// `r` shall be smaller than data.len(). 
    /// 
    /// Note: It perform no check on given parameter. 
    /// If r is larger than length of data then iterate over it
    /// will not occur. The iteration will be end upon enter.
    pub fn new(data : &'a [T], r : usize, result : Rc<RefCell<&'a mut [&'a T]>>) -> GosperCombinationCellIter<'a, T> {
        let mut x : u128 = 1;
        x <<= r;
        x -= 1;
        let n = data.len();
        GosperCombinationCellIter {
            data : data,
            len : divide_factorial(n, multiply_factorial(n - r, r)),
            r : r,
            x : x,

            result : result
        }
    }

    /// Total number of combinations this iterate can return.
    /// It will equals to n!/((n-r)!*r!)
    pub fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> IntoIterator for GosperCombinationCellIter<'a, T> {
    type Item = ();
    type IntoIter = CombinationCellIter<'a, T>;

    fn into_iter(self) -> CombinationCellIter<'a, T> {
        CombinationCellIter {
            data : self.data,
            r : self.r,
            x : self.x,

            result : self.result
        }
    }
}

/// # Deprecated
/// 
/// An iterator return from [struct GosperCombination](struct.GosperCombinationIterator.html)
/// or from [trait Combination](trait.Combination.html) over slice or vec of data.
pub struct CombinationCellIter<'a, T> where T : 'a {
    data : &'a [T], // original data
    r : usize, // len of each combination
    x : u128, // Gosper binary map

    result : Rc<RefCell<&'a mut[&'a T]>>
}

impl<'a, T> Iterator for CombinationCellIter<'a, T> {
    type Item = ();

    fn next(&mut self) -> Option<()> {
        if 128 - self.x.leading_zeros() as usize > self.data.len() {
            return None
        } 
        // else {
        //     let mut i = 0;
        //     let mut j = 0;
        //     let mut mask = self.x;
        //     while mask > 0 {
        //         if mask & 1 == 1 {
        //             self.result.borrow_mut()[i] = &self.data[j];
        //             i += 1;
        //         }

        //         mask >>= 1;
        //         j += 1;
        //     }
        // }

        // stanford_combination(&mut self.x);
        
        let data = self.data;
        let map = &mut self.x;
        let mut result = self.result.borrow_mut();
        _gosper_next_core(map, 
            #[inline(always)]
            |i, j| {
                result[i] = &data[j];
            }
        );

        return Some(())
    }
}

impl<'a, T> IteratorReset for CombinationCellIter<'a, T> {
    fn reset(&mut self) {
        self.x = 1;
        self.x <<= self.r;
        self.x -= 1;
    }
}

impl<'a, T> ExactSizeIterator for CombinationCellIter<'a, T> {
    fn len(&self) -> usize {
        let n = self.data.len();
        divide_factorial(n, multiply_factorial(n - self.r, self.r))
    }
}


/// # Deprecated
/// This iterator family is now deprecated.
/// Consider using [LargeCombinationCellIter](struct.LargeCombinationCellIter.html)
/// instead. This is because current implementation need to copy every ref
/// on every iteration which is inefficient. 
/// On uncontroll test environment, this iterator take 2.29s to iterate over
/// 30,045,015 combinations. The [LargeCombinationCellIter](struct.LargeCombinationCellIter.html)
/// took only 345.44ms.
/// 
/// Create an unsafe combination iterator that return result to mutable pointer.
/// It use Gosper's algorithm to pick a combination out of
/// given data. The produced combination provide no lexicographic
/// order.
/// 
/// The returned combination will be a reference into given data.
/// Each combination return from iterator by storing into given
/// *mut [&T] along with empty Option.
/// 
/// # Unsafe
/// This object took raw mutable pointer and convert in upon object
/// instantiation via [new function](struct.GosperCombinationRefIter.html#method.new)
/// thus all unsafe Rust conditions will be applied on all method.
/// 
/// # Rationale
/// It uses unsafe to take a mutable pointer to store the result
/// to avoid the cost of using Rc<RefCell<>>. 
/// In uncontroll test environment, this struct perform a complete
/// iteration over 657,800 combinations in about 47ms where 
/// [GosperCombinationCellIter](struct.GosperCombinationCellIter.html)
/// took about 52ms.
/// This function is very much alike 
/// [unsafe_combination function](fn.unsafe_combination.html)
/// but took `Iterator` approach.
/// 
/// # Examples
/// Given slice of [1, 2, 3, 4, 5]. It will produce following
/// combinations:
/// [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4], [1, 2, 5],
/// [1, 3, 5], [2, 3, 5], [1, 4, 5], [2, 4, 5], [3, 4, 5]
/// Here's an example of code printing above combination.
/// ```
///    use permutator::{GosperCombinationRefIter};
///    use std::time::{Instant};
///    let data = &[1, 2, 3, 4, 5];
///    let mut result : &mut[&i32] = &mut [&data[0]; 3];
///    unsafe {
///         let mut gosper = GosperCombinationRefIter::new(&[1, 2, 3, 4, 5], 3, result as *mut [&i32]);
///         let mut counter = 0;
///         let timer = Instant::now();
///
///         for _ in gosper {
///             println!("{}:{:?}", counter, result);
///             counter += 1;
///         }
///
///         println!("Total {} combinations in {:?}", counter, timer.elapsed());
///    }
/// ```
/// 
/// # Limitation
/// Gosper algorithm need to know the MSB (most significant bit).
/// The current largest known MSB data type is u128.
/// This make the implementation support up to 128 elements slice.
/// 
/// # See
/// - [Gospel's algorithm in Wikipedia page, October 9, 2018](https://en.wikipedia.org/wiki/Combinatorial_number_system#Applications)
pub struct GosperCombinationRefIter<'a, T> where T : 'a {
    data : &'a [T], // data to generate a combination
    len : usize, // total possible number of combination.
    r : usize, // a size of combination.
    x : u128, // A binary map to generate combination

    result : &'a mut [&'a T]
}

impl<'a, T> GosperCombinationRefIter<'a, T> {
    /// Create new combination generator using Gosper's algorithm.
    /// `r` shall be smaller than data.len(). 
    /// 
    /// Note: It perform no check on given parameter. 
    /// If r is larger than length of data then iterate over it
    /// will not occur. The iteration will be end upon enter.
    pub unsafe fn new(data : &'a [T], r : usize, result : *mut [&'a T]) -> GosperCombinationRefIter<'a, T> {
        let mut x : u128 = 1;
        x <<= r;
        x -= 1;
        let n = data.len();
        GosperCombinationRefIter {
            data : data,
            len : divide_factorial(n, multiply_factorial(n - r, r)),
            r : r,
            x : x,

            result : &mut *result
        }
    }

    /// Total number of combinations this iterate can return.
    /// It will equals to n!/((n-r)!*r!)
    pub fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> IntoIterator for GosperCombinationRefIter<'a, T> {
    type Item = ();
    type IntoIter = CombinationRefIter<'a, T>;

    fn into_iter(self) -> CombinationRefIter<'a, T> {
        CombinationRefIter {
            data : self.data,
            r : self.r,
            x : self.x,

            result : self.result
        }
    }
}

/// # Deprecated
/// 
/// An iterator return from [struct GosperCombination](struct.GosperCombinationIterator.html)
/// or from [trait Combination](trait.Combination.html) over slice or vec of data.
pub struct CombinationRefIter<'a, T> where T : 'a {
    data : &'a [T], // original data
    r : usize, // len of each combination
    x : u128, // Gosper binary map

    result : &'a mut[&'a T]
}

impl<'a, T> Iterator for CombinationRefIter<'a, T> {
    type Item = ();

    fn next(&mut self) -> Option<()> {
        if 128 - self.x.leading_zeros() as usize > self.data.len() {
            return None
        } 
        // else {
        //     let mut i = 0;
        //     let mut j = 0;
        //     let mut mask = self.x;
        //     while mask > 0 {
        //         if mask & 1 == 1 {
        //             self.result[i] = &self.data[j];
        //             i += 1;
        //         }

        //         mask >>= 1;
        //         j += 1;
        //     }
        // }

        // stanford_combination(&mut self.x);
        let data = self.data;
        let map = &mut self.x;
        let result = &mut self.result;
        _gosper_next_core(map, 
            #[inline(always)]
            |i, j| {
                result[i] = &data[j];
            }
        );

        return Some(())
    }
}

impl<'a, T> IteratorReset for CombinationRefIter<'a, T> {
    fn reset(&mut self) {
        self.x = 1;
        self.x <<= self.r;
        self.x -= 1;
    }
}

impl<'a, T> ExactSizeIterator for CombinationRefIter<'a, T> {
    fn len(&self) -> usize {
        let n = self.data.len();
        divide_factorial(n, multiply_factorial(n - self.r, self.r))
    }
}

/// A core logic of `next` function of `LargeCombination` iterator family.
/// 
/// # Parameters
/// 1. `c` - a ref mut slice to usize. It's current cursor state in iterator
/// 2. `data` - a ref slice to data to get a combination from.
/// 3. `iterated` - A ref mut to empty Option. If none, it mean this is first call
/// to the function.
/// 4. `r` - A size of combination
/// 5. `result` - A ref mut to result container
/// 6. `result_change_fn` - A closure that accept parameter `usize`, `usize`, and `&mut R`.
/// It responsible to assign a new value to R. The first usize is a slot of R 
/// to be updated. The second usize is the index to `data`.
/// 7. `result_fn` - A function that make result ready for comsumption.
#[inline(always)]
fn _large_comb_next_core<'a, T, R, V>(
    c : &mut [usize], 
    data : & [T],
    iterated : &mut Option<()>,
    r : usize,
    result : &mut R,
    mut result_change_fn : impl FnMut(usize, usize, &mut R),
    result_fn : impl Fn(&R) -> V
) -> Option<V>
    where T : 'a,
{
    /// Move cursor and update result
    #[inline(always)]
    fn move_cur_res<'a, T, R>(
        c : &mut [usize], 
        domain : &'a [T], 
        result : &mut R, 
        mut next_result_fn : impl FnMut(usize, usize, &mut R)
    ) -> Option<()> {
        let n = c.len();
        let max = domain.len();
        let mut i = c.len() - 1;
    
        if c[i] < max - n + i {
            c[i] += 1;
            next_result_fn(i, c[i], result);
            Some(())
        } else {
            // find where to start reset cursor
            while c[i] >= max - n + i && i > 0 {
                i -= 1;
            }

            if c[0] >= max - n {
                // first slot already on last possible value
                return None;
            }

            c[i] += 1;
            next_result_fn(i, c[i], result);
            i += 1;
            // reset all cursor from `i + 1`
            (i..c.len()).for_each(|i| {
                c[i] = c[i - 1] + 1;
                next_result_fn(i, c[i], result);
            });

            Some(())
        }
    }
    
    /// Init first result.
    /// It'd be call only once to populate the result
    #[inline(always)]
    fn init_once<'a, F, R>(
        c : &mut [usize], 
        r : usize,
        result : &mut R,
        result_change_fn : &mut F
    ) -> Option<()> 
        where for<'r> F : FnMut(usize, usize, &mut R),
    {
        (0..r).for_each(|i| {
            result_change_fn(i, i, result);
            c[i] = i;
        });

        return Some(());
    }

    if let None = iterated {
        *iterated = Some(());

        init_once(c, r, result, &mut result_change_fn);

        // handle special case where data.len() == 1
        if data.len() == 1 {
            c[0] = 1; // force cursor to go move or next call will reinit result
        }

        return Some(result_fn(&*result));
    }

    match move_cur_res(c, data, result, result_change_fn) {
        Some(_) => Some(result_fn(&*result)),
        None => None
    }
}

/// Create a combination iterator.
/// The result is lexicographic ordered if input is lexicorgraphic ordered.
/// The returned combination will be a reference into given data.
/// Each combination return from iterator will be a new Vec.
/// It's safe to hold onto a combination or `collect` it.
/// 
/// # Examples
/// Given slice of [1, 2, 3, 4, 5]. It will produce following
/// combinations:
/// [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4], [1, 2, 5],
/// [1, 3, 5], [2, 3, 5], [1, 4, 5], [2, 4, 5], [3, 4, 5]
/// Here's an example of code printing above combination.
/// ```
///    use permutator::LargeCombinationIterator;
///    use std::time::{Instant};
///    let lc = LargeCombinationIterator::new(&[1, 2, 3, 4, 5], 3);
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    for combination in lc {
///        println!("{}:{:?}", counter, combination);
///        counter += 1;
///    }
///
///    println!("Total {} combinations in {:?}", counter, timer.elapsed());
/// ```
/// 
/// # Panic
/// It panic if `r == 0` or `r > data.len()`
pub struct LargeCombinationIterator<'a, T> where T : 'a {
    c : Vec<usize>, // cursor for each combination slot
    data : &'a [T], // data to generate a combination
    i : usize, // slot index being mutate.
    nexted : Option<()>, // If iterated at least once, it'd be Some(()). Otherwise, None.
    len : usize, // total possible number of combination.
    r : usize, // a size of combination.
    result : Vec<&'a T>, // result container
}

impl<'a, T> LargeCombinationIterator<'a, T> {
    pub fn new(data : &[T], r : usize) -> LargeCombinationIterator<T> {
        assert_ne!(r, 0);
        assert!(r <= data.len());
        
        let c = vec![0; r];
        let n = data.len();
        let result = vec![&data[0]; r];

        LargeCombinationIterator {
            c,
            data : data,
            i : 0,
            nexted : None,
            len : divide_factorial(n, multiply_factorial(n - r, r)),
            r : r,
            result : result
        }
    }

    pub fn iter(&mut self) -> &mut Self {
        self
    }
}

impl<'a, T> Iterator for LargeCombinationIterator<'a, T> {
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Vec<&'a T>> {
        let data = &self.data;
        _large_comb_next_core(
            &mut self.c,
            data,
            &mut self.nexted,
            self.r,
            &mut self.result,
            |i, j, r| {
                r[i] = &data[j];
            },
            |r| {
                r.to_owned()
            }
        )
    }
}

impl<'a, T> IteratorReset for LargeCombinationIterator<'a, T> {
    fn reset(&mut self) {
        self.nexted = None;
        self.c.iter_mut().for_each(|c| *c = 0);
        self.i = 0;
    }
}

impl<'a, T> ExactSizeIterator for LargeCombinationIterator<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

/// Create a combination iterator.
/// The result is lexicographic ordered if input is lexicorgraphic ordered.
/// The returned combination will be a reference into given data.
/// Each combination return from iterator is stored into given
/// Rc<RefCell<&mut [&T]>>.
/// 
/// The result will be overwritten on every iteration.
/// To reuse a result, convert a result to owned value.
/// If most result need to be reused, consider using
/// [LargeCombinationIterator](struct.LargeCombinationIterator.html)
/// 
/// # Examples
/// Given slice of [1, 2, 3, 4, 5]. It will produce following
/// combinations:
/// [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4], [1, 2, 5],
/// [1, 3, 5], [2, 3, 5], [1, 4, 5], [2, 4, 5], [3, 4, 5]
/// Here's an example of code printing above combination.
/// ```
///    use permutator::{LargeCombinationCellIter};
///    use std::cell::RefCell;
///    use std::rc::Rc;
///    use std::time::{Instant};
///    let data = &[1, 2, 3, 4, 5];
///    let mut result : &mut[&i32] = &mut [&data[0]; 3];
///    let shared = Rc::new(RefCell::new(result));
///    let mut lc = LargeCombinationCellIter::new(&[1, 2, 3, 4, 5], 3, Rc::clone(&shared));
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    for _ in lc {
///        println!("{}:{:?}", counter, shared);
///        counter += 1;
///    }
///
///    println!("Total {} combinations in {:?}", counter, timer.elapsed());
/// ```
/// 
/// # Panic
/// It panic if `r > data.len()` or `r == 0`
pub struct LargeCombinationCellIter<'a, T> where T : 'a {
    c : Vec<usize>, // cursor for each combination slot
    data : &'a [T], // data to generate a combination
    i : usize, // slot index being mutate.
    nexted : Option<()>, // If iterated at least once, it'd be Some(()). Otherwise, None.
    len : usize, // total possible number of combination.
    r : usize, // a size of combination.

    result : Rc<RefCell<&'a mut [&'a T]>>
}

impl<'a, T> LargeCombinationCellIter<'a, T> {
    pub fn new(data : &'a [T], r : usize, result : Rc<RefCell<&'a mut [&'a T]>>) -> LargeCombinationCellIter<'a, T> {
        assert_ne!(r, 0);
        assert!(r <= data.len());
        
        let c = vec![0; r];
        let n = data.len();

        LargeCombinationCellIter {
            c,
            data : data,
            i : 0,
            nexted : None,
            len : divide_factorial(n, multiply_factorial(n - r, r)),
            r : r,

            result : result
        }
    }

    pub fn iter(&mut self) -> &mut Self {
        self
    }
}

impl<'a, T> Iterator for LargeCombinationCellIter<'a, T> {
    type Item = ();

    fn next(&mut self) -> Option<()> {
        let data = &self.data;
        _large_comb_next_core(
            &mut self.c,
            data,
            &mut self.nexted,
            self.r,
            &mut self.result,
            |i, j, r| {
                r.borrow_mut()[i] = &data[j];
            },
            |_| {
                ()
            }
        )
    }
}

impl<'a, T> IteratorReset for LargeCombinationCellIter<'a, T> {
    fn reset(&mut self) {
        self.nexted = None;
        self.c.iter_mut().for_each(|c| *c = 0);
        self.i = 0;
    }
}

impl<'a, T> ExactSizeIterator for LargeCombinationCellIter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

/// Create an unsafe combination iterator that return result to mutable pointer.
/// The result is lexicographic ordered if input is lexicorgraphic ordered.
/// The returned combination will be a reference into given data.
/// Each combination return from iterator is stored into given
/// *mut [&T].
/// 
/// The result will be overwritten on every iteration.
/// To reuse a result, convert a result to owned value.
/// If most result need to be reused, consider using
/// [LargeCombinationIterator](struct.LargeCombinationIterator.html)
/// 
/// # Safety
/// This object took raw mutable pointer and convert in upon object
/// instantiation via [new function](struct.LargeCombinationRefIter.html#method.new)
/// thus all unsafe Rust conditions will be applied on all method.
/// 
/// # Rationale
/// It uses unsafe to take a mutable pointer to store the result
/// to avoid the cost of using Rc<RefCell<>>. 
/// In uncontroll test environment, this struct perform a complete
/// iteration over 30,045,015 combinations in about 337ms where 
/// [LargeCombinationCellIter](struct.LargeCombinationCellIter.html)
/// took about 460ms.
/// This function is very much alike 
/// [unsafe_combination function](fn.unsafe_combination.html)
/// but took `Iterator` approach.
/// 
/// # Examples
/// Given slice of [1, 2, 3, 4, 5]. It will produce following
/// combinations:
/// [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4], [1, 2, 5],
/// [1, 3, 5], [2, 3, 5], [1, 4, 5], [2, 4, 5], [3, 4, 5]
/// Here's an example of code printing above combination.
/// ```
///    use permutator::{LargeCombinationRefIter};
///    use std::time::{Instant};
///    let data = &[1, 2, 3, 4, 5];
///    let mut result : &mut[&i32] = &mut [&data[0]; 3];
///    unsafe {
///         let mut comb = LargeCombinationRefIter::new(&[1, 2, 3, 4, 5], 3, result as *mut [&i32]);
///         let mut counter = 0;
///         let timer = Instant::now();
///
///         for _ in comb {
///             println!("{}:{:?}", counter, result);
///             counter += 1;
///         }
///
///         println!("Total {} combinations in {:?}", counter, timer.elapsed());
///    }
/// ```
pub struct LargeCombinationRefIter<'a, T> where T : 'a {
    c : Vec<usize>, // cursor for each combination slot
    data : &'a [T], // data to generate a combination
    i : usize, // slot index being mutate.
    nexted : Option<()>, // If iterated at least once, it'd be Some(()). Otherwise, None.
    len : usize, // total possible number of combination.
    r : usize, // a size of combination.

    result : &'a mut [&'a T]
}

impl<'a, T> LargeCombinationRefIter<'a, T> {
    pub unsafe fn new(data : &'a [T], r : usize, result : *mut [&'a T]) -> LargeCombinationRefIter<'a, T> {
        assert_ne!(r, 0);
        assert!(r <= (*data).len());
        
        let c = vec![0; r];
        let n = data.len();

        LargeCombinationRefIter {
            c,
            data : data,
            i : 0,
            nexted : None,
            len : divide_factorial(n, multiply_factorial(n - r, r)),
            r : r,

            result : &mut *result
        }
    }

    /// Total number of combinations this iterate can return.
    /// It will equals to n!/((n-r)!*r!)
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn iter(&mut self) -> &mut Self {
        self
    }
}

impl<'a, T> Iterator for LargeCombinationRefIter<'a, T> {
    type Item = ();

    fn next(&mut self) -> Option<()> {
        let data = &self.data;
        _large_comb_next_core(
            &mut self.c,
            data,
            &mut self.nexted,
            self.r,
            &mut self.result,
            |i, j, r| {
                r[i] = &data[j];
            },
            |_| {
                ()
            }
        )
    }
}

impl<'a, T> IteratorReset for LargeCombinationRefIter<'a, T> {
    fn reset(&mut self) {
        self.nexted = None;
        self.c.iter_mut().for_each(|c| *c = 0);
        self.i = 0;
    }
}

impl<'a, T> ExactSizeIterator for LargeCombinationRefIter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

/// Core logic of `next` function of `HeapPermutation` iterator family.
/// 
/// # Parameters
/// 1. `c` - mutable slice of usize. A cursor that pointed to data for
/// each permutation slot.
/// 2. `i` - the current index pointed to which slot to be permuted.
/// 3. `n` - the number of data/slots to be permuted.
#[inline(always)]
fn _heap_next_core(
    c : &mut[usize], 
    i : &mut usize, 
    n : usize, 
    mut swap_fn : impl FnMut(usize, usize)) 
{
    while *i < n {
        if c[*i] < *i {
            if *i % 2 == 0 {
                // self.data.swap(0, *i);
                swap_fn(0, *i);
            } else {
                swap_fn(c[*i], *i);
            }

            c[*i] += 1;
            *i = 0;
            return
        } else {
            c[*i] = 0;
            *i += 1;
        }
    }
}

/// Heap's permutation in iterator style implementation.
/// 
/// # Examples
/// Iterator style usage example:
/// ```
///    use permutator::HeapPermutationIterator;
///    use std::time::{Instant};
///    let data = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
///    println!("0:{:?}", data);
///    let mut permutator = HeapPermutationIterator::new(data);
///    let timer = Instant::now();
///    let mut counter = 1;
///
///    for permutated in permutator {
///        // println!("{}:{:?}", counter, permutated);
///        counter += 1;
///    }
/// 
///    // or use iterator related functional approach like line below.
///    // permutator.into_iter().for_each(|permutated| {counter += 1;});
///
///    println!("Done {} permutations in {:?}", counter, timer.elapsed());
/// ```
/// # See
/// - [Heap's algorithm in Wikipedia page, October 9, 2018](https://en.wikipedia.org/wiki/Heap%27s_algorithm)
pub struct HeapPermutationIterator<'a, T> where T : 'a {
    c : Box<[usize]>,
    data : &'a mut [T],
    i : usize
}

impl<'a, T> HeapPermutationIterator<'a, T> {
    /// Construct a new permutation iterator.
    /// Note: the provided parameter will get mutated
    /// in placed at first call to next.
    pub fn new(data : &mut [T]) -> HeapPermutationIterator<T> {
        HeapPermutationIterator {
            c : vec![0; data.len()].into_boxed_slice(),
            data : data,
            i : 0
        }
    }

    /// Consume itself immediately return it.
    /// It mimic how `IntoIterator` trait perform except
    /// that this struct itself implement `Iterator` trait.
    pub fn into_iter(self) -> Self {
        self
    }
}

impl<'a, T> Iterator for HeapPermutationIterator<'a, T> where T : Clone {
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let HeapPermutationIterator {ref mut c, ref mut data, ref mut i } = self;
        let n = data.len();
        let mut result : Option<Vec<T>> = None;
        _heap_next_core(c, i, n, 
            #[inline(always)]
            |from, to| {
                data.swap(from, to);
                result = Some(data.to_owned());
            }
        );

        result
    }
}

impl<'a, T> IteratorReset for HeapPermutationIterator<'a, T> {
    /// Reset this permutator so calling next will continue
    /// permutation on current permuted data.
    /// It will not reset permuted data.
    fn reset(&mut self) {
        self.i = 0;
        self.c.iter_mut().for_each(|c| {*c = 0;});
    }
}

impl<'a, T> ExactSizeIterator for HeapPermutationIterator<'a, T> where T : Clone {
    fn len(&self) -> usize {
        factorial(self.data.len())
    }
}

/// Heap's permutation in Rc<RefCell<>> mimic Iterator style.
/// It provides another choice for user that want to share 
/// permutation result but doesn't want to clone it for 
/// each share. It also doesn't create new result on each
/// iteration unlike other object that implement `Iterator` trait.
/// # Rationale
/// Unlike all other struct, HeapPermutationIterator permute value in place.
/// If HeapPermutationIterator struct implement IteratorCell itself will
/// result in the `data` inside struct left unused.
/// This struct introduce the same concept to other struct that 
/// implement `IteratorCell`, to be able to easily share
/// result with as less performance overhead as possible.
/// 
/// The implementation take Rc<RefCell<&mut [T]>> instead of regular
/// slice like other permutation struct.
/// It implements `Iterator` trait with empty associated type because
/// it doesn't return value. It permutes the data in place thus
/// every owner of Rc<RefCell<&mut [T]>> will always has an up-to-date
/// slice.
/// # Examples
/// Iterator style usage example:
/// ```
///    use permutator::HeapPermutationCellIter;
///    use std::cell::RefCell;
///    use std::rc::Rc;
///    use std::time::{Instant};
///    let data : &mut [i32] = &mut [1, 2, 3, 4, 5];
///    let shared = Rc::new(RefCell::new(data));
///    let mut permutator = HeapPermutationCellIter::new(Rc::clone(&shared));
///    println!("0:{:?}", &*shared.borrow());
///    let timer = Instant::now();
///    let mut counter = 1;
///
///    for _ in permutator { // it return empty
///        println!("{}:{:?}", counter, &*shared.borrow());
///        counter += 1;
///    }
/// 
///    // or use iterator related functional approach like line below.
///    // permutator.into_iter().for_each(|_| {
///    //     println!("{}:{:?}", counter, &*data.borrow());
///    //     counter += 1;
///    // });
///
///    println!("Done {} permutations in {:?}", counter, timer.elapsed());
/// ```
/// # See
/// - [HeapPermutationIterator struct](struct.HeapPermutationIterator.html)
pub struct HeapPermutationCellIter<'a, T> where T : 'a {
    c : Vec<usize>,
    data : Rc<RefCell<&'a mut[T]>>,
    i : usize
}

impl<'a, T> HeapPermutationCellIter<'a, T> {
    /// Construct a new permutation iterator.
    /// Note: the provided parameter will get mutated
    /// in placed at first call to next.
    pub fn new(data : Rc<RefCell<&'a mut[T]>>) -> HeapPermutationCellIter<'a, T> {
        HeapPermutationCellIter {
            c : vec![0; data.borrow().len()],
            data : Rc::clone(&data),
            i : 0
        }
    }
}

impl<'a, T> Iterator for HeapPermutationCellIter<'a, T> where T : 'a {
    type Item= ();

    fn next(&mut self) -> Option<()> {
        let HeapPermutationCellIter {ref mut c, ref mut data, ref mut i } = self;
        let n = data.borrow().len();
        let mut result : Option<()> = None;
        _heap_next_core(c, i, n, 
            #[inline(always)]
            |from, to| {
                data.borrow_mut().swap(from, to);
                result = Some(());
            }
        );

        result
    }
}

impl<'a, T> IteratorReset for HeapPermutationCellIter<'a, T> {
    /// Reset this permutator so calling next will continue
    /// permutation on current permuted data.
    /// It will not reset permuted data.
    fn reset(&mut self) {
        self.i = 0;
        self.c.iter_mut().for_each(|c| {*c = 0;});
    }
}

impl<'a, T> ExactSizeIterator for HeapPermutationCellIter<'a, T> {
    fn len(&self) -> usize {
        factorial(self.data.borrow().len())
    }
}

/// An unsafe Heap's permutation in iterator style implementation.
/// 
/// # Examples
/// - Iterator style usage example:
/// ```
///    use permutator::HeapPermutationRefIter;
///    use std::time::{Instant};
///    let data : &mut[i32] = &mut [1, 2, 3, 4, 5];
///    println!("0:{:?}", data);
///    unsafe {
///         let mut permutator = HeapPermutationRefIter::new(data as *mut[i32]);
///         let timer = Instant::now();
///         let mut counter = 1;
///
///         for permutated in permutator {
///             println!("{}:{:?}", counter, permutated);
///             counter += 1;
///         }
/// 
///         // or use iterator related functional approach like line below.
///         // permutator.into_iter().for_each(|permutated| {counter += 1;});
///
///         println!("Done {} permutations in {:?}", counter, timer.elapsed());
///    }
/// ```
/// In test environment, given a slice of 8 strings. It has about 40 characters each.
/// This implementation is about 70 times (33ms vs 0.47ms) faster than a [HeapPermutation](struct.HeapPermutation.html)
/// iteration. This is because each `next` function doesn't clone/copy the value.  
/// However, this implementation limited the way to use data because each iteration
/// permute the result in place. It require user to manually sync the share operation.
/// # See
/// - [Heap's algorithm in Wikipedia page, October 9, 2018](https://en.wikipedia.org/wiki/Heap%27s_algorithm)
pub struct HeapPermutationRefIter<'a, T> where T : 'a {
    c : Vec<usize>,
    data : &'a mut [T],
    i : usize
}

impl<'a, T> HeapPermutationRefIter<'a, T> {
    /// Construct a new permutation iterator.
    /// Note: the provided parameter will get mutated
    /// in placed at first call to next.
    pub unsafe fn new(data : *mut [T]) -> HeapPermutationRefIter<'a, T> {
        HeapPermutationRefIter {
            c : vec![0; (*data).len()],
            data : &mut *data,
            i : 0
        }
    }

    /// Consume itself immediately return it.
    /// It mimic how `IntoIterator` trait perform except
    /// that this struct itself implement `Iterator` trait.
    pub fn into_iter(self) -> Self {
        self
    }
}

impl<'a, T> Iterator for HeapPermutationRefIter<'a, T> {
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        let HeapPermutationRefIter {ref mut c, ref mut data, ref mut i } = self;
        let n = data.len();
        let mut result : Option<()> = None;
        _heap_next_core(c, i, n, 
            #[inline(always)]
            |from, to| {
                data.swap(from, to);
                result = Some(());
            }
        );

        result
    }
}

impl<'a, T> IteratorReset for HeapPermutationRefIter<'a, T> {
    /// Reset this permutator so calling next will continue
    /// permutation on current permuted data.
    /// It will not reset permuted data.
    fn reset(&mut self) {
        self.i = 0;
        self.c.iter_mut().for_each(|c| {*c = 0;});
    }
}

impl<'a, T> ExactSizeIterator for HeapPermutationRefIter<'a, T> {
    fn len(&self) -> usize {
        factorial(self.data.len())
    }
}

/// k-permutation iterator common code to perform
/// `next` element operation.
/// 
/// # Parameters
/// 1. `combinator` - A combination iterator object
/// 2. `permutator` - An Option holding permutation iterator object
/// 4. `new_permutator_fn` - A closure that create new permutation iterator
#[inline(always)]
fn _k_permutation_next_core<'a, T, U, V, W, X>(
    combinator : T,
    permutator : &'a mut Option<U>, 
    permuted : X,
    new_permutator_fn : impl FnOnce(&'a mut Option<U>, X, V) + 'a
) -> Option<()>
where T : Iterator<Item=V> + 'a,
      U : Iterator<Item=W> + IteratorReset + 'a,
      V : 'a,
      X : 'a
{
    #[inline(always)]
    fn get_next<'a, T, U, V, W, X>(
        combinator : T, 
        permutator : &'a mut Option<U>, 
        permuted : X,
        new_permutator_fn : impl FnOnce(&'a mut Option<U>, X, V)
    ) -> Option<()> 
    where T : Iterator<Item=V> + 'a,
          U : Iterator<Item=W> + IteratorReset + 'a,
          V : 'a,
          X : 'a
    {
        if let Some(ref mut perm) = *permutator {
            // permutator already exist

            if let Some(_) = perm.next() {
                // get next permutation of current permutator
                return Some(());
            } 
        } 

        // permutator is not exist yet.
        if let Ok(_) = next_permutator(combinator, permutator, permuted, new_permutator_fn) {
            // success create new permutator
            Some(())
        } else {
            // no more combination to permute
            return None;
        }
    }

    #[inline(always)]
    fn next_permutator<'a, T, U, V, W, X>(
        mut combinator : T, 
        permutator : &'a mut Option<U>, 
        permuted : X,
        new_permutator_fn : impl FnOnce(&'a mut Option<U>, X, V) 
    ) -> Result<(), ()> 
    where T : Iterator<Item = V> + 'a,
          U : Iterator<Item=W> + IteratorReset + 'a,
          V : 'a,
          X : 'a
    {
        if let Some(v) = combinator.next() {
            new_permutator_fn(&mut *permutator, permuted, v);
            Ok(())
        } else {
            Err(())
        }
    }

    get_next(combinator, permutator, permuted, new_permutator_fn)
}

/// k-Permutation over data of length n where k must be
/// less than n.
/// It'll attempt to permute given data by pick `k` elements
/// out of data. It use Gosper algorithm to pick the elements.
/// It then use Heap's algorithm to permute those `k` elements
/// and return each permutation back to caller.
/// 
/// # Examples
/// - Iterator style permit using 'for-in' style loop along with
/// enable usage of functional paradigm over iterator object.
/// ```
///    use permutator::KPermutationIterator;
///    use std::time::Instant;
///    let data = [1, 2, 3, 4, 5];
///    let permutator = KPermutationIterator::new(&data, 3);
///    let mut counter = 0;
///    // println!("Begin testing KPermutation");
///    let timer = Instant::now();
///
///    for permuted in permutator {
///        // uncomment a line below to print all permutation.
///        // println!("{}:{:?}", counter, permuted);
///        counter += 1;
///    }
/// 
///    // Or simply use functional paradigm of iterator like below
///    // permutator.into_iter().any(|item| {item == [7, 8, 9]});
///
///    println!("Total {} permutations done in {:?}", counter, timer.elapsed());
///    assert_eq!(60, counter);
/// ```
/// 
/// # Notes
/// The additional functionality provided by this struct is that it can be
/// pause or completely stop midway while the [k-permutation](fn.k_permutation.html)
/// need to be run from start to finish only.
/// 
/// # Safety
/// This struct implementation use unsafe code internally.
/// It use unsafe because it uses `Vec<T>` to own a combination
/// for each permutation. Rust cannot derive lifetime of mutable
/// slice created inside next and store it into struct object itself.
/// This is because `next` signature have no lifetime associated 
/// with `self`. To get around this, the implementation convert
/// Vec<T> to `*mut [T]` then perform `&mut *` on it.
/// 
/// # See
/// - [GosperCombination](struct.GoserPermutation.html)
/// - [HeapPermutation](struct.HeapPermutationIterator.html)
pub struct KPermutationIterator<'a, T> where T : 'a {
    permuted : Vec<&'a T>,
    
    len : usize,

    combinator : LargeCombinationIterator<'a, T>,
    permutator : Option<HeapPermutationIterator<'a, &'a T>>
}

impl<'a, T> KPermutationIterator<'a, T> {
    pub fn new(data : &[T], k : usize) -> KPermutationIterator<T> {
        assert_ne!(k, 0);
        assert!(k <= data.len());
        let combinator = LargeCombinationIterator::new(data, k);
        let n = data.len();
        let permuted = vec![&data[0]; k];

        KPermutationIterator {
            permuted : permuted,

            len : divide_factorial(n, n - k),

            combinator : combinator,
            permutator : None
        }
    }

    /// Consume then return self immediately.
    /// It permit functional style operation over iterator 
    /// from borrow object as Rust isn't yet support
    /// `for _ in borrowed_object` directly.
    /// It need to be `for _ in borrowed_object.into_iter()`.
    pub fn into_iter(self) -> Self {
        self
    }
}

impl<'a, T> Iterator for KPermutationIterator<'a, T> {
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Vec<&'a T>> {
        let combinator = &mut self.combinator;
        let permutator = &mut self.permutator;
        let permuted = self.permuted.as_mut_slice() as *mut [&T];
        
        unsafe {
            if let Some(_) = _k_permutation_next_core(
                combinator, 
                permutator,
                &mut *permuted, 
                #[inline(always)]
                |permutator, permuted, comb| {
                    permuted.copy_from_slice(comb.as_slice());
                    *permutator = Some(HeapPermutationIterator::new(permuted));
                }
            ) {
                Some(self.permuted.to_owned())
            } else {
                None
            }
        }
    }
}

impl<'a, T> IteratorReset for KPermutationIterator<'a, T> {
    fn reset(&mut self) {
        self.combinator.reset();
        self.permutator = None;
    }
}

impl<'a, T> ExactSizeIterator for KPermutationIterator<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

/// k-Permutation over data of length "n" where `k` must be
/// less than `n`.
/// It'll attempt to permute given data by pick `k` elements
/// out of `n` data. It use Gosper algorithm to pick the elements.
/// It then use Heap's algorithm to permute those `k` elements
/// and return each permutation back to caller by given
/// Rc<RefCell<&mut [&T]>> parameter to 
/// [new method of KPermutationCellIter](struct.KPermutationCellIter.html#method.new).
/// 
/// # Examples
/// - Iterator style permit using 'for-in' style loop along with
/// enable usage of functional paradigm over iterator object.
/// ```
///    use permutator::{KPermutationCellIter, IteratorReset};
///    use std::cell::RefCell;
///    use std::rc::Rc;
///    use std::time::Instant;
///    let data = [1, 2, 3, 4, 5];
///    let mut result : Vec<&i32> = vec![&data[0]; 3];
///    let shared = Rc::new(RefCell::new(result.as_mut_slice()));
///    let mut permutator = KPermutationCellIter::new(&data, 3, Rc::clone(&shared));
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    permutator.for_each(|_| {
///        println!("{}:{:?}", counter, &*shared.borrow());
///        counter += 1;
///    });
///
///    println!("Total {} permutations done in {:?}", counter, timer.elapsed());
///    assert_eq!(60, counter);
/// ```
///
/// # Notes
/// This struct manual iteration performance is about 110% slower than using 
/// [k-permutation](fn.k_permutation.html) function
/// while the slowest using Iterator style is about 2300% slower.
/// The additional functionality provided by this struct is that it can be
/// pause or completely stop midway while the [k-permutation](fn.k_permutation.html)
/// need to be run from start to finish only.
/// 
/// # Warning
/// This struct implementation use unsafe code.
/// This is because inside the `next` function, it require
/// a share mutable variable on both the Gosper iterator and
/// Heap permutator. It also require to re-assign the
/// permutator on first call to `next` which is impossible in current safe Rust.
/// To do it in safe Rust way, it need to copy the data
/// which will hurt performance.
/// 
/// # See
/// - [HeapPermutation](struct.HeapPermutationIterator.html)
pub struct KPermutationCellIter<'a, T> where T : 'a {
    permuted : Rc<RefCell<&'a mut [&'a T]>>,
    
    len : usize,

    combinator : LargeCombinationIterator<'a, T>,
    permutator : Option<HeapPermutationCellIter<'a, &'a T>>
}

impl<'a, T> KPermutationCellIter<'a, T> {
    pub fn new(data : &'a [T], k : usize, result : Rc<RefCell<&'a mut [&'a T]>>) -> KPermutationCellIter<'a, T> {
        let combinator = LargeCombinationIterator::new(data, k);
        let n = data.len();

        KPermutationCellIter {
            permuted : result,

            len : divide_factorial(n, n - k),

            combinator : combinator,
            permutator : None
        }
    }

    /// Consume then return self immediately.
    /// It permit functional style operation over iterator 
    /// from borrow object as Rust isn't yet support
    /// `for _ in borrowed_object` directly.
    /// It need to be `for _ in borrowed_object.into_iter()`.
    pub fn into_iter(self) -> Self {
        self
    }

    /// Get total number of permutation this KPermutationIterator object
    /// can permute. It'll be equals to number of possible `next`
    /// call.
    pub fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> Iterator for KPermutationCellIter<'a, T> {
    type Item = ();

    fn next(&mut self) -> Option<()> {
        let permutator = &mut self.permutator;
        let permuted = Rc::clone(&self.permuted);

        if let Some(_) = _k_permutation_next_core(
            &mut self.combinator, 
            permutator,
            permuted,
            #[inline(always)]
            |permutator, permuted, comb| {
                permuted.borrow_mut().iter_mut().enumerate().for_each(|(i, p)| *p = comb[i]);
                if let Some(p) = permutator {
                    p.reset();
                } else {
                    *permutator = Some(HeapPermutationCellIter::new(permuted));
                }
            }) {
            return Some(());
        } else {
            return None;
        }
    }
}

impl<'a, T> IteratorReset for KPermutationCellIter<'a, T> {
    fn reset(&mut self) {
        self.combinator.reset();
        self.permutator = None;
    }
}

impl<'a, T> ExactSizeIterator for KPermutationCellIter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

/// k-Permutation over data of length "n" where `k` must be
/// less than `n` and store result into mutable pointer.
/// It'll attempt to permute given data by pick `k` elements
/// out of `n` data. It use Gosper algorithm to pick the elements.
/// It then use Heap's algorithm to permute those `k` elements
/// and return each permutation back to caller by given
/// *mut [&T]>> parameter to 
/// [new method of KPermutationRefIter](struct.KPermutationRefIter.html#method.new).
/// 
/// # Safety
/// This object use raw mutable pointer provided from user and keep using it
/// in each `next` iteration. Therefore, all raw pointer conditions are applied
/// up until this object is dropped.
/// 
/// # Rationale
/// It uses unsafe to take a mutable pointer to store the result
/// to avoid the cost of using Rc<RefCell<>>. 
/// In uncontroll test environment, this struct perform a complete
/// iteration over 8,648,640 permutations in about 66ms where 
/// [KPermutationCellIter](struct.KPermutationCellIter.html)
/// took about 125 ms.
/// This function is very much alike 
/// [unsafe_k_permutation function](fn.unsafe_k_permutation.html)
/// but took `Iterator` approach.
/// 
/// # Examples
/// - Iterator style permit using 'for-in' style loop along with
/// enable usage of functional paradigm over iterator object.
/// ```
///    use permutator::{KPermutationCellIter, IteratorReset};
///    use std::cell::RefCell;
///    use std::rc::Rc;
///    use std::time::Instant;
///    let data = [1, 2, 3, 4, 5];
///    let mut result : Vec<&i32> = vec![&data[0]; 3];
///    let shared = Rc::new(RefCell::new(result.as_mut_slice()));
///    let mut permutator = KPermutationCellIter::new(&data, 3, Rc::clone(&shared));
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    permutator.for_each(|_| {
///        println!("{}:{:?}", counter, &*shared.borrow());
///        counter += 1;
///    });
///
///    println!("Total {} permutations done in {:?}", counter, timer.elapsed());
///    assert_eq!(60, counter);
/// ```
/// 
/// # Notes
/// This struct manual iteration performance is about 110% slower than using 
/// [k-permutation](fn.k_permutation.html) function
/// while the slowest using Iterator style is about 2300% slower.
/// The additional functionality provided by this struct is that it can be
/// pause or completely stop midway while the [k-permutation](fn.k_permutation.html)
/// need to be run from start to finish only.
/// 
/// # See
/// - [HeapPermutation](struct.HeapPermutationIterator.html)
pub struct KPermutationRefIter<'a, T> where T : 'a {
    permuted : *mut [&'a T],
    
    len : usize,

    combinator : LargeCombinationIterator<'a, T>,
    permutator : Option<HeapPermutationIterator<'a, &'a T>>
}

impl<'a, T> KPermutationRefIter<'a, T> {
    pub unsafe fn new(data : &'a [T], k : usize, result : *mut [&'a T]) -> KPermutationRefIter<'a, T> {
        let combinator = LargeCombinationIterator::new(data, k);
        let n = data.len();

        KPermutationRefIter {
            permuted : result,

            len : divide_factorial(n, n - k),

            combinator : combinator,
            permutator : None
        }
    }

    /// Consume then return self immediately.
    /// It permit functional style operation over iterator 
    /// from borrow object as Rust isn't yet support
    /// `for _ in borrowed_object` directly.
    /// It need to be `for _ in borrowed_object.into_iter()`.
    pub fn into_iter(self) -> Self {
        self
    }

    /// Get total number of permutation this KPermutationIterator object
    /// can permute. It'll be equals to number of possible `next`
    /// call.
    pub fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> Iterator for KPermutationRefIter<'a, T> {
    type Item = ();

    fn next(&mut self) -> Option<()> {
        let permutator = &mut self.permutator;
        let permuted = self.permuted as *mut [&T];
        unsafe {
            if let Some(_) = _k_permutation_next_core(
                &mut self.combinator, 
                permutator,
                &mut *permuted,
                #[inline(always)]
                |permutator, permuted, comb| {
                    permuted.iter_mut().enumerate().for_each(|(i, p)| *p = comb[i]);

                    if let Some(p) = permutator {
                        p.reset();
                    } else {
                        *permutator = Some(HeapPermutationIterator::new(&mut *permuted));
                    }
                }) {
                return Some(());
            } else {
                return None;
            }
        }
    }
}

impl<'a, T> IteratorReset for KPermutationRefIter<'a, T> {
    fn reset(&mut self) {
        self.combinator.reset();
        self.permutator = None;
    }
}

impl<'a, T> ExactSizeIterator for KPermutationRefIter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

/// Core logic for XPermutation
/// 
/// # Parameters
/// - `a : Vec<usize>` - A vec that contains an index of data currently put into result.
/// - `k : usize` - An index of result to be mutated.
/// - `l : Vec<usize>` - A vec that contains an index of next data to be put into data.
/// - `n : usize` - Total number of data.
/// - `p : usize` - An index used for queueing next index or backtrack the traversal.
/// - `q : usize` - An index of data to be put into result.
/// - `u : Vec<usize>` - A vec cantains an index of data to be put into result when
/// algorithm need to be backtracked.
/// - `result_fn : FnMut(usize, usize)` - Function that mutate result.
/// - `t : FnMut(usize) -> bool` - Function that will be called to check if the branch
/// need to be traversed. If it return true, the branch will be traversed. If it return
/// false, the current branch will be skip and it'll be backtrack one level.
/// The first usize is an index of result to be mutated.
/// The second usize is an index of data to be put into result.
/// 
/// # Return
/// An empty `Option`. When it's `Some`, it means the new result is updated. When it's
/// `None`,  it means there's no next permutation.
fn _x_permutation_next_core(
    a : &mut [usize], 
    k : &mut usize, 
    l : &mut [usize], 
    n : usize, 
    p : &mut usize, 
    q : &mut usize, 
    u : &mut [usize], 
    mut result_fn : impl FnMut(usize, usize), 
    mut t : impl FnMut(usize) -> bool
) -> Option<()> 
{
    /// Return tuple of (p, q) where
    /// p = 0 and q = l[0]
    #[inline(always)]
    fn enter(l : &[usize]) -> (usize, usize) {
        return (0, l[0])
    }

    while *k != 0 { 
        // "Algo X" X3
        // perm[k - 1] = &d[q - 1];
        result_fn(*k - 1, *q - 1);
        a[*k] = *q;

        if t(*k) { // part of "Algo X" X3
            if *k == n { // part of "Algo X" X3
                loop { // condition of "Algo X" X5
                    // "Algo X" X6
                    *k -= 1;

                    if *k == 0 {
                        break;
                    } else {
                        *p = u[*k];
                        *q = a[*k];
                        l[*p] = *q;

                        // "Algo X" X5
                        *p = *q;
                        *q = l[*p];

                        if *q != 0 {
                            break;
                        }
                    }
                }

                // visit part of "Algo X" X3
                return Some(());
            } else {
                // "Algo X" X4
                u[*k] = *p;
                l[*p] = l[*q];
                *k += 1;

                // "Algo X" X2
                let (new_p, new_q) = enter(l);
                *p = new_p;
                *q = new_q;
            }
        } else {
            // "Algo X" X5
            loop {
                *p = *q;
                *q = l[*p];

                if *q != 0 {
                    break;
                }
                
                // "Algo X" X6
                *k -= 1;

                if *k == 0 {
                    return None;
                } else {
                    *p = u[*k];
                    *q = a[*k];
                    l[*p] = *q;
                }
            }
        }
    }

    None
}

/// A lexicographic ordered permutation based on ["Algoritm X" published by
/// Donald E. Knuth.](http://www.cs.utsa.edu/~wagner/knuth/fasc2b.pdf) page 20.
/// 
/// If order is not important, consider using [heap permutation](struct.HeapPermutationIterator.html)
/// struct instead. This struct is a bit slower (about 10%) than [heap 
/// permutation](struct.HeapPermutationIterator.html) in uncontroll test environment.
/// 
/// The algorithm work by simulate tree traversal where some branch can be 
/// skip altogether. This is archive by provided `t` function that take 
/// slice of partial result as parameter. If the partial result needed to be skip,
/// return false. Otherwise, return true and the algorithm will call this function
/// again when the branch is descended deeper. For example: First call to `t` may
/// contain [1]. If `t` return true, it will be called again with [1, 2]. If it
/// return true, and there's leaf node, cb will be called with [1, 2]. On the other hand,
/// if `t` is called with [1, 3] and it return false, it won't call the callback.
/// If `t` is called with [4] and it return false, it won't try to traverse deeper even
/// if there're [4, 5], or [4, 6]. It will skip altogether and call `t` with [7].
/// The process goes on until every branch is traversed.
/// 
/// # Example
/// Get all lexicalgraphic ordered permutation
/// ```Rust
/// use permutator::XPermutationIterator;
/// 
/// let data = vec![1, 2, 3, 4];
/// let mut counter = 0;
///
/// XPermutationIterator::new(&data, |_| true).for_each(|p| {
///     println!("{:?}", p);
///     counter += 1;
/// });
///
/// assert_eq!(factorial(data.len()), counter);
/// ```
/// Skip all permutation that has `1` in first element. 
/// ```Rust
/// use permutator::XPermutationIterator;
/// 
/// let data : Vec<u8> = vec![1, 2, 3, 4];
/// let mut counter = 0;
///
/// XPermutationIterator::new(&data, |f| {
///     *f[0] != 1u8 // filter all permutation that start with 1
/// }).for_each(|p| {
///     println!("{:?}", p);
///     counter += 1;
/// });
///
/// assert_eq!(factorial(data.len()) - factorial(data.len() - 1), counter);
/// ```
/// Multi-threads permutation example
/// ```Rust
/// use permutator::XpermutationIterator;
/// use std::time::{Instant};
/// let data : Vec<usize> = (0..4).map(|num| num).collect();
/// let threads = 2;
/// let chunk = data.len() / threads;
/// let (tx, rx) = mpsc::channel();
///
/// for i in 0..threads {
///     let start = chunk * i;
///     let end = match i {
///         j if j == threads - 1 => data.len(), // last thread handle remaining work
///         _ => chunk * (i + 1)
///     };     
///
///     let l_dat = data.to_owned(); // copy data for each thread
///     let end_sig = tx.clone();
///
///     thread::spawn(move || {
///         let timer = Instant::now();
///
///         let perm = XPermutationIterator::new(
///             &l_dat, 
///             |v| *v[0] >= start && *v[0] < end // skip branch that is outside the start/end
///         );
///
///         let mut counter = 0u64;
///
///         for p in perm {
///             // each permutation is stored in p
///             counter += 1;
///         }
///
///         end_sig.send(i).unwrap();
///     });
/// }
///
/// let main = thread::spawn(move || { // main thread
///     let mut counter = 0;
///
///     while counter < threads {
///         let i = rx.recv().unwrap();
///         // do something 
///         counter += 1;
///     }
/// });
///
/// main.join().unwrap();
/// ```
pub struct XPermutationIterator<'a, F, T> 
    where F : FnMut(&[&T]) -> bool, 
          T : 'a 
{
    a : Vec<usize>,
    data : &'a [T],
    k : usize, 
    l : Vec<usize>, 
    len : usize,
    n : usize, 
    p : usize, 
    q : usize,
    result : Vec<&'a T>,
    t: F,
    u : Vec<usize>, 
}

impl<'a, F, T> XPermutationIterator<'a, F, T>
    where F : FnMut(&[&T]) -> bool,
          T : 'a
{
    /// Construct new XPermutationIterator object.
    /// 
    /// # Parameters
    /// - `data : &[T]` - A data used for generate permutation.
    /// - `t : FnMut(&[&T])` - A function that if return true, will
    /// make algorithm continue traversing the tree. Otherwise,
    /// the entire branch will be skip.
    pub fn new(data : &'a [T], t : F) -> XPermutationIterator<F, T> {
        let n = data.len();
        let mut l : Vec<usize> = (0..n).map(|k| k + 1).collect();
        
        // l[n] = 0
        l.push(0);

        // "Algo X" X1 and X2
        XPermutationIterator {
            a : (0..=n).map(|v| v).collect(),
            data : data,
            k : 1,
            l : l,
            len : factorial(n),
            n : n,
            p : 0,
            q : 1,
            result : vec![&data[0]; n],
            t : t,
            u : vec![0; n + 1]
        }
    }
}

impl<'a, F, T> Iterator for XPermutationIterator<'a, F, T> 
    where F : FnMut(&[&T]) -> bool, 
          T : 'a
{
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Self::Item> {
        let data = self.data;
        let result = self.result.as_mut_slice();
        let result_ptr = &*result as *const [&T];
        let t = &mut self.t;
        if let Some(_) = _x_permutation_next_core(
            &mut self.a, 
            &mut self.k, 
            &mut self.l, 
            self.n, 
            &mut self.p, 
            &mut self.q, 
            &mut self.u, 
            |k, q| {result[k] = &data[q]},
            |k| {
                unsafe {
                    t(&(*result_ptr)[0..k])
                }
            }) {
            Some(result.to_owned())
        } else {
            None
        }
    }
}

impl<'a, F, T> IteratorReset for XPermutationIterator<'a, F, T>
    where F : FnMut(&[&T]) -> bool, 
          T : 'a
{
    fn reset(&mut self) {
        let n = self.data.len();
        let mut l : Vec<usize> = (0..n).map(|k| k + 1).collect();
        
        // l[n] = 0
        l.push(0);

        self.a = (0..=n).map(|v| v).collect();
        self.k = 1;
        self.l = l;
        self.p = 0;
        self.q = 1;
        self.u = vec![0; n + 1];
    }
}

impl<'a, F, T> ExactSizeIterator for XPermutationIterator<'a, F, T>
    where F : FnMut(&[&T]) -> bool, 
          T : 'a
{
    fn len(&self) -> usize {
        self.len
    }
}

/// A lexicographic ordered permutation based on ["Algoritm X" published by
/// Donald E. Knuth.](http://www.cs.utsa.edu/~wagner/knuth/fasc2b.pdf) page 20.
/// 
/// If order is not important, consider using [heap permutation](struct.HeapPermutationCellIter.html)
/// struct instead. This struct is a bit slower (about 10%) than [heap 
/// permutation](struct.HeapPermutationCellIter.html) in uncontroll test environment.
/// 
/// The algorithm work by simulate tree traversal where some branch can be 
/// skip altogether. This is archive by provided `t` function that take 
/// slice of partial result as parameter. If the partial result needed to be skip,
/// return false. Otherwise, return true and the algorithm will call this function
/// again when the branch is descended deeper. For example: First call to `t` may
/// contain [1]. If `t` return true, it will be called again with [1, 2]. If it
/// return true, and there's leaf node, cb will be called with [1, 2]. On the other hand,
/// if `t` is called with [1, 3] and it return false, it won't call the callback.
/// If `t` is called with [4] and it return false, it won't try to traverse deeper even
/// if there're [4, 5], or [4, 6]. It will skip altogether and call `t` with [7].
/// The process goes on until every branch is traversed.
pub struct XPermutationCellIter<'a, F, T> 
    where F : FnMut(&[&T]) -> bool, 
          T : 'a 
{
    a : Vec<usize>,
    data : &'a [T],
    k : usize, 
    l : Vec<usize>, 
    len : usize,
    n : usize, 
    p : usize, 
    q : usize,
    result : Rc<RefCell<&'a mut [&'a T]>>,
    t: F,
    u : Vec<usize>, 
}

impl<'a, F, T> XPermutationCellIter<'a, F, T>
    where F : FnMut(&[&T]) -> bool,
          T : 'a
{
    /// Construct new XPermutationIterator object.
    /// 
    /// # Parameters
    /// - `data : &[T]` - A data used for generate permutation.
    /// - `result : Rc<RefCell<&mut [&T]>>` - A result container.
    /// It'll be overwritten on each call to `next`
    /// - `t : FnMut(&[&T])` - A function that if return true, will
    /// make algorithm continue traversing the tree. Otherwise,
    /// the entire branch will be skip.
    pub fn new(data : &'a [T], result : Rc<RefCell<&'a mut [&'a T]>>, t : F) -> XPermutationCellIter<'a, F, T> {
        let n = data.len();
        let mut l : Vec<usize> = (0..n).map(|k| k + 1).collect();
        
        // l[n] = 0
        l.push(0);

        // "Algo X" X1 and X2
        XPermutationCellIter {
            a : (0..=n).map(|v| v).collect(),
            data : data,
            k : 1,
            l : l,
            len : factorial(n),
            n : n,
            p : 0,
            q : 1,
            result : result,
            t : t,
            u : vec![0; n + 1]
        }
    }
}

impl<'a, F, T> Iterator for XPermutationCellIter<'a, F, T> 
    where F : FnMut(&[&T]) -> bool, 
          T : 'a
{
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        let data = self.data;
        let mut result = self.result.borrow_mut();
        let result_ptr = (&**result) as *const [&T];
        let t = &mut self.t;
        if let Some(_) = _x_permutation_next_core(
            &mut self.a, 
            &mut self.k, 
            &mut self.l, 
            self.n, 
            &mut self.p, 
            &mut self.q, 
            &mut self.u, 
            |k, q| {result[k] = &data[q]},
            |k| {
                unsafe {
                    t(&(*result_ptr)[0..k])
                }
            }) {
            Some(())
        } else {
            None
        }
    }
}

impl<'a, F, T> IteratorReset for XPermutationCellIter<'a, F, T>
    where F : FnMut(&[&T]) -> bool, 
          T : 'a
{
    fn reset(&mut self) {
        let n = self.data.len();
        let mut l : Vec<usize> = (0..n).map(|k| k + 1).collect();
        
        // l[n] = 0
        l.push(0);

        self.a = (0..=n).map(|v| v).collect();
        self.k = 1;
        self.l = l;
        self.p = 0;
        self.q = 1;
        self.u = vec![0; n + 1];
    }
}

impl<'a, F, T> ExactSizeIterator for XPermutationCellIter<'a, F, T>
    where F : FnMut(&[&T]) -> bool, 
          T : 'a
{
    fn len(&self) -> usize {
        self.len
    }
}

/// A lexicographic ordered permutation based on ["Algoritm X" published by
/// Donald E. Knuth.](http://www.cs.utsa.edu/~wagner/knuth/fasc2b.pdf) page 20.
/// 
/// If order is not important, consider using [heap permutation](struct.HeapPermutationRefIter.html)
/// struct instead. This struct is a bit slower (about 10%) than [heap 
/// permutation](struct.HeapPermutationRefIter.html) in uncontroll test environment.
/// 
/// The algorithm work by simulate tree traversal where some branch can be 
/// skip altogether. This is archive by provided `t` function that take 
/// slice of partial result as parameter. If the partial result needed to be skip,
/// return false. Otherwise, return true and the algorithm will call this function
/// again when the branch is descended deeper. For example: First call to `t` may
/// contain [1]. If `t` return true, it will be called again with [1, 2]. If it
/// return true, and there's leaf node, cb will be called with [1, 2]. On the other hand,
/// if `t` is called with [1, 3] and it return false, it won't call the callback.
/// If `t` is called with [4] and it return false, it won't try to traverse deeper even
/// if there're [4, 5], or [4, 6]. It will skip altogether and call `t` with [7].
/// The process goes on until every branch is traversed.
pub struct XPermutationRefIter<'a, F, T> 
    where F : FnMut(&[&T]) -> bool, 
          T : 'a 
{
    a : Vec<usize>,
    data : &'a [T],
    k : usize, 
    l : Vec<usize>, 
    len : usize,
    n : usize, 
    p : usize, 
    q : usize,
    result : &'a mut [&'a T],
    t: F,
    u : Vec<usize>, 
}

impl<'a, F, T> XPermutationRefIter<'a, F, T>
    where F : FnMut(&[&T]) -> bool,
          T : 'a
{
    /// Construct new XPermutationIterator object.
    /// 
    /// # Parameters
    /// - `data : &[T]` - A data used for generate permutation.
    /// - `result : Rc<RefCell<&mut [&T]>>` - A result container.
    /// It'll be overwritten on each call to `next`
    /// - `t : FnMut(&[&T])` - A function that if return true, will
    /// make algorithm continue traversing the tree. Otherwise,
    /// the entire branch will be skip.
    pub unsafe fn new(data : &'a [T], result : *mut [&'a T], t : F) -> XPermutationRefIter<'a, F, T> {
        let n = data.len();
        let mut l : Vec<usize> = (0..n).map(|k| k + 1).collect();
        
        // l[n] = 0
        l.push(0);

        // "Algo X" X1 and X2
        XPermutationRefIter {
            a : (0..=n).map(|v| v).collect(),
            data : data,
            k : 1,
            l : l,
            len : factorial(n),
            n : n,
            p : 0,
            q : 1,
            result : &mut *result,
            t : t,
            u : vec![0; n + 1]
        }
    }
}

impl<'a, F, T> Iterator for XPermutationRefIter<'a, F, T> 
    where F : FnMut(&[&T]) -> bool, 
          T : 'a
{
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        let data = self.data;
        let result = &mut *self.result;
        let result_ptr = (&*result) as *const [&T];
        let t = &mut self.t;
        if let Some(_) = _x_permutation_next_core(
            &mut self.a, 
            &mut self.k, 
            &mut self.l, 
            self.n, 
            &mut self.p, 
            &mut self.q, 
            &mut self.u, 
            |k, q| {result[k] = &data[q]},
            |k| {
                unsafe {
                    t(&(*result_ptr)[0..k])
                }
            }) {
            Some(())
        } else {
            None
        }
    }
}

impl<'a, F, T> IteratorReset for XPermutationRefIter<'a, F, T>
    where F : FnMut(&[&T]) -> bool, 
          T : 'a
{
    fn reset(&mut self) {
        let n = self.data.len();
        let mut l : Vec<usize> = (0..n).map(|k| k + 1).collect();
        
        // l[n] = 0
        l.push(0);

        self.a = (0..=n).map(|v| v).collect();
        self.k = 1;
        self.l = l;
        self.p = 0;
        self.q = 1;
        self.u = vec![0; n + 1];
    }
}

impl<'a, F, T> ExactSizeIterator for XPermutationRefIter<'a, F, T>
    where F : FnMut(&[&T]) -> bool, 
          T : 'a
{
    fn len(&self) -> usize {
        self.len
    }
}

/// Generate a cartesian product on itself in an iterator style.
/// The struct implement `Iterator` trait so it can be used in `Iterator` 
/// style. The struct provide [into_iter()](#method.into_iter()) function 
/// that return itself.
/// 
/// # Example
/// ```
///    use permutator::SelfCartesianProductIterator;
///    use std::time::Instant;
///    let data : &[usize] = &[1, 2, 3];
///    let n = 3;
///    let cart = SelfCartesianProductIterator::new(&data, n);
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    for p in cart {
///        // println!("{:?}", p);
///        counter += 1;
///    }
/// 
///    // or functional style like the line below
///    // cart.into_iter().for_each(|p| {/* do something iterative style */});
///
///    assert_eq!(data.len().pow(n as u32), counter);
///    println!("Total {} products done in {:?}", counter, timer.elapsed());
/// ```
pub struct SelfCartesianProductIterator<'a, T> where T : 'a {
    c : Vec<usize>,
    domain : &'a [T],
    exhausted : bool,
    i : usize,
    n : usize,

    result : Vec<&'a T>
}

impl<'a, T> SelfCartesianProductIterator<'a, T> where T : 'a {
    /// Create a new Cartesian product iterator that create a product on
    /// itself `n` times.
    /// # Parameters
    /// - `domain` A slice of domains to create a cartesian product between
    /// each domain inside it.
    /// - `n` the size of product. For example `n = 3` means create
    /// a cartesian product over `domain` paremeter 3 times.
    /// This is equals to create a `domains` contains
    /// cloned `domain` 3 time.
    /// # Return
    /// An object that can be iterate over in iterator style.
    pub fn new(domain : &'a[T], n : usize) -> SelfCartesianProductIterator<'a, T> {

        SelfCartesianProductIterator {
            c : vec![0; domain.len()],
            domain : domain,
            exhausted : false,
            i : 0,
            n : n,

            result : vec![&domain[0]; n]
        }
    }

    /// Consume itself and return without modify it.
    /// Typical usecase is `for p in ref_to_this.into_iter() {}`
    /// or `ref_to_this.into_iter().for_each(|p| {/* Do something with product */});`
    pub fn into_iter(self) -> Self {
        self
    }
}

impl<'a, T> Iterator for SelfCartesianProductIterator<'a, T> {
    type Item = Vec<&'a T>;

    /// Each iteration return a new Vec contains borrowed element inside
    /// an Option. The result can be collected by using `collect` method
    /// from `Iterator` trait.
    /// 
    /// Return None when exhausted.
    fn next(&mut self) -> Option<Vec<&'a T>> {
        let result = &mut self.result;
        let domain = self.domain;
        _cartesian_next_core(
            &mut self.i, 
            &mut self.c, 
            &mut self.exhausted,
            self.n,
            #[inline(always)]
            |_| {
                domain.len()
            },
            #[inline(always)]
            |i, j| {
                result[i] = &domain[j];
            }
        );

        if self.exhausted {
            None
        } else {
            self.i -= 1; // rewind `i` back to last domain
            Some(result.to_owned())
        }
    }
}

impl<'a, T> IteratorReset for SelfCartesianProductIterator<'a, T> {
    fn reset(&mut self) {
        self.c = vec![0; self.n];
        self.exhausted = false;
        self.i = 0;
    }
}

impl<'a, T> ExactSizeIterator for SelfCartesianProductIterator<'a, T> {
    fn len(&self) -> usize {
        self.n
    }
}

/// Generate a cartesian product on itself in an iterator style.
/// The struct implement `Iterator` trait so it can be used in `Iterator` 
/// style. The struct provide [into_iter()](#method.into_iter()) function 
/// that return itself.
/// 
/// # Example
/// ```
///    use permutator::SelfCartesianProductCellIter;
///    use std::cell::RefCell;
///    use std::rc::Rc;
///    use std::time::Instant;
///    let data : &[usize] = &[1, 2, 3];
///    let n = 3;
///    let result : &mut[&usize] = &mut vec![&data[0]; n];
///    let shared = Rc::new(RefCell::new(result));
///    let cart = SelfCartesianProductCellIter::new(&data, n, Rc::clone(&shared));
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    for _ in cart {
///        // println!("{:?}", &*shared.borrow());
///        counter += 1;
///    }
/// 
///    // or functional style like the line below
///    // cart.into_iter().for_each(|_| {/* do something iterative style */});
///
///    assert_eq!(data.len().pow(n as u32), counter);
///    println!("Total {} products done in {:?}", counter, timer.elapsed());
/// ```
pub struct SelfCartesianProductCellIter<'a, T> where T : 'a {
    c : Vec<usize>,
    domain : &'a [T],
    exhausted : bool,
    i : usize,
    n : usize,

    result : Rc<RefCell<&'a mut [&'a T]>>
}

impl<'a, T> SelfCartesianProductCellIter<'a, T> where T : 'a {
    /// Create a new Cartesian product iterator that create a product on
    /// itself `n` times.
    /// # Parameters
    /// - `domain` A slice of domains to create a cartesian product between
    /// each domain inside it.
    /// This is equals to create a `domains` contains
    /// cloned `domain` 3 time.
    /// - `n` the size of product. For example `n = 3` means create
    /// a cartesian product over `domain` paremeter 3 times.
    /// - `result` an Rc<RefCell<&mut[&T]>> to store each product
    /// # Return
    /// An object that can be iterate over in iterator style.
    pub fn new(domain : &'a[T], n : usize, result : Rc<RefCell<&'a mut [&'a T]>>) -> SelfCartesianProductCellIter<'a, T> {

        SelfCartesianProductCellIter {
            c : vec![0; domain.len()],
            domain : domain,
            exhausted : false,
            i : 0,
            n : n,

            result : Rc::clone(&result)
        }
    }

    /// Consume itself and return without modify it.
    /// Typical usecase is `for p in ref_to_this.into_iter() {}`
    /// or `ref_to_this.into_iter().for_each(|p| {/* Do something with product */});`
    pub fn into_iter(self) -> Self {
        self
    }
}

impl<'a, T> Iterator for SelfCartesianProductCellIter<'a, T> {
    type Item = ();

    /// Each iteration return a new Vec contains borrowed element inside
    /// an Option. The result can be collected by using `collect` method
    /// from `Iterator` trait.
    /// 
    /// Return None when exhausted.
    fn next(&mut self) -> Option<()> {
        let mut result = self.result.borrow_mut();
        let domain = self.domain;
        _cartesian_next_core(
            &mut self.i, 
            &mut self.c, 
            &mut self.exhausted,
            self.n,
            #[inline(always)]
            |_| {
                domain.len()
            },
            #[inline(always)]
            |i, j| {
                result[i] = &domain[j];
            }
        );

        if self.exhausted {
            None
        } else {
            self.i -= 1; // rewind `i` back to last domain
            Some(())
        }
    }
}

impl<'a, T> IteratorReset for SelfCartesianProductCellIter<'a, T> {
    fn reset(&mut self) {
        self.c = vec![0; self.n];
        self.exhausted = false;
        self.i = 0;
    }
}

impl<'a, T> ExactSizeIterator for SelfCartesianProductCellIter<'a, T> {
    fn len(&self) -> usize {
        self.n
    }
}

/// Generate a cartesian product on itself in an iterator style.
/// The struct implement `Iterator` trait so it can be used in `Iterator` 
/// style. The struct provide [into_iter()](#method.into_iter()) function 
/// that return itself.
/// 
/// # Example
/// ```
///    use permutator::SelfCartesianProductRefIter;
///    use std::time::Instant;
///    let data : &[usize] = &[1, 2, 3];
///    let n = 3;
///    let result : &mut[&usize] = &mut vec![&data[0]; n];
///    let shared = result as *mut[&usize];
///    
///    unsafe {
///         let cart = SelfCartesianProductRefIter::new(&data, n, result);
///         let mut counter = 0;
///         let timer = Instant::now();
///
///         for _ in cart {
///             // println!("{:?}", &*shared);
///             counter += 1;
///         }
/// 
///         // or functional style like the line below
///         // cart.into_iter().for_each(|_| {/* do something iterative style */});
///
///         assert_eq!(data.len().pow(n as u32), counter);
///         println!("Total {} products done in {:?}", counter, timer.elapsed());
///    }
/// ```
pub struct SelfCartesianProductRefIter<'a, T> where T : 'a {
    c : Vec<usize>,
    domain : &'a [T],
    exhausted : bool,
    i : usize,
    n : usize,

    result : &'a mut [&'a T]
}

impl<'a, T> SelfCartesianProductRefIter<'a, T> where T : 'a {
    /// Create a new Cartesian product iterator that create a product on
    /// itself `n` times.
    /// # Parameters
    /// - `domain` A slice of domains to create a cartesian product between
    /// each domain inside it.
    /// This is equals to create a `domains` contains
    /// cloned `domain` 3 time.
    /// - `n` the size of product. For example `n = 3` means create
    /// a cartesian product over `domain` paremeter 3 times.
    /// - `result` *mut[&T] to store each product
    /// # Return
    /// An object that can be iterate over in iterator style.
    pub unsafe fn new(domain : &'a[T], n : usize, result : * mut [&'a T]) -> SelfCartesianProductRefIter<'a, T> {

        SelfCartesianProductRefIter {
            c : vec![0; domain.len()],
            domain : domain,
            exhausted : false,
            i : 0,
            n : n,

            result : &mut *result
        }
    }

    /// Consume itself and return without modify it.
    /// Typical usecase is `for p in ref_to_this.into_iter() {}`
    /// or `ref_to_this.into_iter().for_each(|p| {/* Do something with product */});`
    pub fn into_iter(self) -> Self {
        self
    }
}

impl<'a, T> Iterator for SelfCartesianProductRefIter<'a, T> {
    type Item = ();

    /// Each iteration return a new Vec contains borrowed element inside
    /// an Option. The result can be collected by using `collect` method
    /// from `Iterator` trait.
    /// 
    /// Return None when exhausted.
    fn next(&mut self) -> Option<()> {
        let result = &mut self.result;
        let domain = self.domain;
        _cartesian_next_core(
            &mut self.i, 
            &mut self.c, 
            &mut self.exhausted,
            self.n,
            #[inline(always)]
            |_| {
                domain.len()
            },
            #[inline(always)]
            |i, j| {
                result[i] = &domain[j];
            }
        );

        if self.exhausted {
            None
        } else {
            self.i -= 1; // rewind `i` back to last domain
            Some(())
        }
    }
}

impl<'a, T> IteratorReset for SelfCartesianProductRefIter<'a, T> {
    fn reset(&mut self) {
        self.c = vec![0; self.n];
        self.exhausted = false;
        self.i = 0;
    }
}

impl<'a, T> ExactSizeIterator for SelfCartesianProductRefIter<'a, T> {
    fn len(&self) -> usize {
        self.n
    }
}

/// Create a cartesian product out of `T`.
/// For example,
/// - `T` can be a slice of slices so the product can
/// be created between all the slices.
/// - `T` can be a pair of slice to slices and Rc<RefCell<>> contains
/// a mutable product from slices.
/// 
/// # Examples
/// - Create a cartesian product and return it as new owned value
/// ```
///    use std::time::Instant;
///    use permutator::CartesianProduct;
///    
///    let mut counter = 0;
///    let timer = Instant::now();
///    let data : &[&[u8]]= &[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]];
///
///    data.cart_prod().for_each(|p| {
///        counter += 1;
///    });
///
///    assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
///    println!("Total {} products done in {:?}", counter, timer.elapsed());
/// ```   
/// - Create a cartesian product and return result inside
/// Rc<RefCell<>>
/// ```
///    use std::cell::RefCell;
///    use std::rc::Rc;
///    use std::time::Instant;
///    use permutator::CartesianProduct;
///    
///    let mut counter = 0;
///    let timer = Instant::now();
///    let data : &[&[u8]]= &[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]];
///    let mut result = vec![&data[0][0]; data.len()];
///    let shared = Rc::new(RefCell::new(result.as_mut_slice()));
///
///    (data, Rc::clone(&shared)).cart_prod().for_each(|_| {
///        counter += 1;
///    });
///
///    assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
///    println!("Total {} products done in {:?}", counter, timer.elapsed());
/// ``` 
pub trait CartesianProduct<'a> {
    type Producer : Iterator;

    /// Create a cartesian product producer which
    /// can be used to iterate over each product.
    fn cart_prod(&'a self) -> Self::Producer;
}

impl<'a, T> CartesianProduct<'a> for [&'a [T]]
    where T : 'a {
    
    type Producer = CartesianProductIterator<'a, T>;

    fn cart_prod(&'a self) -> Self::Producer {
        CartesianProductIterator::new(self)
    }
}

impl<'a, T> CartesianProduct<'a> for Vec<&'a [T]>
    where T : 'a {
    
    type Producer = CartesianProductIterator<'a, T>;

    fn cart_prod(&'a self) -> Self::Producer {
        CartesianProductIterator::new(self)
    }
}

/// A type that represent a cartesian product of the slice
/// over slices and return result into Rc<RefCell<&mut [&T]>> 
/// by using [CartesianProductCellIter](trait.CartesianProductCellIter.html)
/// 
/// # Format
/// 1. A mutable slice of slices.
/// It's a domains to of a cartesian product operation.
/// 2. An Rc<RefCell<&mut[&T]>.
/// It's a result container. 
pub type CartesianProductIntoCellParams<'a, T> = (&'a [&'a [T]], Rc<RefCell<&'a mut[&'a T]>>);

impl<'a, 'b: 'a, T> CartesianProduct<'a> for CartesianProductIntoCellParams<'b, T> 
    where T : 'b {
    
    type Producer = CartesianProductCellIter<'b, T>;

    fn cart_prod(&'a self) -> Self::Producer {
        CartesianProductCellIter::new(self.0, Rc::clone(&self.1))
    }
}

/// A type that used exclusively for [trait CartesianProduct](trait.CartesianProduct.html).
/// It return [CartesianProductRefIter](struct.CartesianProductRefIter.html).
/// 
/// It's a tuple where first element is a slice contains slices represents a domains
/// of Cartesian product function. The second element is a mutable pointer to a slice which
/// will be used to store each product.
/// 
/// # Format
/// 1. A mutable slice of slices.
/// It's a domains to of a cartesian product operation.
/// 2. A pointer to mutable slice of borrowed value.
/// It's a result container. 
pub type CartesianProductIntoRefParams<'a, T> = (&'a [&'a [T]], *mut [&'a T]);

/// An implementation for convenient use of [CartesianProductRefIter](struct.CartesianProductRefIter.html)
/// # Warning
/// It hid unsafe object instantiation of [CartesianProductRefIter](struct.CartesianProductRefIter.html#method.new)
/// from user but all unsafe conditions are still applied as long as
/// the the life of object itself.
/// 
impl<'a, 'b: 'a, T> CartesianProduct<'a> for CartesianProductIntoRefParams<'b, T> 
    where T : 'b {
    
    type Producer = CartesianProductRefIter<'b, T>;

    fn cart_prod(&'a self) -> Self::Producer {
        unsafe {
            CartesianProductRefIter::new(self.0, self.1)
        }
    }
}

/// A type that used exclusively for [trait CartesianProduct](trait.CartesianProduct.html).
/// It return [SelfCartesianProductIterator](struct.SelfCartesianProductIterator.html).
/// 
/// # Format
/// 1. A slice of T.
/// 2. How many time to create a product on slice
pub type SelfCartesianProduct<'a, T> = (&'a [T], usize);

impl<'a, 'b : 'a, T> CartesianProduct<'a> for SelfCartesianProduct<'b, T>
    where T : 'b {
    type Producer = SelfCartesianProductIterator<'b, T>;

    fn cart_prod(&'a self) -> Self::Producer {
        SelfCartesianProductIterator::new(self.0, self.1)
    }
}

/// A type that used exclusively for [trait CartesianProduct](trait.CartesianProduct.html).
/// It return [SelfCartesianProductCellIter](struct.SelfCartesianProductCellIter.html).
/// 
/// # Format
/// 1. A slice of T.
/// 2. How many time to create a product on slice
/// 3. An Rc<RefCell<&mut [T]>> to store each product on each iteration.
pub type SelfCartesianProductIntoCellParams<'a, T> = (&'a [T], usize, Rc<RefCell<&'a mut [&'a T]>>);

impl<'a, 'b : 'a, T> CartesianProduct<'a> for SelfCartesianProductIntoCellParams<'b, T>
    where T : 'b {
    type Producer = SelfCartesianProductCellIter<'b, T>;

    fn cart_prod(&'a self) -> Self::Producer {
        SelfCartesianProductCellIter::new(self.0, self.1, Rc::clone(&self.2))
    }
}

/// A type that used exclusively for [trait CartesianProduct](trait.CartesianProduct.html).
/// It return [SelfCartesianProductRefIter](struct.SelfCartesianProductRefIter.html).
/// 
/// # Format
/// 1. A slice of T.
/// 2. How many time to create a product on slice
/// 3. A mutable pointer to a slice of ref T
pub type SelfCartesianProductIntoRefParams<'a, T> = (&'a [T], usize, *mut [&'a T]);

/// An implementation for convenient use of [SelfCartesianProductRefIter](struct.SelfCartesianProductRefIter.html)
/// # Warning
/// It hid unsafe object instantiation of [SelfCartesianProductRefIter](struct.SelfCartesianProductRefIter.html#method.new)
/// from user but all unsafe conditions are still applied as long as
/// the life of object itself.
impl<'a, 'b : 'a, T> CartesianProduct<'a> for SelfCartesianProductIntoRefParams<'b, T>
    where T : 'b {
    type Producer = SelfCartesianProductRefIter<'b, T>;

    fn cart_prod(&'a self) -> Self::Producer {
        unsafe {
            SelfCartesianProductRefIter::new(self.0, self.1, self.2)
        }
    }
}

/// Create a combination out of `T`
/// Normally, it take a `[T]` or `Vec<T>` to create a combination.
/// 
/// # Example
/// ```
/// use permutator::Combination;
/// let data = [1, 2, 3, 4, 5];
/// data.combination(3).for_each(|c| {
///     // called multiple times.
///     // Each call have [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4]
///     // [1, 2, 5], [1, 3, 5], [2, 3, 5], [1, 4, 5], [2, 4, 5],
///     // and [3, 4, 5] respectively.
///     println!("{:?}", c);
/// });
/// ```
/// 
/// See [Example implementation](trait.Combination.html#foreign-impls) on
/// foreign type.
pub trait Combination<'a> {
    type Combinator : Iterator;

    /// Create a family of [LargeCombinationIterator](struct.LargeCombinationIterator.html)
    /// of `k` size out of `self`.
    /// See [LargeCombinationIterator](struct.LargeCombinationIterator.html) for
    /// how to use [LargeCombinationIterator](struct.LargeCombinationIterator.html)
    /// 
    /// # Return
    /// A new family of [LargeCombinationIterator<T>](struct.LargeCombinationIterator.html)
    fn combination(&'a self, k : usize) -> Self::Combinator;
}

/// An implementation for convenient use of [LargeCombinationIterator](struct.LargeCombinationIterator.html)
impl<'a, T> Combination<'a> for [T] where T : 'a {
    type Combinator = LargeCombinationIterator<'a, T>;

    fn combination(&'a self, k : usize) -> LargeCombinationIterator<'a, T> {

        LargeCombinationIterator::new(self, k)
    }
}

/// An implementation for convenient use of [LargeCombinationIterator](struct.LargeCombinationIterator.html)
impl<'a, T> Combination<'a> for Vec<T> where T : 'a {
    type Combinator = LargeCombinationIterator<'a, T>;

    fn combination(&'a self, k : usize) -> LargeCombinationIterator<'a, T> {
        
        LargeCombinationIterator::new(self, k)
    }
}

/// A pair of source and sink to get a sharable combination.
/// 
/// It's tuple contains a source data to generate a combination
/// and a sink to temporary store each combination.
/// 
/// This type is use exclusively with [trait Combination](trait.Combination.html#implementors)
/// 
/// # Format
/// 1. First value in tuple is a `&'a [T]` -
/// It's a source data to generate a combination.
/// 2. Second value in tuple is an Rc<RefCell<&'a mut[&'a T]>>` -
/// It's a sink to temporary store each combination.
pub type CombinationIntoCellParams<'a, T> = (&'a [T], Rc<RefCell<&'a mut[&'a T]>>);

/// An implementation for convenient use of [LargeCombinationCellIter](struct.LargeCombinationCellIter.html)
impl<'a, 'b : 'a, T> Combination<'a> for CombinationIntoCellParams<'b, T> {
    type Combinator = LargeCombinationCellIter<'b, T>;

    fn combination(&'a self, k : usize) -> LargeCombinationCellIter<'b, T> {
        LargeCombinationCellIter::new(self.0, k, Rc::clone(&self.1))
    }
}

/// A pair of source and sink to get a sharable combination.
/// 
/// It's tuple contains a source data to generate a combination
/// and a sink to temporary store each combination.
/// 
/// This type is use exclusively with [trait Combination](trait.Combination.html#implementors)
/// 
/// # Format
/// 1. A mutable slice of slices.
/// It's a domains to of a cartesian product operation.
/// 2. A pointer to mutable slice of borrowed value.
/// It's a result container. 
pub type CombinationIntoRefParams<'a, T> = (&'a [T], * mut[&'a T]);

/// An implementation for convenient use of [LargeCombinationRefIter](struct.LargeCombinationRefIter.html)
/// # Warning
/// It hid unsafe object instantiation of [LargeCombinationRefIter](struct.LargeCombinationRefIter.html#method.new)
/// from user but all unsafe conditions are still applied as long as
/// the life of object itself.
impl<'a, 'b : 'a, T> Combination<'a> for CombinationIntoRefParams<'b, T> {
    type Combinator = LargeCombinationRefIter<'b, T>;

    fn combination(&'a self, k : usize) -> LargeCombinationRefIter<'b, T> {
        unsafe {
            LargeCombinationRefIter::new(self.0, k, self.1)
        }
    }
}

/// Create a permutation iterator that permute data in place.
/// Built-in implementation return an object of 
/// [HeapPermutation](struct.HeapPermutationIterator.html) for slice/array and Vec.
/// It return an object of [HeapPermutationCellIter](struct.HeapPermutationCellIter.html)
/// on data type of `Rc<RefCell<&mut [T]>>`.
/// 
/// # Example
/// For typical permutation:
/// ```
/// use permutator::Permutation;
/// let mut data = vec![1, 2, 3];
/// data.permutation().for_each(|p| {
///     // call multiple times. It'll print [2, 1, 3], [3, 1, 2], 
///     // [1, 3, 2], [2, 3, 1], and [3, 2, 1] respectively.
///     println!("{:?}", p);
/// });
/// ```
/// For k-permutation:
/// ```
/// use permutator::{Combination, Permutation};
/// let data = [1, 2, 3, 4, 5];
/// let k = 3;
///
/// data.combination(k).for_each(|mut combination| {
///     // print the first combination
///     println!("{:?}", combination);
///     combination.permutation().for_each(|permuted| {
///         // print permutation of each combination
///         println!("{:?}", permuted);
///     });
/// });
/// // All k-permutation printed
/// ```
/// 
/// # See 
/// - [HeapPermutation](struct.HeapPermutationIterator.html) for more detail
/// about how to use [HeapPermutation](struct.HeapPermutationIterator.html).
/// - [HeapPermutationCellIter](struct.HeapPermutationCellIter.html) for more detail 
/// about how to use [HeapPermutationCellIter](struct.HeapPermutationCellIter.html)
/// - [Example implementation](trait.Permutation.html#foreign-impls) on foreign type
pub trait Permutation<'a> {
    /// A permutation generator for a collection of data.
    /// # See
    /// - [Foreign implementation for an example different return type](trait.Permutation.html#foreign-impls)
    type Permutator : Iterator;

    /// Create a permutation based on Heap's algorithm.
    /// It return [HeapPermutation](struct.HeapPermutationIterator.html) object.
    fn permutation(&'a mut self) -> Self::Permutator;
}

/// Generate permutation on an array or slice of T
/// It return [HeapPermutation](struct.HeapPermutationIterator.html)
impl<'a, T> Permutation<'a> for [T] where T : 'a + Clone {
    /// Use [HeapPermutation](struct.HeapPermutationIterator.html)
    /// as permutation generator
    type Permutator = HeapPermutationIterator<'a, T>;

    fn permutation(&'a mut self) -> HeapPermutationIterator<T> {
        HeapPermutationIterator::new(self)
    }
}

/// Generate permutation on a Vec of T
/// It return [HeapPermutation](struct.HeapPermutationIterator.html)
impl<'a, T> Permutation<'a> for Vec<T> where T : 'a + Clone {
    /// Use [HeapPermutation](struct.HeapPermutationIterator.html)
    /// as permutation generator
    type Permutator = HeapPermutationIterator<'a, T>;

    fn permutation(&'a mut self) -> HeapPermutationIterator<T> {
        HeapPermutationIterator::new(self)
    }
}

/// Generate a sharable permutation inside `Rc<RefCell<&mut [T]>>`
/// It return [HeapPermutationCellIter](struct.HeapPermutationCellIter.html)
impl<'a, T> Permutation<'a> for Rc<RefCell<&'a mut[T]>> where T :'a {
    /// Use [HeapPermutationCellIter](struct.HeapPermutationCellIter.html)
    /// as permutation generator
    type Permutator = HeapPermutationCellIter<'a, T>;

    fn permutation(&'a mut self) -> HeapPermutationCellIter<T> {
        HeapPermutationCellIter {
            c : vec![0; self.borrow().len()],
            data : Rc::clone(self),
            i : 0
        }
    }
}

/// Generate permutation a mutable pointer to slice of T
/// It return [HeapPermutation](struct.HeapPermutationRefIter.html)
/// 
/// # Warning
/// This implementation hid unsafe inside the permutation function but
/// doesn't provide any additional safety. 
/// User need to treat the return object as unsafe.
impl<'a, T> Permutation<'a> for *mut [T] where T : 'a + Clone {
    /// Use [HeapPermutation](struct.HeapPermutationIterator.html)
    /// as permutation generator
    type Permutator = HeapPermutationRefIter<'a, T>;

    fn permutation(&'a mut self) -> HeapPermutationRefIter<T> {
        unsafe {
            HeapPermutationRefIter {
                c : vec![0; (**self).len()],
                data : &mut (**self),
                i : 0
            }
        }
    }
}

/// A pair of parameter that allow `Permutation` trait
/// to create [k-permutation iterator](struct.KPermutationIterator.html) from it.
/// 
/// This type is used exclusively in [trait Permutation](trait.Permutation.html#implementors)
/// 
/// # Format
/// 1. First value in tuple is `&'a [T]`.
/// It's a source data to generate k-permutation.
/// 2. Second value in tuple is `usize`.
/// It's `k` size which shall be less than `n` 
/// where `n` is a length of the first value.
pub type KPermutationParams<'a, T> = (&'a [T], usize);

impl<'a, T> Permutation<'a> for KPermutationParams<'a, T> {
    type Permutator = KPermutationIterator<'a, T>;

    fn permutation(&'a mut self) -> KPermutationIterator<'a, T> {
        KPermutationIterator::new(self.0, self.1)
    }
}

/// A tuples of 3 parameters that allow `Permutation` trait
/// to create [k-permutation iterator](struct.KPermutationCellIter.html) from it.
/// 
/// This type is used exclusively in [trait Permutation](trait.Permutation.html#implementors)
/// 
/// # Format
/// 1. First value in tuple is `&'a [T]`.
/// It's a source data to generate k-permutation.
/// 2. Second value in tuple is `usize`.
/// It's `k` size which shall be less than `n` 
/// where `n` is a length of the first value.
/// 3. Third value in tuple is `Rc<RefCell<&mut[&T]>>`
/// It's a sink of operation. It's a ref to each permutation result.
pub type KPermutationIntoCellParams<'a, T> = (&'a [T], usize, Rc<RefCell<&'a mut [&'a T]>>);

impl<'a, 'b : 'a, T> Permutation<'a> for KPermutationIntoCellParams<'b, T> {
    type Permutator = KPermutationCellIter<'b, T>;

    fn permutation(&'a mut self) -> Self::Permutator {
        KPermutationCellIter::new(self.0, self.1, Rc::clone(&self.2))
    }
}

/// A tuple of 3 parameters that allow `Permutation` trait
/// to create [k-permutation ref iterator](struct.KPermutationRefIterator.html) from it.
/// 
/// This type is used exclusively in [trait Permutation](trait.Permutation.html#implementors)
/// 
/// # Format
/// 1. First value in tuple is `&'a [T]`.
/// It's a source data to generate k-permutation.
/// 2. Second value in tuple is `usize`.
/// It's `k` size which shall be less than `n` 
/// where `n` is a length of the first value.
/// 3. Third value in tule i `*mut [&T]`
/// It's a sink that store a ref to each permutation.
pub type KPermutationIntoRefParams<'a, T> = (&'a [T], usize, *mut [&'a T]);

impl<'a, 'b : 'a, T> Permutation<'a> for KPermutationIntoRefParams<'b, T> {
    type Permutator = KPermutationRefIter<'b, T>;

    fn permutation(&'a mut self) -> Self::Permutator {
        unsafe {
            KPermutationRefIter::new(self.0, self.1, &mut *self.2)
        }
    }
}

/// # Deprecated
/// Superseded by algorithm published by Stanford university
/// Generate binary representation of combination inside
/// usize. It mutate variable in place.
/// It'll return None when there's no further possible 
/// combination by given x. 
#[allow(unused)]
fn gosper_combination(x : &mut u128) -> Option<()> {
    let u = *x & x.overflowing_neg().0; // get LSB that has 1
    let v = u + *x; // Add LSB to x
    if v == 0 {
        return None
    }
    
    *x = v + (((v ^ *x) / u) >> 2);
    Some(())
}

/// Generate binary representation of combination by
/// using algorithm published by Stanford university.
/// The different from original Gosper algorithm is
/// it eliminate divide operation by using built in
/// trailing_zeros function.
/// 
/// # Limitation
/// Gosper algorithm need to know the MSB (most significant bit).
/// The current largest known MSB data type is u128.
/// This make the implementation support up to 128 elements slice.
/// 
/// Reference:
/// - [Compute the lexicographically next bit permutation](http://graphics.stanford.edu/~seander/bithacks.html#NextBitPermutation)
#[inline(always)]
fn stanford_combination(x: &mut u128) {
    let t = *x | (*x - 1); // get x and set LSB set to 1
    // Next set to 1 the most significant bit to change, 
    // set to 0 the least significant ones, and add the necessary 1 bits.
    *x = (t + 1) | (((!t & (!t).overflowing_neg().0) - 1) >> (x.trailing_zeros() + 1));
}

/// Calculate factorial from given value.
pub fn factorial<T>(n: T) -> T where T : PrimInt + Unsigned + Product {
    num::range(T::one(), n + T::one()).product()
}

/// Calculate factorial for two factorial division.
/// It'll return 1 if numerator is smaller or equals to denominator.
/// Otherwise, it'll short circuit the calculation by calculate only
/// the undivided remainder.
/// 
/// # Examples
/// ```
/// use permutator::divide_factorial;
/// 
/// // calculate 5!/3!
/// divide_factorial(5u8, 3u8); // return 5 * 4 = 20
/// // calculate 3!/5!
/// divide_factorial(3u32, 5u32); // return 1.
/// // calculate 5!/5!
/// divide_factorial(5u16, 5u16); // return 1.
/// ```
pub fn divide_factorial<T>(numerator: T, denominator: T) -> T where T : PrimInt + Unsigned + Product {
    if numerator < denominator {
        T::one()
    } else if denominator < numerator {
        num::range_inclusive(denominator + T::one(), numerator).product()
    } else {
        T::one()
    }
}

/// Calculate two factorial multiply on each other.
/// It'll try to reduce calculation time by calculate the
/// common value only once.
/// 
/// # Examples
/// ```
/// use permutator::multiply_factorial;
/// // 5! * 4!
/// multiply_factorial(5u32, 4u32); // calculate 4! and power it by 2 then multiply by 5.
/// multiply_factorial(4u32, 5u32); // perform similar to above step.
/// multiply_factorial(5u128, 5u128); // calculate 5! and power it by 2.
/// ```
pub fn multiply_factorial<T>(fact1: T, fact2: T) -> T where T : PrimInt + Unsigned + Product {
    if fact1 < fact2 {
        let common = factorial(fact1);
        common.pow(2) * num::range_inclusive(fact1 + T::one(), fact2).product()
    } else if fact2 < fact1 {
        let common = factorial(fact2);
        common.pow(2) * num::range_inclusive(fact2 + T::one(), fact1).product()
    } else {
        return factorial(fact1).pow(2);
    }
}

/// Initiate a first combination along with Gospel's map for further
/// combination calculation.
/// The name k_set refer to the use case of k-permutation.
/// It's first k combination of data `d` inside single set.
fn create_k_set<T>(d : &[T], width : usize) -> (Vec<&T>, u128) {
    let mask = (1 << width) - 1;
    let mut copied_mask = mask;
    let mut i = 0;
    let mut subset = Vec::new();
    while copied_mask > 0 {
        if copied_mask & 1 == 1 {
            subset.push(&d[i]);
        }
        i += 1;
        copied_mask >>= 1;
    }
    (subset, mask)
}

/// Similar to create_k_set but return result through unsafe pointer
/// # Parameters
/// - `d` A raw data to get a subset `k`
/// - `width` A size of subset, AKA `k`
/// - `result` A mutable pointer that will be stored `k` subset
/// - `mask` A gosper bit map
/// # See
/// - [create_k_set](fn.create_k_set.html)
unsafe fn unsafe_create_k_set<'a, T>(d : &'a[T], width : usize, result : *mut [&'a T], mask : &mut u128) {
    *mask = (1 << width) - 1;
    let mut copied_mask = *mask;
    let mut i = 0;
    let mut j = 0;
    
    while copied_mask > 0 {
        if copied_mask & 1 == 1 {
            (*result)[j] = &d[i];
            j += 1;
        }
        i += 1;
        copied_mask >>= 1;
    }
}

/// Similar to create_k_set but return result through Rc<RefCell<&'a mut[&'a T]>>
/// # Parameters
/// - `d` A raw data to get a subset `k`
/// - `width` A size of subset, AKA `k`
/// - `result` An ref to Rc<RefCell<>> storing mutable slice that will be stored `k` subset
/// - `mask` A gosper bit map
/// # See
/// - [create_k_set](fn.create_k_set.html)
fn create_k_set_in_cell<'a, T>(d : &'a[T], width : usize, result : &Rc<RefCell<&'a mut[&'a T]>>, mask : &mut u128) {
    *mask = (1 << width) - 1;
    let mut copied_mask = *mask;
    let mut i = 0;
    let mut j = 0;
    
    while copied_mask > 0 {
        if copied_mask & 1 == 1 {
            result.borrow_mut()[j] = &d[i];
            j += 1;
        }
        i += 1;
        copied_mask >>= 1;
    }
}

/// Similar to create_k_set but return result through Rc<RefCell<&'a mut[&'a T]>>
/// # Parameters
/// - `d` A raw data to get a subset `k`
/// - `width` A size of subset, AKA `k`
/// - `result` An ref to Rc<RefCell<>> storing mutable slice that will be stored `k` subset
/// - `mask` A gosper bit map
/// # See
/// - [create_k_set](fn.create_k_set.html)
fn create_k_set_sync<'a, T>(d : &'a[T], width : usize, result : &Arc<RwLock<Vec<&'a T>>>, mask : &mut u128) {
    *mask = (1 << width) - 1;
    let mut copied_mask = *mask;
    let mut i = 0;
    let mut j = 0;
    
    while copied_mask > 0 {
        if copied_mask & 1 == 1 {
            result.write().unwrap()[j] = &d[i];
            j += 1;
        }
        i += 1;
        copied_mask >>= 1;
    }
}

/// Swap variable into data k sized data set. It take a pair of k size data set with
/// associated Gospel's map. It'll then replace all data in set with new combination
/// map generated by Gospel's algorithm. The replacement is done in place.
/// The function return `Some(())` to indicate that new combination replacement is done.
/// If there's no further combination, it'll return `None`.
#[inline(always)]
fn swap_k<'a, 'b : 'a, 'c : 'b, T : 'c>(subset_map : (&'a mut [&'b T], &mut u128), d : &'c[T]) -> Option<()> {
    // Replace original Gosper's algorithm by using enhanced version from Stanford University instead
    // if let Some(_) = gosper_combination(subset_map.1) {
    //     let mut copied_mask = *subset_map.1;
    //     let n = d.len();
    //     let mut i = 0;
    //     let mut j = 0;
    //     while copied_mask > 0 && i < n {
    //         if copied_mask & 1 == 1 {
    //             subset_map.0[j] = &d[i];
    //             j += 1;
    //         }
    //         i += 1;
    //         copied_mask >>= 1;
    //     }

    //     if copied_mask > 0 { // mask goes over the length of `d` now.
    //         None
    //     } else {
    //         Some(())
    //     }
    // } else {
    //     None
    // }

    stanford_combination(subset_map.1);
    let mut copied_mask = *subset_map.1;
    let n = d.len();
    let mut i = 0;
    let mut j = 0;
    while copied_mask > 0 && i < n {
        if copied_mask & 1 == 1 {
            subset_map.0[j] = &d[i];
            j += 1;
        }
        i += 1;
        copied_mask >>= 1;
    }

    if copied_mask > 0 { // mask goes over the length of `d` now.
        None
    } else {
        Some(())
    }
}
/// Swap variable into data k sized data set. It take a pair of k size data set with
/// associated Gospel's map. It'll then replace all data in set with new combination
/// map generated by Gospel's algorithm. The replacement is done in place.
/// The function return `Some(())` to indicate that new combination replacement is done.
/// If there's no further combination, it'll return `None`.
fn swap_k_in_cell<'a, 'b : 'a, T>(subset_map : (&Rc<RefCell<&'a mut [&'b T]>>, &mut u128), d : &'b[T]) -> Option<()> {
    // Replace original Gosper's algorithm by using enhanced version from Stanford University instead
    // if let Some(_) = gosper_combination(subset_map.1) {
    //     let mut copied_mask = *subset_map.1;
    //     let n = d.len();
    //     let mut i = 0;
    //     let mut j = 0;
    //     while copied_mask > 0 && i < n {
    //         if copied_mask & 1 == 1 {
    //             subset_map.0[j] = &d[i];
    //             j += 1;
    //         }
    //         i += 1;
    //         copied_mask >>= 1;
    //     }

    //     if copied_mask > 0 { // mask goes over the length of `d` now.
    //         None
    //     } else {
    //         Some(())
    //     }
    // } else {
    //     None
    // }

    stanford_combination(subset_map.1);
    let mut copied_mask = *subset_map.1;
    let n = d.len();
    let mut i = 0;
    let mut j = 0;
    while copied_mask > 0 && i < n {
        if copied_mask & 1 == 1 {
            subset_map.0.borrow_mut()[j] = &d[i];
            j += 1;
        }
        i += 1;
        copied_mask >>= 1;
    }

    if copied_mask > 0 { // mask goes over the length of `d` now.
        None
    } else {
        Some(())
    }
}

/// Swap variable into data k sized data set. It take a pair of k size data set with
/// associated Gospel's map. It'll then replace all data in set with new combination
/// map generated by Gospel's algorithm. The replacement is done in place.
/// The function return `Some(())` to indicate that new combination replacement is done.
/// If there's no further combination, it'll return `None`.
fn swap_k_sync<'a, 'b : 'a, T>(subset_map : (&Arc<RwLock<Vec<&'b T>>>, &mut u128), d : &'b[T]) -> Option<()> {
    // Replace original Gosper's algorithm by using enhanced version from Stanford University instead
    // if let Some(_) = gosper_combination(subset_map.1) {
    //     let mut copied_mask = *subset_map.1;
    //     let n = d.len();
    //     let mut i = 0;
    //     let mut j = 0;
    //     while copied_mask > 0 && i < n {
    //         if copied_mask & 1 == 1 {
    //             subset_map.0[j] = &d[i];
    //             j += 1;
    //         }
    //         i += 1;
    //         copied_mask >>= 1;
    //     }

    //     if copied_mask > 0 { // mask goes over the length of `d` now.
    //         None
    //     } else {
    //         Some(())
    //     }
    // } else {
    //     None
    // }

    stanford_combination(subset_map.1);
    let mut copied_mask = *subset_map.1;
    let n = d.len();
    let mut i = 0;
    let mut j = 0;
    while copied_mask > 0 && i < n {
        if copied_mask & 1 == 1 {
            subset_map.0.write().unwrap()[j] = &d[i];
            j += 1;
        }
        i += 1;
        copied_mask >>= 1;
    }

    if copied_mask > 0 { // mask goes over the length of `d` now.
        None
    } else {
        Some(())
    }
}

#[cfg(test)]
pub mod test {
    use super::*;
    use std::thread;
    use std::sync::mpsc;
    use std::sync::mpsc::{SyncSender, Receiver};

    #[test]
    fn test_get_cartesian_for() {
        let words = ["word1", "word2", "word3"];
        let result = [[&words[0], &words[0]], [&words[0], &words[1]],
                    [&words[0], &words[2]], [&words[1], &words[0]],
                    [&words[1], &words[1]], [&words[1], &words[2]],
                    [&words[2], &words[0]], [&words[2], &words[1]],
                    [&words[2], &words[2]]];
        for (i, r) in result.iter().enumerate() {
            assert_eq!(get_cartesian_for(&words, 2, i).unwrap(), r, "Fail to get cartesian product degree 2@i={}", i);
        }

        assert_eq!(get_cartesian_for(&words, 4, 0).is_err(), true, "Unexpected no error when degree is larger than size of objects");
        
        for (i, w) in words.iter().enumerate() {
            assert_eq!(get_cartesian_for(&words, 1, i).unwrap()[0], w, "Fail to get cartesian product degree 1@i={}", i);
        }

        assert_eq!(get_cartesian_for(&words, 0, 0).unwrap().len(), 0, "Fail to get cartesian product degree 0");
    }

    #[test]
    fn test_get_permutation_for() {
        let words = ["word1", "word2", "word3"];
        let result = [[&words[0], &words[1]], [&words[0], &words[2]], 
                    [&words[1], &words[0]], [&words[1], &words[2]],
                    [&words[2], &words[0]], [&words[2], &words[1]]];
        for (i, r) in result.iter().enumerate() {
            assert_eq!(get_permutation_for(&words, 2, i).unwrap(), r, "Fail to get permutation degree 2@i={}", i);
        }

        assert_eq!(get_permutation_for(&words, 4, 0).is_err(), true, "Unexpected no error when degree is larger than size of objects");
        
        for (i, w) in words.iter().enumerate() {
            assert_eq!(get_permutation_for(&words, 1, i).unwrap()[0], w, "Fail to get permutation degree 1@i={}", i);
        }

        assert_eq!(get_permutation_for(&words, 0, 0).unwrap().len(), 0, "Fail to get permutation degree 0");
    }

    #[test]
    fn test_heap_permutation_6() {
        let mut data = [1, 2, 3, 4, 5, 6];
        let mut counter = 1;
        heap_permutation(&mut data, |_| {
            counter +=1;
        });

        assert_eq!(720, counter);
    }

    #[test]
    fn test_heap_permutation_10() {
        use std::time::{Instant};
        let mut data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let mut counter = 1;
        let timer = Instant::now();
        // println!("{:?}", data);
        heap_permutation(&mut data, |_| {
            // println!("{:?}", perm);
            counter += 1;
        });

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
        assert_eq!(3628800, counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_CartesianProduct() {
        use std::time::Instant;
        let data : &[&[usize]] = &[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]];
        let cart = CartesianProductIterator::new(&data);
        let mut counter = 0;
        let timer = Instant::now();

        for p in cart {
            // println!("{:?}", p);
            counter += 1;
        }

        assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
        println!("Total {} products done in {:?}", counter, timer.elapsed());
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_SelfCartesianProduct() {
        use std::time::Instant;
        let data : &[usize] = &[1, 2, 3];
        let n = 3;
        let cart = SelfCartesianProductIterator::new(&data, n);
        let mut counter = 0;
        let timer = Instant::now();

        for p in cart {
            println!("{:?}", p);
            counter += 1;
        }

        assert_eq!(data.len().pow(n as u32), counter);
        println!("Total {} products done in {:?}", counter, timer.elapsed());
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_CartesianProduct_reset() {
        use std::time::Instant;
        let data : &[&[usize]] = &[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]];
        let mut counter = 0;
        let mut result : Vec<&usize> = vec![&data[0][0]; data.len()];
        unsafe {
            let mut cart = CartesianProductRefIter::new(&data, result.as_mut_slice());
            let timer = Instant::now();

            while let Some(_) = cart.next() {
                counter += 1;
            }

            let all_possible = data.iter().fold(1, |cum, domain| {cum * domain.len()});
            assert_eq!(all_possible, counter);

            counter = 0;
            // it shall end immediately because it's already exhausted
            while let Some(_) = cart.next() {
                counter += 1;
            }

            assert_eq!(0, counter);

            cart.reset();
            counter = 0;
            
            // now it shall start iterating again.
            for _ in cart {
                counter += 1;
            }

            assert_eq!(all_possible, counter); 

            println!("Total {} products done in {:?}", counter, timer.elapsed());
        }
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_CartesianProduct_mimic_iterator() {
        use std::time::Instant;
        let data : &[&[usize]] = &[&[1, 2], &[3, 4, 5, 6], &[7, 8, 9], &[10, 11, 12,]];
        let mut result : Vec<&usize> = vec![&data[0][0]; data.len()];
        unsafe {
            let mut cart = CartesianProductRefIter::new(&data, result.as_mut_slice());
            let mut counter = 0;
            let timer = Instant::now();

            for _ in cart {
                // println!("{:?}", p);
                counter += 1;
            }

            assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
            println!("Total {} products done in {:?}", counter, timer.elapsed());
        }
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_SelfCartesianProduct_cell() {
        use std::time::Instant;
        let data : &[usize] = &[1, 2, 3];
        let n = 3;
        let mut result = vec![&data[0]; n];
        let shared = Rc::new(RefCell::new(result.as_mut_slice()));
        let cart = SelfCartesianProductCellIter::new(&data, n, Rc::clone(&shared));
        let mut counter = 0;
        let timer = Instant::now();

        for _ in cart {
            println!("{:?}", &*shared.borrow());
            counter += 1;
        }

        assert_eq!(data.len().pow(n as u32), counter);
        println!("Total {} products done in {:?}", counter, timer.elapsed());
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_SelfCartesianProduct_ref() {
        use std::time::Instant;
        let data : &[usize] = &[1, 2, 3];
        let n = 3;
        let result : &mut[&usize] = &mut vec![&data[0]; n];
        let shared = result as *mut[&usize];
        unsafe {
            let cart = SelfCartesianProductRefIter::new(&data, n, result);
            let mut counter = 0;
            let timer = Instant::now();

            for _ in cart {
                println!("{:?}", &*shared);
                counter += 1;
            }

            assert_eq!(data.len().pow(n as u32), counter);
            println!("Total {} products done in {:?}", counter, timer.elapsed());
        }
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_CartesianProduct_mimic_iterator_2() {
        use std::time::Instant;
        let data : &[&[usize]] = &[&[1, 2], &[3, 4, 5, 6], &[7, 8, 9], &[10, 11, 12,]];
        let mut result : Vec<&usize> = vec![&data[0][0]; data.len()];
        unsafe {
            let mut cart = CartesianProductRefIter::new(&data, result.as_mut_slice() as *mut [&usize]);
            let mut counter = 0;
            let timer = Instant::now();

            for _ in cart {
                // println!("{:?}", p);
                counter += 1;
            }

            assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
            println!("Total {} products done in {:?}", counter, timer.elapsed());
        }
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_CartesianProduct_trait() {
        use std::time::Instant;
        
        let mut counter = 0;
        let timer = Instant::now();
        let data : &[&[u8]]= &[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]];

        data.cart_prod().for_each(|p| {
            counter += 1;
        });

        assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
        println!("Total {} products done in {:?}", counter, timer.elapsed());
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_CartesianProduct_shared_trait() {
        use std::time::Instant;
        
        let mut counter = 0;
        let timer = Instant::now();
        let data : &[&[u8]]= &[&[1, 2], &[3, 4, 5, 6], &[7, 8, 9], &[10, 11, 12,]];;
        let mut result = vec![&data[0][0]; data.len()];
        let shared = Rc::new(RefCell::new(result.as_mut_slice()));

        (data, Rc::clone(&shared)).cart_prod().for_each(|_| {
            counter += 1;
        });

        assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
        println!("Total {} products done in {:?}", counter, timer.elapsed());
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_CartesianProduct_ptr_trait() {
        use std::time::Instant;
        
        let mut counter = 0;
        let timer = Instant::now();
        let data : &[&[u8]]= &[&[1, 2], &[3, 4, 5, 6], &[7, 8, 9], &[10, 11, 12,]];;
        let mut result = vec![&data[0][0]; data.len()];
        let shared = result.as_mut_slice() as *mut [&u8];

        (data, shared).cart_prod().for_each(|_| {
            counter += 1;
        });

        assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
        println!("Total {} products done in {:?}", counter, timer.elapsed());
    }

    #[allow(unused)]
    #[test]
    fn test_k_permutation_fn() {
        use std::time::{Instant};
        let data = [1, 2, 3, 4, 5];
        let k = 3;
        let mut counter = 0;
        let timer = Instant::now();
        k_permutation(&data, k, |permuted| {
            // uncomment line below to print all k-permutation
            println!("{}:{:?}", counter, permuted);
            counter += 1;
        });

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
        assert_eq!(divide_factorial(data.len(), data.len() - k), counter);
    }

    #[allow(unused)]
    #[should_panic]
    #[test]
    fn test_k_permutation_empty_dom() {
        use std::time::{Instant};
        let data : &[i32] = &[];
        let k = 1;
        let mut counter = 0;
        let timer = Instant::now();
        k_permutation(&data, k, |permuted| {
            // uncomment line below to print all k-permutation
            println!("{}:{:?}", counter, permuted);
            counter += 1;
        });

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
        assert_eq!(divide_factorial(data.len(), data.len() - k), counter);
    }

    #[allow(unused)]
    #[test]
    fn test_k_permutation_k_1() {
        use std::time::{Instant};
        let data : &[i32] = &[1, 2];
        let k = 1;
        let mut counter = 0;
        let timer = Instant::now();
        k_permutation(&data, k, |permuted| {
            // uncomment line below to print all k-permutation
            println!("{}:{:?}", counter, permuted);
            counter += 1;
        });

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
        assert_eq!(divide_factorial(data.len(), data.len() - k), counter);
    }

    #[allow(unused)]
    #[test]
    #[ignore]
    fn test_large_k_permutation() {
        use std::time::{Instant};
        let data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
        let k = 11;
        let mut counter = 0;
        let timer = Instant::now();
        k_permutation(&data, k, |permuted| {
            // uncomment line below to print all k-permutation
            // println!("{}:{:?}", counter, permuted);
            counter += 1;
        });

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
        assert_eq!(divide_factorial(data.len(), data.len() - k), counter);
    }


    // #[test]
    // fn test_gosper_combination() {
    //     let mut comb = 7;

    //     for _ in 0..40 {
    //         gosper_combination(&mut comb);
    //         println!("next_combination is {:b}", comb);
    //     }

    // }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_HeapPermutation() {
        use std::time::{Instant};
        let mut data : Vec<String> = (1..=3).map(|num| {format!("some ridiculously long word prefix without any point{}", num)}).collect();
        // let data = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        // println!("0:{:?}", data);
        let mut permutator = HeapPermutationIterator::new(&mut data);
        let timer = Instant::now();
        let mut counter = 1;

        while let Some(permutated) = permutator.next() {
            // println!("{}:{:?}", counter, permutated);
            counter += 1;
        }

        assert_eq!(6, counter);
        println!("Done {} permutations in {:?}", counter, timer.elapsed());
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_XPermutationIterator() {
        use std::time::{Instant};
        let mut data : Vec<u32> = (0..3).map(|num| num).collect();
        let mut permutator = XPermutationIterator::new(&data, |_| true);
        let timer = Instant::now();
        let mut counter = 0;

        while let Some(permutated) = permutator.next() {
            // println!("{}:{:?}", counter, permutated);
            counter += 1;
        }

        assert_eq!(factorial(data.len()), counter);
        println!("Done {} permutations in {:?}", counter, timer.elapsed());
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_XPermutationCellIter() {
        use std::time::{Instant};
        let mut data : Vec<u32> = (0..3).map(|num| num).collect();
        let mut result = vec![&data[0]; data.len()];
        let share = Rc::new(RefCell::new(result.as_mut_slice()));
        let mut permutator = XPermutationCellIter::new(&data, Rc::clone(&share), |_| true);
        let timer = Instant::now();
        let mut counter = 0;

        while let Some(_) = permutator.next() {
            println!("{}:{:?}", counter, &*share.borrow());
            counter += 1;
        }

        assert_eq!(factorial(data.len()), counter);
        println!("Done {} permutations in {:?}", counter, timer.elapsed());
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_XPermutationRefIter() {
        use std::time::{Instant};
        let mut data : Vec<u32> = (0..3).map(|num| num).collect();
        let mut result = vec![&data[0]; data.len()];
        let share = result.as_mut_slice() as *mut [&u32];
        unsafe {
            let mut permutator = XPermutationRefIter::new(&data, share, |_| true);
            let timer = Instant::now();
            let mut counter = 0;

            while let Some(_) = permutator.next() {
                println!("{}:{:?}", counter, result);
                counter += 1;
            }

            assert_eq!(factorial(data.len()), counter);
            println!("Done {} permutations in {:?}", counter, timer.elapsed());
        }
    }

    #[allow(non_snake_case, unused)]
    #[ignore]
    #[test]
    fn test_XPermutationIterator_mt() {
        use std::time::{Instant};
        let data : Vec<usize> = (0..3).map(|num| num).collect();
        let threads = 3;
        let chunk = data.len() / threads;
        let (tx, rx) = mpsc::channel();

        for i in 0..threads {
            let start = chunk * i;
            let end = match i {
                j if j == threads - 1 => data.len(), // last thread handle remaining work
                _ => chunk * (i + 1)
            };
            

            let l_dat = data.to_owned(); // copy data for each thread
            let end_sig = tx.clone();

            thread::spawn(move || {
                let timer = Instant::now();

                let perm = XPermutationIterator::new(
                    &l_dat, 
                    |v| *v[0] >= start && *v[0] < end // skip branch that is outside the start/end
                );

                let mut counter = 0u64;

                for p in perm {
                    // each permutation is stored in p
                    counter += 1;
                }

                end_sig.send(i).unwrap();
            });
        }

        let main = thread::spawn(move || { // main thread
            let mut counter = 0;

            while counter < threads {
                let i = rx.recv().unwrap();
                // do something 
                counter += 1;
            }
        });

        main.join().unwrap();
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_HeapPermutation_reset() {
        use std::time::{Instant};
        let mut data : Vec<String> = (1..=3).map(|num| {format!("some ridiculously long word prefix without any point{}", num)}).collect();
        // let data = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        println!("0:{:?}", data);
        let mut permutator = HeapPermutationIterator::new(&mut data);
        let timer = Instant::now();
        let mut counter = 1;

        while let Some(permutated) = permutator.next() {
            // println!("{}:{:?}", counter, permutated);
            counter += 1;
        }

        assert_eq!(6, counter);

        let mut counter = 1;

        while let Some(permutated) = permutator.next() {
            // println!("{}:{:?}", counter, permutated);
            counter += 1;
        }

        assert_eq!(1, counter);
        
        permutator.reset();
        let mut counter = 1;

        while let Some(permutated) = permutator.next() {
            // println!("{}:{:?}", counter, permutated);
            counter += 1;
        }

        assert_eq!(6, counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_HeapPermutationIntoIterator() {
        use std::time::{Instant};
        let mut data : Vec<String> = (1..=3).map(|num| {format!("some ridiculously long word prefix without any point{}", num)}).collect();
        // let data = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        println!("0:{:?}", data);
        let permutator = HeapPermutationIterator::new(&mut data);
        let timer = Instant::now();
        let mut counter = 1;

        permutator.into_iter().for_each(|permutated| {counter += 1;});

        println!("Done {} permutations in {:?}", counter, timer.elapsed());
        assert_eq!(6, counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_HeapPermutationRefIterator() {
        use std::time::{Instant};
        let mut data : Vec<String> = (1..=3).map(|num| {format!("some ridiculously long word prefix without any point{}", num)}).collect();
        // let data = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        // println!("0:{:?}", data);
        unsafe {
            let mut permutator = HeapPermutationRefIter::new(data.as_mut_slice());
            let timer = Instant::now();
            let mut counter = 1;

            while let Some(permutated) = permutator.next() {
                // println!("{}:{:?}", counter, permutated);
                counter += 1;
            }

            assert_eq!(6, counter);
            println!("Done perm_ref {} permutations in {:?}", counter, timer.elapsed());
        }
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_HeapPermutationCellIterIterator() {
        use std::time::{Instant};
        let mut data : Vec<String> = (1..=3).map(|num| {format!("some ridiculously long word prefix without any point{}", num)}).collect();
        let shared = Rc::new(RefCell::new(data.as_mut_slice()));
        // let data = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let permutator = HeapPermutationCellIter::new(Rc::clone(&shared));
        println!("{}:{:?}", 0, &*shared.borrow()); 
        let timer = Instant::now();
        let mut counter = 1;

        for _ in permutator {
            println!("{}:{:?}", counter, &*shared.borrow());
            counter += 1;
        }

        println!("Done {} permutations in {:?}", counter, timer.elapsed());
        assert_eq!(6, counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_GosperCombinationIterator() {
        use std::time::{Instant};
        let gosper = GosperCombinationIterator::new(&[1, 2, 3, 4, 5], 3);
        let mut counter = 0;
        let timer = Instant::now();

        for combination in gosper {
            // println!("{}:{:?}", counter, combination);
            counter += 1;
        }

        println!("Total {} combinations in {:?}", counter, timer.elapsed());
        assert_eq!(10, counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_LargeCombinationIterator() {
        use std::time::{Instant};
        let data : &[i32] = &[1, 2, 3, 4, 5];
        let k = 3;
        let mut combs = LargeCombinationIterator::new(data, k);
        let mut counter = 0;
        let timer = Instant::now();

        for combination in combs.iter() {
            println!("{}:{:?}", counter, combination);
            counter += 1;
        }

        println!("Total {} combinations in {:?}", counter, timer.elapsed());
        assert_eq!(divide_factorial(data.len(), data.len() - k) / factorial(k), counter);

        // test continue on exhausted iterator
        for combination in combs.iter() {
            println!("{}:{:?}", counter, combination);
            counter += 1;
        }
        assert_eq!(divide_factorial(data.len(), data.len() - k) / factorial(k), counter);
        
        // test reset the iterator
        combs.reset();
        let mut counter = 0;
        let timer = Instant::now();

        for combination in combs.iter() {
            println!("{}:{:?}", counter, combination);
            counter += 1;
        }

        println!("Total {} combinations in {:?}", counter, timer.elapsed());
        assert_eq!(divide_factorial(data.len(), data.len() - k) / factorial(k), counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_LargeCombinationIterator_single() {
        use std::time::{Instant};
        let data : &[i32] = &[1, 2, 3, 4, 5];
        let k = 1;
        let mut combs = LargeCombinationIterator::new(data, k);
        let mut counter = 0;
        let timer = Instant::now();

        for combination in combs.iter() {
            println!("{}:{:?}", counter, combination);
            counter += 1;
        }

        println!("Total {} combinations in {:?}", counter, timer.elapsed());
        assert_eq!(divide_factorial(data.len(), data.len() - k) / factorial(k), counter);

        // test continue on exhausted iterator
        for combination in combs.iter() {
            println!("{}:{:?}", counter, combination);
            counter += 1;
        }
        assert_eq!(divide_factorial(data.len(), data.len() - k) / factorial(k), counter);
        
        // test reset the iterator
        combs.reset();
        let mut counter = 0;
        let timer = Instant::now();

        for combination in combs.iter() {
            println!("{}:{:?}", counter, combination);
            counter += 1;
        }

        println!("Total {} combinations in {:?}", counter, timer.elapsed());
        assert_eq!(divide_factorial(data.len(), data.len() - k) / factorial(k), counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_GosperCombinationIteratorUnsafe() {
        use std::time::{Instant};
        let data = &[1, 2, 3, 4, 5, 6];
        let r = 4;
        let mut counter = 0;
        let timer = Instant::now();
        let mut result = vec![&data[0]; r];
        unsafe {
            let mut gosper = GosperCombinationRefIter::new(data, r, result.as_mut_slice() as *mut [&i32]);

            for _ in gosper {
                // println!("{}:{:?}", counter, combination);
                counter += 1;
            }

            println!("Total {} combinations in {:?}", counter, timer.elapsed());
            assert_eq!(counter, divide_factorial(data.len(), data.len() - r) / factorial(r));
        }
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_GosperCombinationCellIter() {
        use std::time::{Instant};
        let data = &[1, 2, 3, 4, 5, 6];
        let r = 3;
        let mut counter = 0;
        let timer = Instant::now();
        let mut result = vec![&data[0]; r];
        let shared = Rc::new(RefCell::new(result.as_mut_slice()));

        let mut gosper = GosperCombinationCellIter::new(data, r, Rc::clone(&shared));

        for _ in gosper {
            // println!("{}:{:?}", counter, &*shared.borrow());
            counter += 1;
        }

        println!("Total {} combinations in {:?}", counter, timer.elapsed());
        assert_eq!(counter, divide_factorial(data.len(), data.len() - r) / factorial(r));
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_GosperCombinationIteratorAlike_reset() {
        use std::time::{Instant};
        let data = &[1, 2, 3, 4, 5];
        let r = 3;
        let mut counter = 0;
        let timer = Instant::now();
        let mut result = vec![&data[0]; r];
        unsafe {
            let mut gosper = GosperCombinationRefIter::new(data, r, result.as_mut_slice() as *mut [&i32]);
            let mut iter = gosper.into_iter();

            while let Some(_) = iter.next() {
                println!("{}:{:?}", counter, result);
                counter += 1;
            }

            println!("Total {} combinations in {:?}", counter, timer.elapsed());
            let all_possible = divide_factorial(data.len(), r) / factorial(data.len() - r);
            assert_eq!(all_possible, counter);
            counter = 0;

            while let Some(_) = iter.next() {
                // println!("{}:{:?}", counter, combination);
                counter += 1;
            }
            assert_eq!(0, counter);
            iter.reset();
            counter = 0;

            while let Some(_) = iter.next() {
                // println!("{}:{:?}", counter, combination);
                counter += 1;
            }
            assert_eq!(all_possible, counter);
        }
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_KPermutationIterator() {
        use std::time::Instant;
        let data = [1, 2, 3, 4, 5];
        let k = 3;
        let permutator = KPermutationIterator::new(&data, k);
        let mut counter = 0;
        // println!("Begin testing KPermutation");
        let timer = Instant::now();

        for permuted in permutator {
            println!("{}:{:?}", counter, permuted);
            counter += 1;
        }

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
        assert_eq!(divide_factorial(data.len(), data.len() - k), counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_KPermutationIteratorBound() {
        use std::time::Instant;
        let data = [1, 2, 3, 4];
        let k = 4;
        let permutator = KPermutationIterator::new(&data, k);
        let mut counter = 0;
        // println!("Begin testing KPermutation");
        let timer = Instant::now();

        for permuted in permutator {
            println!("{}:{:?}", counter, permuted);
            counter += 1;
        }

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
        assert_eq!(divide_factorial(data.len(), data.len() - k), counter);
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_KPermutation_into_Cell() {
        use std::time::Instant;

        let data : &[i32] = &[1, 2, 3, 4, 5];
        let mut counter = 0;
        let k = 3;
        let mut result : Vec<&i32> = vec![&data[0]; k];
        let shared = Rc::new(RefCell::new(result.as_mut_slice()));
        let timer = Instant::now();
        KPermutationCellIter::new(data, k, Rc::clone(&shared)).into_iter().for_each(|_| {
            // println!("{:?}", &*shared);
            counter += 1;
        });

        println!("Total {} combination done in {:?}", counter, timer.elapsed());
        assert_eq!(counter, divide_factorial(data.len(), data.len() - k));
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_KPermutation_into_Ref() {
        use std::time::Instant;

        let data : &[i32] = &[1, 2, 3, 4, 5];
        let mut counter = 0;
        let k = 3;
        let mut result : Vec<&i32> = vec![&data[0]; k];
        let shared = result.as_mut_slice() as *mut [&i32];
        let timer = Instant::now();
        unsafe {
            KPermutationRefIter::new(data, k, shared).into_iter().for_each(|_| {
                // println!("{:?}", &*shared);
                counter += 1;
            });

            println!("Total {} combination done in {:?}", counter, timer.elapsed());
            assert_eq!(counter, divide_factorial(data.len(), data.len() - k));
        }
    }

    #[allow(unused)]
    #[test]
    fn test_cartesian_product() {
        use std::time::Instant;
        let set = (1..4).map(|item| item).collect::<Vec<u64>>();
        let mut data = Vec::<&[u64]>::new();
        for _ in 0..4 {
            data.push(&set);
        }

        let mut counter = 0;
        let timer = Instant::now();

        cartesian_product(&data, |product| {
            // println!("{:?}", product);
            counter += 1;
        });

        println!("Total {} product done in {:?}", counter, timer.elapsed());
    }

    #[allow(unused)]
    #[test]
    fn test_self_cartesian_product() {
        use std::time::Instant;
        let data : &[i32] = &[1, 2, 3];
        let n = 3;

        let mut counter = 0;
        let timer = Instant::now();

        self_cartesian_product(&data, 3, |product| {
            println!("{:?}", product);
            counter += 1;
        });

        println!("Total {} product done in {:?}", counter, timer.elapsed());
    }

    #[allow(unused)]
    #[should_panic]
    #[test]
    fn test_self_cartesian_product_zero() {
        use std::time::Instant;
        let data : &[i32] = &[1, 2, 3];
        let n = 0;

        let mut counter = 0;
        let timer = Instant::now();

        self_cartesian_product(&data, n, |product| {
            println!("{:?}", product);
            counter += 1;
        });

        println!("Total {} product done in {:?}", counter, timer.elapsed());
    }

    #[test]
    fn test_combination_trait() {
        let data = [1, 2, 3, 4, 5, 6, 7, 8];
        let k = 4;
        let mut counter = 0;
        for combination in data.combination(k) {
            println!("{:?}", combination);
            counter += 1;
        }

        assert_eq!(counter, divide_factorial(data.len(), data.len() - k) / factorial(k) ); // n!/(k!(n-k!))
    }

    #[test]
    fn test_combination_trait_share() {
        let data : &[i32] = &[1, 2, 3, 4, 5, 6, 7, 8];
        let k = 3;
        let mut result = vec![&data[0]; k];
        let shared = Rc::new(RefCell::new(result.as_mut_slice()));
        let combination_op = (data, shared);
        let mut counter = 0;
        for combination in combination_op.combination(k) {
            println!("{:?}", combination);
            counter += 1;
        }

        assert_eq!(counter, divide_factorial(data.len(), data.len() - k) / factorial(k) ); // n!/(k!(n-k!))
    }

    #[test]
    fn test_combination_trait_ptr() {
        let data : &[i32] = &[1, 2, 3, 4, 5, 6];
        let k = 4;
        let mut result = vec![&data[0]; k];
        let shared = result.as_mut_slice() as *mut [&i32];
        let combination_op = (data, shared);
        let mut counter = 0;
        unsafe {
            for _ in combination_op.combination(k) {
                println!("{:?}", &*shared);
                counter += 1;
            }
        }

        assert_eq!(counter, divide_factorial(data.len(), data.len() - k) / factorial(k) ); // n!/(k!(n-k!))
    }

    #[test]
    fn test_large_combination_fn_k_1() {
        let data : &[i32] = &[1, 2, 3, 4, 5, 6];
        let k = 1;
        let mut counter = 0;
        large_combination(data, k, |_result| {
            counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - k) / factorial(k) ); // n!/(k!(n-k!))
    }

    #[should_panic]
    #[test]
    fn test_large_combination_fn_k_0() {
        let data : &[i32] = &[1, 2, 3, 4, 5, 6];
        let k = 0;
        let mut counter = 0;
        large_combination(data, k, |_result| {
            counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - k) / factorial(k) ); // n!/(k!(n-k!))
    }

    #[test]
    fn test_large_combination_fn_d_eq_k() {
        let data : &[i32] = &[1, 2, 3];
        let k = 3;
        let mut counter = 0;
        large_combination(data, k, |_result| {
            // println!("{:?}", _result);
            counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - k) / factorial(k) ); // n!/(k!(n-k!))
    }

    #[test]
    fn test_large_combination_fn() {
        let data : &[i32] = &[1, 2, 3, 4, 5];
        let k = 3;
        let mut counter = 0;
        large_combination(data, k, |_result| {
            // println!("{:?}", _result);
            counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - k) / factorial(k) ); // n!/(k!(n-k!))
    }

    #[test]
    fn test_permutation_trait() {
        let mut data = [1, 2, 3, 4, 5];
        println!("{:?}", data);
        let mut counter = 1;
        for permuted in data.permutation() {
            println!("{:?}", permuted);
            counter += 1;
        }

        assert_eq!(counter, factorial(data.len()));
    }

    #[test]
    fn test_permutation_trait_cell() {
        let data : &mut[i32] = &mut [1, 2, 3, 4, 5];
        let mut shared = Rc::new(RefCell::new(data));
        let value = Rc::clone(&shared);
        println!("{:?}", &*shared.borrow());
        let mut counter = 1;
        shared.permutation().for_each(|_| {
            println!("{:?}", &*value.borrow());
            counter += 1;
        });

        assert_eq!(counter, factorial(value.borrow().len()));
    }

    #[test]
    fn test_permutation_trait_ref() {
        let data : &mut[i32] = &mut [1, 2, 3, 4, 5];
        let mut shared = data as *mut [i32];
        let mut counter = 1;
        shared.permutation().for_each(|_| {
            println!("{:?}", data);
            counter += 1;
        });

        assert_eq!(counter, factorial(data.len()));
    }

    #[test]
    fn test_k_permutation_primitive() {
        let data = [1, 2, 3, 4, 5];
        let k = 3;
        let mut counter = 0;

        data.combination(k).for_each(|mut combination| {
            println!("{:?}", combination);
            counter += 1;
            combination.permutation().for_each(|permuted| {
                println!("{:?}", permuted);
                counter += 1;
            });
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - k));
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_KPermutation_trait() {
        let data : &mut[i32] = &mut [1, 2, 3, 4, 5];
        let mut counter = 0;
        (&*data, 3usize).permutation().for_each(|_p| {
            // println!("{:?}", p);
            counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - 3));
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_KPermutation_single() {
        let data : &mut[i32] = &mut [1, 2, 3, 4, 5];
        let mut counter = 0;
        let k = 1usize;
        (&*data, k).permutation().for_each(|_p| {
            println!("{:?}", _p);
            counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - k));
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_KPermutation_into_cell_trait() {
        use std::time::Instant;

        let data : &mut[i32] = &mut [1, 2, 3, 4, 5, 6];
        let mut counter = 0;
        let k = 2;
        let mut result : Vec<&i32> = vec![&data[0]; k];
        let shared = Rc::new(RefCell::new(result.as_mut_slice()));
        let timer = Instant::now();
        (&*data, k, Rc::clone(&shared)).permutation().for_each(|_| {
            // println!("{:?}", &*shared.borrow());
            counter += 1;
        });

        println!("Total {} combination done in {:?}", counter, timer.elapsed());
        assert_eq!(counter, divide_factorial(data.len(), data.len() - k));
    }

    #[allow(non_snake_case, unused_unsafe)]
    #[test]
    fn test_KPermutation_into_Ref_trait() {
        use std::time::Instant;

        let data : &[i32] = &[1, 2, 3, 4, 5];
        let mut counter = 0;
        let k = 3;
        let mut result : Vec<&i32> = vec![&data[0]; k];
        let shared = result.as_mut_slice() as *mut [&i32];
        let timer = Instant::now();
        unsafe {
            (data, k, shared).permutation().for_each(|_| {
                // println!("{:?}", &*shared);
                counter += 1;
            });

            println!("Total {} combination done in {:?}", counter, timer.elapsed());
            assert_eq!(counter, divide_factorial(data.len(), data.len() - k));
        }
    }

    // #[test]
    // fn test_lexicographic_combination() {
    //     let mut x = 7;

    //     for _ in 0..40 {
    //         println!("{:0>8b}", x);
    //         stanford_combination(&mut x);
    //     }
    // }

    #[test]
    fn test_combination_fn() {
        let data = [1, 2, 3, 4, 5];
        let r = 3;
        let mut counter = 0;

        combination(&data, r, |comb| {
            println!("{:?}", comb);
            counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - r) / factorial(r));
    }

    #[test]
    fn test_combination_fn_single() {
        let data = [1];
        let r = 1;
        let mut counter = 0;

        combination(&data, r, |comb| {
            println!("{:?}", comb);
            counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - r) / factorial(r));
    }

    #[test]
    fn test_combination_fn_bound() {
        let data = [1, 2, 3];
        let r = 3;
        let mut counter = 0;

        combination(&data, r, |comb| {
            println!("{:?}", comb);
            counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - r) / factorial(r));
    }

    #[test]
    fn test_large_combination_cell_fn() {
        let data : &mut [i32] = &mut [1, 2, 3, 4, 5];
        let r = 3;
        let mut counter = 0;
        let mut result : Vec<&i32> = vec![&data[0]; r];
        let shared : Rc<RefCell<&mut [&i32]>> = Rc::new(RefCell::new(&mut result));

        large_combination_cell(&data, r, Rc::clone(&shared), || {
            println!("{:?}", shared.borrow());
            counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - r) / factorial(r));
    }

    #[test]
    fn test_large_combination_sync_fn() {
        let data : &mut [i32] = &mut [1, 2, 3, 4, 5];
        let r = 3;
        let mut counter = 0;
        let result : Vec<&i32> = vec![&data[0]; r];
        let shared : Arc<RwLock<Vec<&i32>>> = Arc::new(RwLock::new(result));

        large_combination_sync(&data, r, Arc::clone(&shared), || {
            println!("{:?}", shared.read().unwrap());
            counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - r) / factorial(r));
    }

    #[test]
    fn test_unsafe_combination_fn() {
        let data = [1, 2, 3, 4, 5];
        let r = 3;
        let mut counter = 0;
        let mut result = vec![&data[0]; r];
        let result_ptr = result.as_mut_slice() as *mut [&usize];

        unsafe {
            unsafe_combination(&data, r, result_ptr, || {
                println!("{:?}", result);
                counter += 1;
            });
        }

        assert_eq!(counter, divide_factorial(data.len(), data.len() - r) / factorial(r));
    }

    #[test]
    fn test_combination_cell_fn() {
        let data = [1, 2, 3, 4, 5];
        let r = 3;
        let mut counter = 0;
        let mut result = vec![&data[0]; r];
        let result_cell = Rc::new(RefCell::new(result.as_mut_slice()));

        combination_cell(&data, r, Rc::clone(&result_cell), || {
                println!("{:?}", result_cell.borrow());
                counter += 1;
        });

        assert_eq!(counter, divide_factorial(data.len(), data.len() - r) / factorial(r));
    }

    #[test]
    fn test_unsafe_shared_combination_result_fn() {
        use std::fmt::Debug;

        trait Consumer {
            fn consume(&self);
        }
        struct Worker1<'a, T : 'a> {
            data : &'a[&'a T]
        }
        impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
            fn consume(&self) {
                // println!("Work1 has {:?}", self.data);
                self.data.iter().for_each(|_| {});
            }
        }
        struct Worker2<'a, T : 'a> {
            data : &'a[&'a T]
        }
        impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
            fn consume(&self) {
                // println!("Work2 has {:?}", self.data);
                self.data.iter().for_each(|_| {});
            }
        }

        unsafe fn start_combination_process<'a>(data : &'a[i32], cur_result : *mut [&'a i32], k : usize, consumers : Vec<Box<Consumer + 'a>>) {
            use std::time::Instant;
            let timer = Instant::now();
            let mut counter = 0;
            unsafe_combination(data, k, cur_result, || {
                consumers.iter().for_each(|c| {
                    c.consume();
                });
                counter += 1;
            });
            println!("Done {} combinations with 2 workers in {:?}", counter, timer.elapsed());
        }
        let k = 5;
        let data = &[1, 2, 3, 4, 5, 6];
        let mut result = vec![&data[0]; k];

        unsafe {

            let shared = result.as_mut_slice() as *mut [&i32];
            let worker1 = Worker1 {
                data : &result
            };
            let worker2 = Worker2 {
                data : &result
            };
            let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
            start_combination_process(data, shared, k, consumers);
        }
    }

    #[test]
    fn test_shared_combination_result_fn() {
        use std::fmt::Debug;

        trait Consumer {
            fn consume(&self);
        }
        struct Worker1<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
            fn consume(&self) {
                // println!("Work1 has {:?}", self.data.borrow());
                let result = self.data.borrow();
                result.iter().for_each(|_| {});
            }
        }
        struct Worker2<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
            fn consume(&self) {
                // println!("Work2 has {:?}", self.data.borrow());
                let result = self.data.borrow();
                result.iter().for_each(|_| {});
            }
        }

        fn start_combination_process<'a>(data : &'a[i32], cur_result : Rc<RefCell<&'a mut[&'a i32]>>, k : usize, consumers : Vec<Box<Consumer + 'a>>) {
            use std::time::Instant;
            let timer = Instant::now();
            let mut counter = 0;
            combination_cell(data, k, cur_result, || {
                consumers.iter().for_each(|c| {
                    c.consume();
                });
                counter += 1;
            });
            println!("Done {} combinations with 2 workers in {:?}", counter, timer.elapsed());
        }
        let k = 4;
        let data = &[1, 2, 3, 4, 5, 6, 7];
        let mut result = vec![&data[0]; k];
        let result_cell = Rc::new(RefCell::new(result.as_mut_slice()));

        let worker1 = Worker1 {
            data : Rc::clone(&result_cell)
        };
        let worker2 = Worker2 {
            data : Rc::clone(&result_cell)
        };
        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
        start_combination_process(data, result_cell, k, consumers);
    }

    #[test]
    fn test_shared_combination_result_sync_fn() {
        fn start_combination_process<'a>(data : &'a[i32], cur_result : Arc<RwLock<Vec<&'a i32>>>, k : usize, notifier : Vec<SyncSender<Option<()>>>, release_recv : Receiver<()>) {
            use std::time::Instant;
            let timer = Instant::now();
            let mut counter = 0;
            combination_sync(data, k, cur_result, || {
                notifier.iter().for_each(|n| {
                    n.send(Some(())).unwrap(); // notify every thread that new data available
                });

                for _ in 0..notifier.len() {
                    release_recv.recv().unwrap(); // block until all thread reading data notify on read completion
                }

                counter += 1;
            });

            notifier.iter().for_each(|n| {n.send(None).unwrap()}); // notify every thread that there'll be no more data.

            println!("Done {} combinations with 2 workers in {:?}", counter, timer.elapsed());
        }
        let k = 4;
        let data = &[1, 2, 3, 4, 5, 6];
        let result = vec![&data[0]; k];
        let result_sync = Arc::new(RwLock::new(result));

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
        let (main_send, main_recv) = mpsc::sync_channel(0);
        let t1_local = main_send.clone();
        let t1_dat = Arc::clone(&result_sync);
        thread::spawn(move || {
            while let Some(_) = t1_recv.recv().unwrap() {
                let _result : &Vec<&i32> = &*t1_dat.read().unwrap();
                // println!("Thread1: {:?}", _result);
                t1_local.send(()).unwrap(); // notify generator thread that reference is no longer neeed.
            }
            println!("Thread1 is done");
        });

        // worker thread 2
        let (t2_send, t2_recv) = mpsc::sync_channel::<Option<()>>(0);
        let t2_dat = Arc::clone(&result_sync);
        let t2_local = main_send.clone();
        thread::spawn(move || {
            while let Some(_) = t2_recv.recv().unwrap() {
                let _result : &Vec<&i32> = &*t2_dat.read().unwrap();
                // println!("Thread2: {:?}", _result);
                t2_local.send(()).unwrap(); // notify generator thread that reference is no longer neeed.
            }
            println!("Thread2 is done");
        });

        // main thread that generate result
        thread::spawn(move || {
            start_combination_process(data, result_sync, k, vec![t1_send, t2_send], main_recv);
        }).join().unwrap();
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_share_result_CombinationIterator_with_thread_fn() {
        let k = 3;
        let data : &[i32] = &[1, 2, 3, 4, 5];

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<Vec<&i32>>>(0);

        thread::spawn(move || {
            while let Some(c) = t1_recv.recv().unwrap() {
                let _result : Vec<&i32> = c;
                // println!("Thread1: {:?}", _result);
            }
            println!("Thread1 is done");
        });

        // worker thread 2
        let (t2_send, t2_recv) = mpsc::sync_channel::<Option<Vec<&i32>>>(0);
        thread::spawn(move || {
            while let Some(c) = t2_recv.recv().unwrap() {
                let _result : Vec<&i32> = c;
                // println!("Thread2: {:?}", _result);
            }
            println!("Thread2 is done");
        });

        let channels = vec![t1_send, t2_send];
        // main thread that generate result
        thread::spawn(move || {
            use std::time::Instant;
            let timer = Instant::now();
            let mut counter = 0;
            
            data.combination(k).for_each(|c| {
                channels.iter().for_each(|t| {t.send(Some(c.to_owned())).unwrap();});
                counter += 1;
            });
            channels.iter().for_each(|t| {t.send(None).unwrap()});
            println!("Done {} combinations in {:?}", counter, timer.elapsed());
        }).join().unwrap();
    }

    #[test]
    fn test_shared_combination_result_iterator_alike() {
        use std::fmt::Debug;
        use std::time::Instant;

        trait Consumer {
            fn consume(&self);
        }
        struct Worker1<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
            fn consume(&self) {
                // println!("Work1 has {:?}", self.data.borrow());
                let result = self.data.borrow();
                result.iter().for_each(|_| {});
            }
        }
        struct Worker2<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
            fn consume(&self) {
                // println!("Work2 has {:?}", self.data.borrow());
                let result = self.data.borrow();
                result.iter().for_each(|_| {});
            }
        }
        let k = 4;
        let data = &[1, 2, 3, 4, 5, 6, 7];
        let mut result = vec![&data[0]; k];
        let result_cell = Rc::new(RefCell::new(result.as_mut_slice()));

        let worker1 = Worker1 {
            data : Rc::clone(&result_cell)
        };
        let worker2 = Worker2 {
            data : Rc::clone(&result_cell)
        };
        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
        let gosper = GosperCombinationCellIter::new(data, k, result_cell);
        let timer = Instant::now();
        let mut counter = 0;

        for _ in gosper {
            consumers.iter().for_each(|c| {c.consume()});
            counter += 1;
        }

        println!("Total {} combinations done in {:?}", counter, timer.elapsed());
    }

    #[test]
    fn test_unsafe_cartesian_product_shared_result() {
        use std::fmt::Debug;

        trait Consumer {
            fn consume(&self);
        }
        struct Worker1<'a, T : 'a> {
            data : &'a[&'a T]
        }
        impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
            fn consume(&self) {
                println!("Work1 has {:?}", self.data);
            }
        }
        struct Worker2<'a, T : 'a> {
            data : &'a[&'a T]
        }
        impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
            fn consume(&self) {
                println!("Work2 has {:?}", self.data);
            }
        }

        unsafe fn start_cartesian_product_process<'a>(data : &'a[&'a[i32]], cur_result : *mut [&'a i32], consumers : Vec<Box<Consumer + 'a>>) {
            unsafe_cartesian_product(data, cur_result, || {
                consumers.iter().for_each(|c| {
                    c.consume();
                })
            });
        }

        let data : &[&[i32]] = &[&[1, 2], &[3, 4, 5], &[6]];
        let mut result = vec![&data[0][0]; data.len()];

        unsafe {

            let shared = result.as_mut_slice() as *mut [&i32];
            let worker1 = Worker1 {
                data : &result
            };
            let worker2 = Worker2 {
                data : &result
            };
            let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
            start_cartesian_product_process(data, shared, consumers);
        }
    }

    #[allow(unused)]
    #[test]
    fn test_unsafe_self_cartesian_product_shared_result() {
        use std::fmt::Debug;

        trait Consumer {
            fn consume(&self);
        }
        struct Worker1<'a, T : 'a> {
            data : &'a[&'a T]
        }
        impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
            fn consume(&self) {
                // println!("Work1 has {:?}", self.data);
            }
        }
        struct Worker2<'a, T : 'a> {
            data : &'a[&'a T]
        }
        impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
            fn consume(&self) {
                // println!("Work2 has {:?}", self.data);
            }
        }

        unsafe fn start_cartesian_product_process<'a>(data : &'a[i32], n : usize, cur_result : *mut [&'a i32], consumers : Vec<Box<Consumer + 'a>>) {
            use std::time::Instant;
            let timer = Instant::now();
            let mut counter = 0;
            unsafe_self_cartesian_product(data, n, cur_result, || {
                consumers.iter().for_each(|c| {
                    c.consume();
                });
                counter += 1;
            });

            println!("start_cartesian_product_process: {} products in {:?}", counter, timer.elapsed());
        }

        let data : &[i32] = &[1, 2, 3];
        let n = 3;
        let mut result = vec![&data[0]; n];

        unsafe {

            let shared = result.as_mut_slice() as *mut [&i32];
            let worker1 = Worker1 {
                data : &result
            };
            let worker2 = Worker2 {
                data : &result
            };
            let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
            start_cartesian_product_process(data, n, shared, consumers);
        }
    }

    #[test]
    fn test_cartesian_product_shared_result_fn() {
        use std::fmt::Debug;

        trait Consumer {
            fn consume(&self);
        }
        struct Worker1<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
            fn consume(&self) {
                println!("Work1 has {:?}", self.data);
            }
        }
        struct Worker2<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
            fn consume(&self) {
                println!("Work2 has {:?}", self.data);
            }
        }

        fn start_cartesian_product_process<'a>(data : &'a[&'a[i32]], cur_result : Rc<RefCell<&'a mut [&'a i32]>>, consumers : Vec<Box<Consumer + 'a>>) {
            cartesian_product_cell(data, cur_result, || {
                consumers.iter().for_each(|c| {
                    c.consume();
                })
            });
        }

        let data : &[&[i32]] = &[&[1, 2], &[3, 4, 5], &[6]];
        let mut result = vec![&data[0][0]; data.len()];

        let shared = Rc::new(RefCell::new(result.as_mut_slice()));
        let worker1 = Worker1 {
            data : Rc::clone(&shared)
        };
        let worker2 = Worker2 {
            data : Rc::clone(&shared)
        };
        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
        start_cartesian_product_process(data, shared, consumers);
    }
    
    #[allow(unused)]
    #[test]
    fn test_self_cartesian_product_shared_result_fn() {
        use std::fmt::Debug;

        trait Consumer {
            fn consume(&self);
        }
        struct Worker1<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
            fn consume(&self) {
                println!("Work1 has {:?}", self.data);
            }
        }
        struct Worker2<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
            fn consume(&self) {
                println!("Work2 has {:?}", self.data);
            }
        }

        fn start_cartesian_product_process<'a>(data : &'a[i32], n : usize, cur_result : Rc<RefCell<&'a mut [&'a i32]>>, consumers : Vec<Box<Consumer + 'a>>) {
            self_cartesian_product_cell(data, n, cur_result, || {
                consumers.iter().for_each(|c| {
                    c.consume();
                })
            });
        }

        let data : &[i32] = &[1, 2, 3];
        let n = 3;
        let mut result = vec![&data[0]; n];

        let shared = Rc::new(RefCell::new(result.as_mut_slice()));
        let worker1 = Worker1 {
            data : Rc::clone(&shared)
        };
        let worker2 = Worker2 {
            data : Rc::clone(&shared)
        };
        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
        start_cartesian_product_process(data, n, shared, consumers);
    
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_CartesianProduct_iterator_alike_shared_result() {
        use std::fmt::Debug;

        trait Consumer {
            fn consume(&self);
        }
        struct Worker1<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
            fn consume(&self) {
                println!("Work1 has {:?}", self.data);
            }
        }
        struct Worker2<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
            fn consume(&self) {
                println!("Work2 has {:?}", self.data);
            }
        }

        fn start_cartesian_product_process<'a>(data : &'a[&'a[i32]], cur_result : Rc<RefCell<&'a mut [&'a i32]>>, consumers : Vec<Box<Consumer + 'a>>) {
            let cart = CartesianProductCellIter::new(data, cur_result);
            for _ in cart {
                consumers.iter().for_each(|c| {
                    c.consume();
                })
            };
        }

        let data : &[&[i32]] = &[&[1, 2], &[3, 4, 5], &[6]];
        let mut result = vec![&data[0][0]; data.len()];

        let shared = Rc::new(RefCell::new(result.as_mut_slice()));
        let worker1 = Worker1 {
            data : Rc::clone(&shared)
        };
        let worker2 = Worker2 {
            data : Rc::clone(&shared)
        };
        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
        start_cartesian_product_process(data, shared, consumers);
    
    }
    #[test]
    fn test_shared_cartesian_product_result_sync_fn() {
        fn start_cartesian_product_process<'a>(data : &'a[&[i32]], cur_result : Arc<RwLock<Vec<&'a i32>>>, notifier : Vec<SyncSender<Option<()>>>, release_recv : Receiver<()>) {
            use std::time::Instant;
            let timer = Instant::now();
            let mut counter = 0;
            cartesian_product_sync(data, cur_result, || {
                notifier.iter().for_each(|n| {
                    n.send(Some(())).unwrap(); // notify every thread that new data available
                });

                for _ in 0..notifier.len() {
                    release_recv.recv().unwrap(); // block until all thread reading data notify on read completion
                }

                counter += 1;
            });

            notifier.iter().for_each(|n| {n.send(None).unwrap()}); // notify every thread that there'll be no more data.

            println!("Done {} combinations with 2 workers in {:?}", counter, timer.elapsed());
        }
        let k = 3;
        let data : &[&[i32]]= &[&[1, 2, 3], &[4, 5], &[6, 7, 8, 9, 10]];
        let result = vec![&data[0][0]; k];
        let result_sync = Arc::new(RwLock::new(result));

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
        let (main_send, main_recv) = mpsc::sync_channel(0);
        let t1_local = main_send.clone();
        let t1_dat = Arc::clone(&result_sync);
        thread::spawn(move || {
            while let Some(_) = t1_recv.recv().unwrap() {
                let _result : &Vec<&i32> = &*t1_dat.read().unwrap();
                // println!("Thread1: {:?}", _result);
                t1_local.send(()).unwrap(); // notify generator thread that reference is no longer neeed.
            }
            println!("Thread1 is done");
        });

        // worker thread 2
        let (t2_send, t2_recv) = mpsc::sync_channel::<Option<()>>(0);
        let t2_dat = Arc::clone(&result_sync);
        let t2_local = main_send.clone();
        thread::spawn(move || {
            while let Some(_) = t2_recv.recv().unwrap() {
                let _result : &Vec<&i32> = &*t2_dat.read().unwrap();
                // println!("Thread2: {:?}", _result);
                t2_local.send(()).unwrap(); // notify generator thread that reference is no longer neeed.
            }
            println!("Thread2 is done");
        });

        // main thread that generate result
        thread::spawn(move || {
            start_cartesian_product_process(data, result_sync, vec![t1_send, t2_send], main_recv);
        }).join().unwrap();
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_shared_CartesianProduct_result_sync() {
        let data : &[&[i32]]= &[&[1, 2, 3], &[4, 5], &[6, 7, 8, 9]];
        let result = vec![&data[0][0]; data.len()];
        let result_sync = Arc::new(RwLock::new(result));

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
        let t1_dat = Arc::clone(&result_sync);
        thread::spawn(move || {
            while let Some(_) = t1_recv.recv().unwrap() {
                let _result : &Vec<&i32> = &*t1_dat.read().unwrap();
                println!("Thread1: {:?}", _result);
            }
            println!("Thread1 is done");
        });

        // worker thread 2
        let (t2_send, t2_recv) = mpsc::sync_channel::<Option<()>>(0);
        let t2_dat = Arc::clone(&result_sync);
        thread::spawn(move || {
            while let Some(_) = t2_recv.recv().unwrap() {
                let _result : &Vec<&i32> = &*t2_dat.read().unwrap();
                println!("Thread2: {:?}", _result);
            }
            println!("Thread2 is done");
        });

        let consumers = vec![t1_send, t2_send];
        // main thread that generate result
        thread::spawn(move || {
            use std::time::Instant;
            let cart = CartesianProductIterator::new(data);
            let mut counter = 0;
            let timer = Instant::now();
            
            cart.into_iter().for_each(|_| {
                consumers.iter().for_each(|c| {
                    c.send(Some(())).unwrap();
                });
                counter += 1;
            });
            
            consumers.iter().for_each(|c| {
                c.send(None).unwrap(); // Explicitly terminate all workers
            });

            println!("Done {} products in {:?}", counter, timer.elapsed());
        }).join().unwrap();
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_share_CartesianProductIterator_result_to_thread() {
        let data : &[&[i32]]= &[&[1, 2, 3], &[4, 5], &[6, 7, 8, 9]];

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::channel::<Option<Vec<&i32>>>();
        thread::spawn(move || {
            while let Some(p) = t1_recv.recv().unwrap() {
                println!("Thread1: {:?}", p);
            }
            println!("Thread1 is done");
        });

        // worker thread 2
        let (t2_send, t2_recv) = mpsc::channel::<Option<Vec<&i32>>>();
        thread::spawn(move || {
            while let Some(p) = t2_recv.recv().unwrap() {
                println!("Thread2: {:?}", p);
            }
            println!("Thread2 is done");
        });

        let consumers = vec![t1_send, t2_send];
        // main thread that generate result
        thread::spawn(move || {
            use std::time::Instant;
            let cart = CartesianProductIterator::new(data);
            let mut counter = 0;
            let timer = Instant::now();
            
            cart.into_iter().for_each(|p| {
                println!("{:?}", p);
                consumers.iter().for_each(|c| {
                    c.send(Some(p.to_owned())).unwrap();
                });
                counter += 1;
            });
            
            consumers.iter().for_each(|c| {
                c.send(None).unwrap(); // Explicitly terminate all workers
            });

            println!("Main: Done {} products in {:?}", counter, timer.elapsed());
        }).join().unwrap();
    }

    #[test]
    fn test_unsafe_shared_k_permutation_result_fn() {
        use std::fmt::Debug;

        trait Consumer {
            fn consume(&self);
        }
        struct Worker1<'a, T : 'a> {
            data : &'a[&'a T]
        }
        impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
            fn consume(&self) {
                println!("Work1 has {:?}", self.data);
            }
        }
        struct Worker2<'a, T : 'a> {
            data : &'a[&'a T]
        }
        impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
            fn consume(&self) {
                println!("Work2 has {:?}", self.data);
            }
        }

        unsafe fn start_k_permutation_process<'a>(data : &'a[i32], cur_result : *mut [&'a i32], k : usize, consumers : Vec<Box<Consumer + 'a>>) {
            unsafe_k_permutation(data, k, cur_result, || {
                consumers.iter().for_each(|c| {
                    c.consume();
                })
            });
        }
        let k = 3;
        let data = &[1, 2, 3, 4, 5];
        let mut result = vec![&data[0]; k];

        unsafe {

            let shared = result.as_mut_slice() as *mut [&i32];
            let worker1 = Worker1 {
                data : &result
            };
            let worker2 = Worker2 {
                data : &result
            };
            let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
            start_k_permutation_process(data, shared, k, consumers);
        }
    }

    #[test]
    fn test_shared_k_permutation_result_fn() {
        use std::fmt::Debug;

        trait Consumer {
            fn consume(&self);
        }
        struct Worker1<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
            fn consume(&self) {
                println!("Work1 has {:?}", self.data.borrow());
            }
        }
        struct Worker2<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
            fn consume(&self) {
                println!("Work2 has {:?}", self.data.borrow());
            }
        }

        fn start_k_permutation_process<'a>(data : &'a[i32], cur_result : Rc<RefCell<&'a mut [&'a i32]>>, k : usize, consumers : Vec<Box<Consumer + 'a>>) {
            use std::time::Instant;
            let timer = Instant::now();
            let mut counter = 0;
            k_permutation_cell(data, k, cur_result, || {
                consumers.iter().for_each(|c| {
                    c.consume();
                });
                counter += 1;
            });
            
            println!("Total {} permutation done in {:?}", counter, timer.elapsed());
        }
        let k = 3;
        let data = &[1, 2, 3, 4, 5];
        let mut result = vec![&data[0]; k];
        let shared = Rc::new(RefCell::new(result.as_mut_slice()));

        let worker1 = Worker1 {
            data : Rc::clone(&shared)
        };
        let worker2 = Worker2 {
            data : Rc::clone(&shared)
        };
        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
        start_k_permutation_process(data, shared, k, consumers);
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_shared_KPermutation_result() {
        use std::time::Instant;
        use std::fmt::Debug;

        trait Consumer {
            fn consume(&self);
        }
        struct Worker1<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker1<'a, T> {
            fn consume(&self) {
                println!("Work1 has {:?}", self.data.borrow());
            }
        }
        struct Worker2<'a, T : 'a> {
            data : Rc<RefCell<&'a mut[&'a T]>>
        }
        impl<'a, T : 'a + Debug> Consumer for Worker2<'a, T> {
            fn consume(&self) {
                println!("Work2 has {:?}", self.data.borrow());
            }
        }

        let k = 3;
        let data = &[1, 2, 3, 4, 5];
        let mut result = vec![&data[0]; k];
        let shared = Rc::new(RefCell::new(result.as_mut_slice()));

        let worker1 = Worker1 {
            data : Rc::clone(&shared)
        };
        let worker2 = Worker2 {
            data : Rc::clone(&shared)
        };
        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
        
        let kperm = KPermutationCellIter::new(data, k, shared);
        let timer = Instant::now();
        let mut counter = 0;
        for _ in kperm {
            consumers.iter().for_each(|c| {c.consume();});
            counter += 1;
        }

        println!("Total {} permutation done in {:?}", counter, timer.elapsed());
        assert_eq!(counter, divide_factorial(data.len(), data.len() - k));
    }

    #[test]
    fn test_shared_k_permutation_sync_fn() {
        fn start_k_permutation_process<'a>(data : &'a[i32], cur_result : Arc<RwLock<Vec<&'a i32>>>, k : usize, notifier : Vec<SyncSender<Option<()>>>, release_recv : Receiver<()>) {
            use std::time::Instant;
            let timer = Instant::now();
            let mut counter = 0;
            k_permutation_sync(data, k, cur_result, || {
                notifier.iter().for_each(|n| {
                    n.send(Some(())).unwrap(); // notify every thread that new data available
                });

                for _ in 0..notifier.len() {
                    release_recv.recv().unwrap(); // block until all thread reading data notify on read completion
                }

                counter += 1;
            });

            notifier.iter().for_each(|n| {n.send(None).unwrap()}); // notify every thread that there'll be no more data.

            println!("Done {} combinations with 2 workers in {:?}", counter, timer.elapsed());
        }
        let k = 4;
        let data = &[1, 2, 3, 4, 5, 6];
        let result = vec![&data[0]; k];
        let result_sync = Arc::new(RwLock::new(result));

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
        let (main_send, main_recv) = mpsc::sync_channel(0);
        let t1_local = main_send.clone();
        let t1_dat = Arc::clone(&result_sync);
        thread::spawn(move || {
            while let Some(_) = t1_recv.recv().unwrap() {
                let _result : &Vec<&i32> = &*t1_dat.read().unwrap();
                // println!("Thread1: {:?}", _result);
                t1_local.send(()).unwrap(); // notify generator thread that reference is no longer neeed.
            }
            println!("Thread1 is done");
        });

        // worker thread 2
        let (t2_send, t2_recv) = mpsc::sync_channel::<Option<()>>(0);
        let t2_dat = Arc::clone(&result_sync);
        let t2_local = main_send.clone();
        thread::spawn(move || {
            while let Some(_) = t2_recv.recv().unwrap() {
                let _result : &Vec<&i32> = &*t2_dat.read().unwrap();
                // println!("Thread2: {:?}", _result);
                t2_local.send(()).unwrap(); // notify generator thread that reference is no longer neeed.
            }
            println!("Thread2 is done");
        });

        // main thread that generate result
        thread::spawn(move || {
            start_k_permutation_process(data, result_sync, k, vec![t1_send, t2_send], main_recv);
        }).join().unwrap();
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_share_result_KPermutation_iterator_sync() {
        let k = 3;
        let data : &[i32] = &[1, 2, 3, 4, 5];

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<Vec<&i32>>>(0);

        thread::spawn(move || {
            while let Some(c) = t1_recv.recv().unwrap() {
                let _result : Vec<&i32> = c;
                println!("Thread1: {:?}", _result);
            }
            println!("Thread1 is done");
        });

        // worker thread 2
        let (t2_send, t2_recv) = mpsc::sync_channel::<Option<Vec<&i32>>>(0);
        thread::spawn(move || {
            while let Some(c) = t2_recv.recv().unwrap() {
                let _result : Vec<&i32> = c;
                println!("Thread2: {:?}", _result);
            }
            println!("Thread2 is done");
        });

        let channels = vec![t1_send, t2_send];
        // main thread that generate result
        thread::spawn(move || {
            use std::time::Instant;
            let timer = Instant::now();
            let mut counter = 0;
            let kperm = KPermutationIterator::new(data, k);
            
            kperm.into_iter().for_each(|c| {
                channels.iter().for_each(|t| {t.send(Some(c.to_owned())).unwrap();});
                counter += 1;
            });
            channels.iter().for_each(|t| {t.send(None).unwrap()});
            println!("Done {} combinations in {:?}", counter, timer.elapsed());
            assert_eq!(counter, divide_factorial(data.len(), data.len() - k));
        }).join().unwrap();
    }

    #[test]
    fn test_unsafe_cartesian_product() {
        use std::time::Instant;
        let set = (1..4).map(|item| item).collect::<Vec<u64>>();
        let mut data = Vec::<&[u64]>::new();
        for _ in 0..3 {
            data.push(&set);
        }

        let mut counter = 0;
        let mut result = vec![&data[0][0]; data.len()];
        let result_ptr = result.as_mut_slice() as *mut [&u64];
        let timer = Instant::now();

        unsafe {
            unsafe_cartesian_product(&data, result_ptr, || {
                // println!("{:?}", product);
                counter += 1;
            });
        }

        println!("Total {} product done in {:?}", counter, timer.elapsed());
    }

    #[allow(unused)]
    #[test]
    fn test_unsafe_k_permutation() {
        use std::time::{Instant};
        let data = [1, 2, 3, 4, 5];
        let k = 3;
        let mut counter = 0;
        let mut result = vec![&data[0]; k];
        let timer = Instant::now();
        unsafe {
            unsafe_k_permutation(&data, k, result.as_mut_slice() as *mut [&usize], || {
                // uncomment line below to print all k-permutation
                // println!("{}:{:?}", counter, result);
                counter += 1;
            });
        }

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
        assert_eq!(divide_factorial(data.len(), data.len() - k), counter);
    }

    #[test]
    fn test_tldr_case() {
        let domains : &[&[i32]] = &[&[1, 2], &[3, 4, 5], &[6], &[7, 8], &[9, 10, 11]];
        domains.cart_prod().for_each(|cp| {
            // each cp will be &[&i32] with length equals to domains.len() which in this case 5

            // It's k-permutation of size 3 over data.
            cp.combination(3).for_each(|mut c| { // need mut
                // print the first 3-combination over data
                println!("{:?}", c);

                // start permute the 3-combination
                c.permutation().for_each(|p| {
                    // print each permutation of the 3-combination.
                    println!("{:?}", p);
                });

                // It'll print the last 3-permutation again because permutation permute the value in place.
                println!("{:?}", c);
            })
        });
    }

    #[test]
    fn test_x_permutation() {
        let data = vec![1, 2, 3, 4];
        let mut counter = 0;

        x_permutation(&data, |_| true, |p| {
            println!("{:?}", p);
            counter += 1;
        });

        assert_eq!(factorial(data.len()), counter);
    }

    #[test]
    fn test_x_permutation_cell() {
        let data = vec![1, 2, 3, 4];
        let mut result = vec![&data[0]; data.len()];
        let share = Rc::new(RefCell::new(result.as_mut_slice()));
        let mut counter = 0;

        x_permutation_cell(&data, Rc::clone(&share), |_| true, || {
            println!("{:?}", &*share.borrow());
            counter += 1;
        });

        assert_eq!(factorial(data.len()), counter);
    }

    #[test]
    fn test_x_permutation_sync() {
        let data = vec![1, 2, 3, 4];
        let result = vec![&data[0]; data.len()];
        let share = Arc::new(RwLock::new(result));
        let mut counter = 0;

        x_permutation_sync(&data, Arc::clone(&share), |_| true, || {
            println!("{:?}", &*share.read().unwrap());
            counter += 1;
        });

        assert_eq!(factorial(data.len()), counter);
    }

    #[test]
    fn test_unsafe_x_permutation() {
        let data = vec![1u8, 2, 3, 4];
        let mut result = vec![&data[0]; data.len()];
        let share = result.as_mut_slice() as *mut [&u8];
        let mut counter = 0;

        unsafe {
            unsafe_x_permutation(&data, share, |_| true, || {
                println!("{:?}", result);
                counter += 1;
            });
        }

        assert_eq!(factorial(data.len()), counter);
    }

    #[test]
    fn test_x_permutation_restricted() {
        let data : Vec<u8> = vec![1, 2, 3, 4];
        let mut counter = 0;

        x_permutation(&data, |f| {
            *f[0] != 1u8 // filter all permutation that start with 1
        }, |p| {
            println!("{:?}", p);
            counter += 1;
        });

        assert_eq!(factorial(data.len()) - factorial(data.len() - 1), counter);
    }

    #[test]
    #[ignore]
    fn compare_gosper_custom_fn() {
        use std::time::Instant;
        let data : Vec<i32> = (0..30i32).map(|i| {i}).collect();
        let r = 20;
        let mut counter = 0;
        let timer = Instant::now();
        combination(&data, r, |_c| {counter += 1});
        println!("Stanford comb {} combination done in {:?}", counter, timer.elapsed());
        counter = 0;
        let timer = Instant::now();
        large_combination(&data, r, |_c| {counter += 1});
        println!("Custom comb {} combination done in {:?}", counter, timer.elapsed());
    }

    #[test]
    #[ignore]
    fn compare_gosper_custom_iter() {
        use std::time::Instant;
        let data : Vec<i32> = (0..30i32).map(|i| {i}).collect();
        let r = 20;
        let mut counter = 0;
        let timer = Instant::now();
        let stanford = GosperCombinationIterator::new(&data, r);
        stanford.into_iter().for_each(|_c| {counter += 1});
        println!("Stanford comb {} combination done in {:?}", counter, timer.elapsed());
        counter = 0;
        let timer = Instant::now();
        let mut lc = LargeCombinationIterator::new(&data, r);
        lc.iter().for_each(|_c| {counter += 1});
        println!("Custom comb {} combination done in {:?}", counter, timer.elapsed());
    }

    #[test]
    #[ignore]
    fn compare_gosper_custom_cell_iter() {
        use std::time::Instant;
        let data : Vec<i32> = (0..30i32).map(|i| {i}).collect();
        let r = 20;
        let mut result = vec![&data[0]; r];
        let share : Rc<RefCell<&mut[&i32]>> = Rc::new(RefCell::new(&mut result));
        let mut counter = 0;
        let timer = Instant::now();
        let stanford = GosperCombinationCellIter::new(&data, r, Rc::clone(&share));
        stanford.into_iter().for_each(|_c| {counter += 1});
        println!("Stanford comb {} combination done in {:?}", counter, timer.elapsed());
        counter = 0;
        let timer = Instant::now();
        let mut lc = LargeCombinationCellIter::new(&data, r, Rc::clone(&share));
        lc.iter().for_each(|_c| {counter += 1});
        println!("Custom comb {} combination done in {:?}", counter, timer.elapsed());
    }

    #[test]
    #[ignore]
    fn compare_gosper_custom_ref_iter() {
        use std::time::Instant;
        let data : Vec<i32> = (0..30i32).map(|i| {i}).collect();
        let r = 20;
        let mut result = vec![&data[0]; r];
        let share = result.as_mut_slice() as *mut [&i32];

        unsafe {
            let mut counter = 0;
            let timer = Instant::now();
            let stanford = GosperCombinationRefIter::new(&data, r, share);
            stanford.into_iter().for_each(|_c| {counter += 1});
            println!("Stanford comb {} combination done in {:?}", counter, timer.elapsed());
            counter = 0;
            let timer = Instant::now();
            let mut lc = LargeCombinationRefIter::new(&data, r, share);
            lc.iter().for_each(|_c| {counter += 1});
            println!("Custom comb {} combination done in {:?}", counter, timer.elapsed());
        }
    }

    #[test]
    #[ignore]
    fn bench_heap_fn() {
        use std::time::Instant;
        let mut data : Vec<i32> = (0..10i32).map(|i| {i}).collect();
        let timer = Instant::now();
        let mut counter = 0;

        heap_permutation(data.as_mut_slice(), |_p| {counter += 1});

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
    }

    #[test]
    #[ignore]
    fn bench_heap_iter() {
        use std::time::Instant;
        let mut data : Vec<i32> = (0..10i32).map(|i| {i}).collect();
        let timer = Instant::now();
        let mut counter = 0;

        data.permutation().for_each(|_p| {counter += 1});

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
    }

    #[test]
    #[ignore]
    fn bench_k_perm_fn() {
        use std::time::Instant;

        let data : Vec<i32> = (0..13i32).map(|i| {i}).collect();
        let timer = Instant::now();
        let mut counter = 0;

        k_permutation(data.as_slice(), 7, |_p| {counter += 1});

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
    }

    #[test]
    #[ignore]
    fn bench_k_perm_iter() {
        use std::time::Instant;

        let data : Vec<i32> = (0..13i32).map(|i| {i}).collect();
        let timer = Instant::now();
        let mut counter = 0;

        (data.as_slice(), 7usize).permutation().for_each(|_p| {counter += 1});

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
    }

    #[test]
    #[ignore]
    fn bench_cart_fn() {
        use std::time::Instant;
        let domain : Vec<i32> = (0..5i32).map(|i| {i}).collect();
        let domains : Vec<&[i32]> = (0..10).map(|_| domain.as_slice()).collect();
        let timer = Instant::now();
        let mut counter = 0;

        cartesian_product(domains.as_slice(), |_p| {counter += 1});

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
    }

    #[test]
    #[ignore]
    fn bench_cart_iter() {
        use std::time::Instant;
        let domain : Vec<i32> = (0..5i32).map(|i| {i}).collect();
        let domains : Vec<&[i32]> = (0..10).map(|_| domain.as_slice()).collect();
        let timer = Instant::now();
        let mut counter = 0;

        domains.as_slice().cart_prod().for_each(|_p| {counter += 1});

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
    }

    #[test]
    #[ignore]
    fn bench_x_perm_st_fn() { // st mean single thread
        use std::time::Instant;

        let mut data : Vec<u8> = (0..13u8).map(|v| v).collect();
        let mut counter = 0;
        let timer = Instant::now();

        x_permutation(&data, |_| true, |_p| {
            counter += 1;
        });

        println!("Done {} x_permutation in {:?}", counter, timer.elapsed());
        counter = 0;
        let timer = Instant::now();

        heap_permutation(&mut data, |_p| {
            counter += 1;
        });

        println!("Done {} heap_permutation in {:?}", counter, timer.elapsed());
    }

    #[test]
    #[ignore]
    fn bench_x_perm_mt_fn() { // st mean single thread
        use std::time::{Duration, Instant};

        let mut data : Vec<u8> = (0..13u8).map(|v| v).collect();
        let threads = 3usize;
        let chunk = data.len() / threads; // split data into 3 threads.
        let complete_count = Arc::new(RwLock::new(0u64));
        let total_counter = Arc::new(RwLock::new(0u64));
        for i in 0..threads {
            let u_bound = match i {
                j if j == threads - 1 => data.len() as u8, // last thread do all the rest
                _ => (chunk * (i + 1)) as u8
            };
            let l_bound = (chunk * i) as u8;
            println!("thread{}: {}-{}", i, l_bound, u_bound);
            let perm = get_permutation_for(&data, data.len(), l_bound as usize).unwrap();
            let t_dat : Vec<u8> = perm.iter().map(|v| **v).collect(); // need to move to each thread
            let t_counter = Arc::clone(&complete_count); // thread completed count
            let loc_counter = Arc::clone(&total_counter); // count number of permutation
            thread::spawn(move || {
                let mut counter = 0u64;
                x_permutation(&t_dat, |v| {
                    *v[0] >= l_bound && *v[0] < u_bound
                }, |_p| {
                    counter += 1;
                });

                *loc_counter.write().unwrap() += counter;
                println!("Done {} in local thread", counter);
                *t_counter.write().unwrap() += 1;
            });
        }

        let main = thread::spawn(move || {
            let timer = Instant::now();
            loop {
                if *complete_count.read().unwrap() != (threads as u64) {
                    thread::sleep(Duration::from_millis(100));
                } else {
                    println!("Done {} x_permutation {} threads in {:?}", &*total_counter.read().unwrap(), threads, timer.elapsed());
                    break;
                }
            }
        });

        main.join().unwrap();

        let mut counter = 0u64;
        let timer = Instant::now();

        heap_permutation(&mut data, |_p| {
            counter += 1;
        });

        println!("Done {} heap_permutation in {:?}", counter, timer.elapsed());
    }
}