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
//! # Easy share result
//! - Every function can take Rc<RefCell<>> to store result.
//! - An iterator that return owned value.
//! - Every callback style function can take Arc<RwLock<>> to store result.
//! 
//! # Easy usage
//! Two built-in traits that add combination and permutation functionality
//! to both Vec and slice.
//! 
//! # Unreach raw performance with unsafe
//! Every callback style function can take raw mutable pointer to store result.
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
//! use permutator::{CartesianProduct, cartesian_product};
//! let mut domains : &[&[i32]]= &[&[1, 2], &[3, 4, 5], &[6, 7, 8, 9]];
//! println!("=== Cartesian product iterative style ===");
//! CartesianProduct::new(domains).into_iter().for_each(|p| {
//!     println!("{:?}", p);
//! });
//! println!("=== cartesian product callback style ===");
//! cartesian_product(domains, |p| {
//!     // `p` is borrowed a ref to internal variable inside cartesian_product function.
//!     println!("{:?}", p);
//! });
//! ```
//! # See
//! - [Github repository for more examples](https://github.com/NattapongSiri/permutator)

extern crate num;

use num::{PrimInt, Unsigned};
use std::cell::RefCell;
use std::collections::{VecDeque};
use std::iter::{Product};
use std::rc::Rc;
use std::sync::{Arc, RwLock};

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
pub fn cartesian_product<T>(sets : &[&[T]], mut cb : impl FnMut(&[&T])) {
    let mut result = vec![&sets[0][0]; sets.len()];
    let mut more = true;
    let n = sets.len() - 1;
    let mut i = 0;
    let mut c = vec![0; sets.len()];
    while more {
        result[i] = &sets[i][c[i]];

        if i == n {
            c[i] += 1;
            cb(&result);
        }

        if i < n {
            i += 1;
        }

        while c[i] == sets[i].len() {
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
pub unsafe fn unsafe_cartesian_product<'a, T>(sets : &'a[&[T]], result : *mut [&'a T], mut cb : impl FnMut()) {
    let mut more = true;
    let n = sets.len() - 1;
    let mut i = 0;
    let mut c = vec![0; sets.len()];
    while more {
        (*result)[i] = &sets[i][c[i]];

        if i == n {
            c[i] += 1;
            cb();
        }

        if i < n {
            i += 1;
        }

        while c[i] == sets[i].len() {
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
/// The performance is on par with using [CartesianProduct](struct.CartesianProduct.html#method.next_into_cell)
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
pub fn cartesian_product_cell<'a, T>(sets : &'a[&[T]], result : Rc<RefCell<&'a mut [&'a T]>>, mut cb : impl FnMut()) {
    let mut more = true;
    let n = sets.len() - 1;
    let mut i = 0;
    let mut c = vec![0; sets.len()];
    while more {
        result.borrow_mut()[i] = &sets[i][c[i]];

        if i == n {
            c[i] += 1;
            cb();
        }

        if i < n {
            i += 1;
        }

        while c[i] == sets[i].len() {
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
/// The performance is on roughly 15%-20% slower than [CartesianProduct](struct.CartesianProduct.html)
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
pub fn cartesian_product_sync<'a, T>(sets : &'a[&[T]], result : Arc<RwLock<Vec<&'a T>>>, mut cb : impl FnMut()) {
    let mut more = true;
    let n = sets.len() - 1;
    let mut i = 0;
    let mut c = vec![0; sets.len()];
    while more {
        result.write().unwrap()[i] = &sets[i][c[i]];

        if i == n {
            c[i] += 1;
            cb();
        }

        if i < n {
            i += 1;
        }

        while c[i] == sets[i].len() {
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

/// Generate a combination out of given `domain`.
/// It call `cb` to several times to return each combination.
/// It's similar to [struct GosperCombination](struct.GosperCombination.html) but
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
/// [GosperCombination with next_into_cell function](struct.GosperCombination.html#method.next_into_cell).
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

/// Generate k-permutation over slice of `d`. For example: d = &[1, 2, 3]; k = 2.
/// The result will be [1, 2], [2, 1], [1, 3], [3, 1], [2, 3], [3, 2]
/// 
/// The implementation calculate each combination by using
/// Gospel's algorithm then permute each combination 
/// use Heap's algorithm. There's [KPermutation struct](struct.KPermutation.html) that
/// also generate KPermutation but in iterative style. 
/// The performance of this function is slightly faster than 
/// [KPermutation struct](struct.KPermutation.html) by about 15%-20%
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
/// 
/// # Limitation
/// Gosper algorithm need to know the MSB (most significant bit).
/// The current largest known MSB data type is u128.
/// This make the implementation support up to 128 elements slice.
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
/// - [Gosper's algorithm in Wikipedia page, October 9, 2018](https://en.wikipedia.org/wiki/Combinatorial_number_system#Applications)
/// - [Heap's algorithm in Wikipedia page, October 9, 2018](https://en.wikipedia.org/wiki/Heap%27s_algorithm)
pub fn k_permutation<T>(d : &[T], k : usize, mut cb : impl FnMut(&[&T]) -> ()) {
    if d.len() < k {
        panic!("Cannot create k-permutation of size {} for data of length {}", k, d.len());
    } else if k == 0 {
        // k = 0 mean mean permutation frame size is 0, it cannot have permutation
        return
    }

    let (mut subset, mut map) = create_k_set(d, k); // utility function to create initial subset
    cb(&subset);
    heap_permutation(&mut subset, |permuted| {
        cb(permuted);
    }); // generate all possible permutation for initial subset

    while let Some(_) = swap_k((&mut subset, &mut map), d) { // repeatly swap element
        cb(&subset);
        heap_permutation(&mut subset, |permuted| {
            cb(permuted);
        }); // generate all possible permutation per each subset
    }
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
/// # See
/// - [k_permutation function](fn.k_permutation.html)
pub unsafe fn unsafe_k_permutation<'a, T>(d : &'a [T], k : usize, result : *mut [&'a T], mut cb : impl FnMut() -> ()) {
    if d.len() < k {
        panic!("Cannot create k-permutation of size {} for data of length {}", k, d.len());
    } else if k == 0 {
        // k = 0 mean mean permutation frame size is 0, it cannot have permutation
        return
    }

    let mut map : u128 = 0;

    unsafe_create_k_set(d, k, result, &mut map); // utility function to create initial subset
    cb();
    heap_permutation(&mut *result, |_| {
        cb();
    }); // generate all possible permutation for initial subset

    while let Some(_) = swap_k((&mut *result, &mut map), d) { // repeatly swap element
        cb();
        heap_permutation(&mut *result, |_| {
            cb();
        }); // generate all possible permutation per each subset
    }
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
/// [next_into_cell](struct.KPermutation.html#method.next_into_cell) by
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
/// # See
/// - [k_permutation function](fn.k_permutation.html)
pub fn k_permutation_cell<'a, T>(d : &'a [T], k : usize, result : Rc<RefCell<&'a mut [&'a T]>>, mut cb : impl FnMut() -> ()) {
    if d.len() < k {
        panic!("Cannot create k-permutation of size {} for data of length {}", k, d.len());
    } else if k == 0 {
        // k = 0 mean mean permutation frame size is 0, it cannot have permutation
        return
    }

    let mut map : u128 = 0;

    create_k_set_in_cell(d, k, &result, &mut map); // utility function to create initial subset
    cb();
    heap_permutation_cell(&result, || {
        cb();
    }); // generate all possible permutation for initial subset

    while let Some(_) = swap_k_in_cell((&result, &mut map), d) { // repeatly swap element
        cb();
        heap_permutation_cell(&result, || {
            cb();
        }); // generate all possible permutation per each subset
    }
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
    if d.len() < k {
        panic!("Cannot create k-permutation of size {} for data of length {}", k, d.len());
    } else if k == 0 {
        // k = 0 mean mean permutation frame size is 0, it cannot have permutation
        return
    }

    let mut map : u128 = 0;

    create_k_set_sync(d, k, &result, &mut map); // utility function to create initial subset
    cb();
    heap_permutation_sync(&result, || {
        cb();
    }); // generate all possible permutation for initial subset

    while let Some(_) = swap_k_sync((&result, &mut map), d) { // repeatly swap element
        cb();
        heap_permutation_sync(&result, || {
            cb();
        }); // generate all possible permutation per each subset
    }
}

/// Generate a cartesian product between given domains in an iterator style.
/// The struct implement `Iterator` trait so it can be used in `Iterator` 
/// style. The struct provide [into_iter()](#method.into_iter()) function 
/// that return itself.
/// 
/// # Example
/// - Iterator style usage
/// ```
///    use permutator::CartesianProduct;
///    use std::time::Instant;
///    let data : &[&[usize]] = &[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]];
///    let cart = CartesianProduct::new(&data);
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
/// - Mimic iterator style usage
/// ```
///    use permutator::CartesianProduct;
///    use std::time::Instant;
///    let data : &[&[usize]] = &[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]];
///    let mut cart = CartesianProduct::new(&data);
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    while let Some(p) = cart.next() {
///        // println!("{:?}", p);
///        counter += 1;
///    }
///
///    assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
///    println!("Total {} products done in {:?}", counter, timer.elapsed());
/// ```
pub struct CartesianProduct<'a, T> where T : 'a {
    c : Vec<usize>,
    domains : &'a [&'a [T]],
    i : usize,

    result : Vec<&'a T>
}

impl<'a, T> CartesianProduct<'a, T> where T : 'a {
    /// Create a new Cartesian product iterator that create a product between
    /// each domain inside `domains`.
    /// # Parameters
    /// - `domains` A slice of domains to create a cartesian product between
    /// each domain inside it.
    /// # Return
    /// An object that can be iterate over in iterator style.
    pub fn new(domains : &'a[&[T]]) -> CartesianProduct<'a, T> {

        CartesianProduct {
            c : vec![0; domains.len()],
            domains : domains,
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

    /// Mimic iterator `next` function but return a reference instead of
    /// clone/copy the value into the result.
    pub fn next(&mut self) -> Option<(&[&T])> {
        let mut exhausted = false;
        // move and set `result` and `c` up until all `domains` processed
        while self.i < self.domains.len() && !exhausted {
            // if current domain is exhausted.
            if self.c[self.i] == self.domains[self.i].len() {
                // reset all exhausted domain in `result` and `c`
                let mut k = self.i;

                // reset all exhausted until either found non-exhausted or reach first domain
                while self.c[k] == self.domains[k].len() && k > 0 {
                    self.c[k] = 1;
                    self.result[k] = &self.domains[k][0];
                    k -= 1;
                }

                if k == 0 && self.c[k] == self.domains[k].len() {
                    // if first domain is also exhausted then flag it.
                    exhausted = true;
                } else {
                    // otherwise advance c[k] and set result[k] to next value
                    self.result[k] = &self.domains[k][self.c[k]];
                    self.c[k] += 1;
                }
            } else {
                // non exhausted domain, advance `c` and set result
                self.result[self.i] = &self.domains[self.i][self.c[self.i]];
                self.c[self.i] += 1;
            }
            self.i += 1;
        }

        if exhausted {
            None
        } else {
            self.i -= 1; // rewind `i` back to last domain
            Some(&self.result)
        }
    }

    /// Mimic iterator `next` function but return value into Rc<RefCell<>> that
    /// contains mutable slice. It also return an empty Option to tell caller
    /// to distinguish if it's put new value or the iterator itself is exhausted.
    /// # Paramerter
    /// - `result` An Rc<RefCell<>> contains a mutable slice with length equals
    /// to number of `domains` given in [CartesianProduct::new()](struct.CartesianProduct.html#method.new).
    /// The value inside result will be updated everytime this function is called
    /// until the function return None. The performance using this function is
    /// on part with [cartesian_cell function](fn.cartesian_product_cell.html) on uncontrol
    /// test environment.
    /// # Return
    /// New cartesian product between each `domains` inside `result` parameter 
    /// and also return `Some(())` if result is updated or `None` when there's
    /// no new result.
    pub fn next_into_cell(&mut self, result: &Rc<RefCell<&mut [&'a T]>>) -> Option<()> {
        let mut exhausted = false;
        let mut result = result.borrow_mut();
        
        // move and set `result` and `c` up until all `domains` processed
        while self.i < self.domains.len() && !exhausted {
            // if current domain is exhausted.
            if self.c[self.i] == self.domains[self.i].len() {
                // reset all exhausted domain in `result` and `c`
                let mut k = self.i;

                // reset all exhausted until either found non-exhausted or reach first domain
                while self.c[k] == self.domains[k].len() && k > 0 {
                    self.c[k] = 1;
                    result[k] = &self.domains[k][0];
                    k -= 1;
                }

                if k == 0 && self.c[k] == self.domains[k].len() {
                    // if first domain is also exhausted then flag it.
                    exhausted = true;
                } else {
                    // otherwise advance c[k] and set result[k] to next value
                    result[k] = &self.domains[k][self.c[k]];
                    self.c[k] += 1;
                }
            } else {
                // non exhausted domain, advance `c` and set result
                result[self.i] = &self.domains[self.i][self.c[self.i]];
                self.c[self.i] += 1;
            }
            self.i += 1;
        }

        if exhausted {
            None
        } else {
            self.i -= 1; // rewind `i` back to last domain
            
            Some(())
        }
    }
}

impl<'a, T> Iterator for CartesianProduct<'a, T> {
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Vec<&'a T>> {
        let mut exhausted = false;
        // move and set `result` and `c` up until all `domains` processed
        while self.i < self.domains.len() && !exhausted {
            // if current domain is exhausted.
            if self.c[self.i] == self.domains[self.i].len() {
                // reset all exhausted domain in `result` and `c`
                let mut k = self.i;

                // reset all exhausted until either found non-exhausted or reach first domain
                while self.c[k] == self.domains[k].len() && k > 0 {
                    self.c[k] = 1;
                    self.result[k] = &self.domains[k][0];
                    k -= 1;
                }

                if k == 0 && self.c[k] == self.domains[k].len() {
                    // if first domain is also exhausted then flag it.
                    exhausted = true;
                } else {
                    // otherwise advance c[k] and set result[k] to next value
                    self.result[k] = &self.domains[k][self.c[k]];
                    self.c[k] += 1;
                }
            } else {
                // non exhausted domain, advance `c` and set result
                self.result[self.i] = &self.domains[self.i][self.c[self.i]];
                self.c[self.i] += 1;
            }
            self.i += 1;
        }

        if exhausted {
            None
        } else {
            self.i -= 1; // rewind `i` back to last domain
            Some(self.result.to_owned())
        }
    }
}

/// Heap's permutation in iterator style implementation.
/// It provide two way to iterate over the permutation.
/// - One conform to Iterator trait constraint where each
/// iteration return a moved value. However, Heap's algorithm
/// perform swap in place, it need to clone each permutation 
/// before return.
/// - Another way is to manually call `next` on each loop. 
/// It mimic Iterator trait style by returning an
/// Option that contains a reference to internal slice holding
/// current permutation. It's considerable faster.
/// 
/// # Examples
/// - Iterator style usage example:
/// ```
///    use permutator::HeapPermutation;
///    use std::time::{Instant};
///    let data = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
///    println!("0:{:?}", data);
///    let mut permutator = HeapPermutation::new(data);
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
/// - An example of manually calling next function
/// ```
///    use permutator::HeapPermutation;
///    use std::time::{Instant};
/// 
///    let data = &mut [1, 2, 3, 4];
///    // print original data before permutation
///    // println!("0:{:?}", data);
///    let mut permutator = HeapPermutation::new(data);
///    let timer = Instant::now();
///    let mut counter = 1;
///
///    while let Some(permutated) = permutator.next() {
///        // uncomment the line below to print all possible permutation
///        // println!("{}:{:?}", counter, permutated);
///        counter += 1;
///    }
///
///    println!("Done {} permutations in {:?}", counter, timer.elapsed());
/// ```
/// In test environment, given a slice of 10 string having about 40 character each.
/// The Iterator trait implementation is about 100 times (40ms vs 4s) slower than a mimic 
/// Iterator way. This is because the design of manual `next` function is to store the
/// permutation into a mutable slice. In the test case, it reuse existing one. 
/// However, the Iterator implementation return a new slice on each call.
/// # See
/// - [Heap's algorithm in Wikipedia page, October 9, 2018](https://en.wikipedia.org/wiki/Heap%27s_algorithm)
pub struct HeapPermutation<'a, T> where T : 'a {
    c : Vec<usize>,
    data : &'a mut [T],
    i : usize
}

impl<'a, T> HeapPermutation<'a, T> {
    /// Construct a new permutation iterator.
    /// Note: the provided parameter will get mutated
    /// in placed at first call to next.
    pub fn new(data : &mut [T]) -> HeapPermutation<T> {
        HeapPermutation {
            c : vec![0; data.len()],
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

    /// Mutate the data in place then return a reference to
    /// internal mutated data inside the struct.
    /// It will return `None` when all permutation is done.
    /// It's safe to wrap this function call in 
    /// `while let` syntax.
    pub fn next(&mut self) -> Option<&[T]> {
        let i = &mut self.i;

        while *i < self.data.len() {
            if self.c[*i] < *i {
                if *i % 2 == 0 {
                    self.data.swap(0, *i);
                } else {
                    self.data.swap(self.c[*i], *i);
                }

                self.c[*i] += 1;
                *i = 0;
                return Some(self.data)
            } else {
                self.c[*i] = 0;
                *i += 1;
            }
        }

        None
    }

    /// Reset this permutator so calling next will continue
    /// permutation on current permuted data.
    /// It will not reset permuted data.
    pub fn reset(&mut self) {
        self.i = 0;
        self.c.iter_mut().for_each(|c| {*c = 0;});
    }
}

impl<'a, T> Iterator for HeapPermutation<'a, T> where T : Clone {
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let i = &mut self.i;

        while *i < self.data.len() {
            if self.c[*i] < *i {
                if *i % 2 == 0 {
                    self.data.swap(0, *i);
                } else {
                    self.data.swap(self.c[*i], *i);
                }

                self.c[*i] += 1;
                *i = 0;
                return Some(self.data.to_vec())
            } else {
                self.c[*i] = 0;
                *i += 1;
            }
        }

        None
    }
}

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
/// ```
///    use permutator::GosperCombination;
///    use std::time::{Instant};
///    let gosper = GosperCombination::new(&[1, 2, 3, 4, 5], 3);
///    let mut counter = 0;
///    let timer = Instant::now();
///
///    for combination in gosper {
///        // uncomment a line below to print each combination
///        // println!("{}:{:?}", counter, combination);
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
pub struct GosperCombination<'a, T> where T : 'a {
    data : &'a [T], // data to generate a combination
    len : usize, // total possible number of combination.
    x : u128, // A binary map to generate combination
}

impl<'a, T> GosperCombination<'a, T> {
    /// Create new combination generator using Gosper's algorithm.
    /// `r` shall be smaller than data.len(). 
    /// 
    /// Note: It perform no check on given parameter. 
    /// If r is larger than length of data then iterate over it
    /// will not occur. The iteration will be end upon enter.
    pub fn new(data : &[T], r : usize) -> GosperCombination<T> {
        let mut x : u128 = 1;
        x <<= r;
        x -= 1;
        let n = data.len();
        GosperCombination {
            data : data,
            len : divide_factorial(n, multiply_factorial(n - r, r)),
            x : x
        }
    }

    /// Total number of combinations this iterate can return.
    /// It will equals to n!/((n-r)!*r!)
    pub fn len(&self) -> usize {
        self.len
    }

    /// Attempt to get next combination and mutate a given
    /// `result` to store the next combination.
    /// This function mimic Iterator's next style.
    /// It'll return an empty Option because result will be
    /// contain in given paramter.
    /// It return `None` when there's no further possible combination.
    pub fn next(&mut self, result : &mut [&'a T]) -> Option<()> {
        let mut j = 0;
        let mut i = 0;
        let mut mask = self.x;
        while mask > 0 && j < self.data.len() {
            if mask & 1 == 1 {
                result[i] = &self.data[j];
                i += 1;
            }

            mask >>= 1;
            j += 1;
        }

        if mask != 0 {
            return None
        }

        // gosper_combination(&mut self.x);
        stanford_combination(&mut self.x); // enhanced Gosper algorithm done by Stanford university

        Some(())
    }

    /// Attempt to get next combination and store it into Rc<RefCell<>> 
    /// of mutable slice `result` to store the next combination.
    /// This function mimic Iterator's next style.
    /// It'll return an empty Option because result will be
    /// contain in given paramter.
    /// It return `None` when there's no further possible combination.
    /// 
    /// Use this function when you want a faster than copy/clone but need to
    /// share the combination to multiple target.
    /// 
    /// The test in uncontrol environment found that using this function yield
    /// performance on par with [combination_cell](fn.combination_cell.html) function.
    pub fn next_into_cell(&mut self, result : &Rc<RefCell<&mut [&'a T]>>) -> Option<()> {
        let mut j = 0;
        let mut i = 0;
        let mut mask = self.x;
        while mask > 0 && j < self.data.len() {
            if mask & 1 == 1 {
                result.borrow_mut()[i] = &self.data[j];
                i += 1;
            }

            mask >>= 1;
            j += 1;
        }

        if mask != 0 {
            return None
        }

        // gosper_combination(&mut self.x);
        stanford_combination(&mut self.x); // enhanced Gosper algorithm done by Stanford university

        Some(())
    }
}

impl<'a, T> IntoIterator for GosperCombination<'a, T> {
    type Item = Vec<&'a T>;
    type IntoIter = CombinationIterator<'a, T>;

    fn into_iter(self) -> CombinationIterator<'a, T> {
        CombinationIterator {
            data : self.data,
            x : self.x
        }
    }
}

/// An iterator return from [struct GosperCombination](struct.GosperCombination.html)
/// or from [trait Combination](trait.Combination.html) over slice or vec of data.
pub struct CombinationIterator<'a, T> where T : 'a {
    data : &'a [T], // original data
    x : u128, // Gosper binary map
}

impl<'a, T> Iterator for CombinationIterator<'a, T> {
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Vec<&'a T>> {
        let mut combination : Vec<&T> = Vec::new();

        if 128 - self.x.leading_zeros() as usize > self.data.len() {
            return None
        } else {
            let mut j = 0;
            let mut mask = self.x;
            while mask > 0 {
                if mask & 1 == 1 {
                    combination.push(&self.data[j]);
                }

                mask >>= 1;
                j += 1;
            }
        }

        stanford_combination(&mut self.x);

        return Some(combination)
    }
}

/// k-Permutation over data of length n where k must be
/// less than n.
/// It'll attempt to permute given data by pick `k` elements
/// out of data. It use Gosper algorithm to pick the elements.
/// It then use Heap's algorithm to permute those `k` elements
/// and return each permutation back to caller.
/// 
/// Similar to [HeapPermutation](struct.HeapPermutation.html), 
/// It provides two style of getting a permuted value.
/// - Iterator compatible style
/// - Manual iterative style
/// 
/// # Examples
/// - Iterator style permit using 'for-in' style loop along with
/// enable usage of functional paradigm over iterator object.
/// ```
///    use permutator::KPermutation;
///    use std::time::Instant;
///    let data = [1, 2, 3, 4, 5];
///    let permutator = KPermutation::new(&data, 3);
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
/// - Manual iterative style which yield higher throughput because it return
/// a reference to internal slice stored inside the struct.
/// ```
///    use permutator::KPermutation;
///    use std::time::Instant;
///    let data = [1, 2, 3, 4, 5];
///    let mut permutator = KPermutation::new(&data, 3);
///    let mut counter = 0;
///    // println!("Begin testing KPermutation");
///    let timer = Instant::now();
///
///    while let Some(permuted) = permutator.next() {
///        // uncomment the line below to print all possible value
///        // println!("{}:{:?}", counter, permuted);
///        counter += 1;
///    }
///
///    println!("Total {} permutations done in {:?}", counter, timer.elapsed());
///    assert_eq!(60, counter);
/// ```
/// 
/// # Limitation
/// Gosper algorithm need to know the MSB (most significant bit).
/// The current largest known MSB data type is u128.
/// This make the implementation support up to 128 elements slice.
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
/// - [GosperCombination](struct.GoserPermutation.html)
/// - [HeapPermutation](struct.HeapPermutation.html)
pub struct KPermutation<'a, T> where T : 'a {
    permuted : Vec<&'a T>,
    
    len : usize,

    combinator : GosperCombination<'a, T>,
    permutator : Option<HeapPermutation<'a, &'a T>>
}

impl<'a, T> KPermutation<'a, T> {
    pub fn new(data : &[T], k : usize) -> KPermutation<T> {
        let permuted = vec![&data[0]; k];
        let combinator = GosperCombination::new(data, k);
        let n = data.len();

        KPermutation {
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

    /// Get total number of permutation this KPermutation object
    /// can permute. It'll be equals to number of possible `next`
    /// call.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Mimic iterator's `next` function but return a reference to
    /// current permuted store inside this struct instead of
    /// create a copy of permuted data like actual `next` function
    /// implemented in `Iterator` trait.
    pub fn next(&mut self) -> Option<&[&T]> {
        unsafe fn get_next<'a, T>(combinator : &mut GosperCombination<'a, T>, permuted : *mut Vec<&'a T>, permutator : *mut Option<HeapPermutation<'a, &'a T>>) -> Option<()> {
            if let Some(ref mut perm) = *permutator {
                if let Some(_) = perm.next() {
                    // get next permutation of current permutator
                    Some(())
                } else {
                    if let Ok(_) = next_permutator(combinator, permuted, permutator) {
                        // now perm suppose to be new permutator.
                        Some(())
                    } else {
                        // all combination permuted
                        return None;
                    }
                }
            } else {
                if let Ok(_) = next_permutator(combinator, permuted, permutator) {
                    if let Some(_) = *permutator {
                        Some(())
                    } else {
                        return None;
                    }
                } else {
                    return None;
                }
            }
        }

        unsafe fn next_permutator<'a, T>(combinator : &mut GosperCombination<'a, T>, permuted : *mut Vec<&'a T>, permutator : *mut Option<HeapPermutation<'a, &'a T>>) -> Result<(), ()> {
            if let Some(_) = combinator.next(&mut *permuted) {
                if let Some(ref mut permutator) = *permutator {
                    permutator.reset(); // fresh new permutator
                    Ok(())
                } else {
                    // first time getting a permutator, need to create one.
                    let new_permutator = HeapPermutation::new(&mut *permuted);
                    *permutator = Some(new_permutator);
                    Ok(())
                }
            } else {
                Err(())
            }
        }
        unsafe {
            let permutator = &mut self.permutator as *mut Option<HeapPermutation<'a, &'a T>>;
            let permuted = &mut self.permuted as *mut Vec<&'a T>;
            if let Some(_) = get_next(&mut self.combinator, permuted, permutator) {
                return Some(&self.permuted);
            } else {
                return None;
            }
        }
    }

    /// Mimic iterator's `next` function but return next permutation
    /// into Rc<RefCell<>> of mutable slice instead.
    /// This function is intended to return a sharable result without
    /// deep copy of each permutation.
    /// The mutable slice inside Rc<RefCell<>> is the reference to 
    /// internal data within this object. 
    /// Any modification made to result may cause undesired behavior.
    pub fn next_into_cell(&mut self, result : &Rc<RefCell<&mut [&'a T]>>) -> Option<()> {
        unsafe fn get_next<'a, T>(combinator : &mut GosperCombination<'a, T>, permuted : *mut Vec<&'a T>, permutator : *mut Option<HeapPermutation<'a, &'a T>>) -> Option<()> {
            if let Some(ref mut perm) = *permutator {
                if let Some(_) = perm.next() {
                    // get next permutation of current permutator
                    Some(())
                } else {
                    if let Ok(_) = next_permutator(combinator, permuted, permutator) {
                        // now perm suppose to be new permutator.
                        Some(())
                    } else {
                        // all combination permuted
                        return None;
                    }
                }
            } else {
                if let Ok(_) = next_permutator(combinator, permuted, permutator) {
                    if let Some(_) = *permutator {
                        Some(())
                    } else {
                        return None;
                    }
                } else {
                    return None;
                }
            }
        }

        unsafe fn next_permutator<'a, T>(combinator : &mut GosperCombination<'a, T>, permuted : *mut Vec<&'a T>, permutator : *mut Option<HeapPermutation<'a, &'a T>>) -> Result<(), ()> {
            if let Some(_) = combinator.next(&mut *permuted) {
                if let Some(ref mut permutator) = *permutator {
                    permutator.reset(); // fresh new permutator
                    Ok(())
                } else {
                    // first time getting a permutator, need to create one.
                    let new_permutator = HeapPermutation::new(&mut *permuted);
                    *permutator = Some(new_permutator);
                    Ok(())
                }
            } else {
                Err(())
            }
        }
        unsafe {
            let permutator = &mut self.permutator as *mut Option<HeapPermutation<'a, &'a T>>;
            let permuted = &mut self.permuted as *mut Vec<&'a T>;
            if let Some(_) = get_next(&mut self.combinator, permuted, permutator) {
                result.replace(&mut *permuted);
                return Some(());
            } else {
                return None;
            }
        }
    }
}

impl<'a, T> Iterator for KPermutation<'a, T> {
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Vec<&'a T>> {
        unsafe fn get_next<'a, T>(combinator : &mut GosperCombination<'a, T>, permuted : *mut Vec<&'a T>, permutator : *mut Option<HeapPermutation<'a, &'a T>>) -> Option<()> {
            if let Some(ref mut perm) = *permutator {
                if let Some(_) = perm.next() {
                    // get next permutation of current permutator
                    Some(())
                } else {
                    if let Ok(_) = next_permutator(combinator, permuted, permutator) {
                        // now perm suppose to be new permutator.
                        Some(())
                    } else {
                        // all combination permuted
                        return None;
                    }
                }
            } else {
                if let Ok(_) = next_permutator(combinator, permuted, permutator) {
                    if let Some(_) = *permutator {
                        Some(())
                    } else {
                        return None;
                    }
                } else {
                    return None;
                }
            }
        }

        unsafe fn next_permutator<'a, T>(combinator : &mut GosperCombination<'a, T>, permuted : *mut Vec<&'a T>, permutator : *mut Option<HeapPermutation<'a, &'a T>>) -> Result<(), ()> {
            if let Some(_) = combinator.next(&mut *permuted) {
                if let Some(ref mut permutator) = *permutator {
                    permutator.reset(); // fresh new permutator
                    Ok(())
                } else {
                    // first time getting a permutator, need to create one.
                    let new_permutator = HeapPermutation::new(&mut *permuted);
                    *permutator = Some(new_permutator);
                    Ok(())
                }
            } else {
                Err(())
            }
        }
        unsafe {
            let permutator = &mut self.permutator as *mut Option<HeapPermutation<'a, &'a T>>;
            let permuted = &mut self.permuted as *mut Vec<&'a T>;
            if let Some(_) = get_next(&mut self.combinator, permuted, permutator) {
                return Some(self.permuted.to_vec());
            } else {
                return None;
            }
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
/// - The [HeapPermutation struct](struct.HeapPermutation.html)
/// provide alternate way of getting permutation but in iterative way.
/// # Warning
/// The permutation is done in place which mean the parameter `d` will be
/// mutated.
/// 
/// # Notes
/// 1. The value passed to callback function will equals to value inside parameter `d`.
pub fn heap_permutation<T>(d : &mut [T], mut cb : impl FnMut(&[T]) -> ()) {
    let n = d.len();
    let mut c = vec![0; n];
    let mut i = 0;
    while i < n {
        if c[i] < i {
            if i & 1 == 0 { // equals to mod 2 because it take only 0 and 1 aka last bit
                d.swap(0, i);
            } else {
                d.swap(c[i], i);
            }

            cb(d);
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
pub fn heap_permutation_cell<T>(d : &Rc<RefCell<&mut [T]>>, mut cb : impl FnMut() -> ()) {
    let n = d.borrow().len();
    let mut c = vec![0; n];
    let mut i = 0;
    while i < n {
        if c[i] < i {
            if i & 1 == 0 { // equals to mod 2 because it take only 0 and 1 aka last bit
                d.borrow_mut().swap(0, i);
            } else {
                d.borrow_mut().swap(c[i], i);
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
/// - `d` an Rc<RefCell<>> to mutable slice data to be permuted.
/// - `cb` a callback function that will be called several times for each permuted value.
/// 
/// # Warning
/// The permutation is done in place which mean the parameter `d` will be
/// mutated.
/// 
/// # Notes
/// 1. The value passed to callback function will equals to value inside parameter `d`.
pub fn heap_permutation_sync<T>(d : &Arc<RwLock<Vec<T>>>, mut cb : impl FnMut() -> ()) {
    let n = d.read().unwrap().len();
    let mut c = vec![0; n];
    let mut i = 0;
    while i < n {
        if c[i] < i {
            if i & 1 == 0 { // equals to mod 2 because it take only 0 and 1 aka last bit
                d.write().unwrap().swap(0, i);
            } else {
                d.write().unwrap().swap(c[i], i);
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
pub trait Combination<T> {
    /// Create a [CombinationIterator](struct.CombinationIterator.html)
    /// of `k` size out of `self`.
    /// See [CombinationIterator](struct.CombinationIterator.html) for
    /// how to use [CombinationIterator](struct.CombinationIterator.html)
    /// 
    /// # Return
    /// A new [CombinationIterator<T>](struct.CombinationIterator.html)
    fn combination(&self, k : usize) -> CombinationIterator<T>;
}

impl<T> Combination<T> for [T] {
    fn combination(&self, k : usize) -> CombinationIterator<T> {
        let mut x : u128 = 1;
        x <<= k;
        x -= 1;

        CombinationIterator {
            data : self,
            x : x
        }
    }
}

impl<T> Combination<T> for Vec<T> {
    fn combination(&self, k : usize) -> CombinationIterator<T> {
        let mut x : u128 = 1;
        x = (x << k) - 1;
        
        CombinationIterator {
            data : self,
            x : x
        }
    }
}

/// Create a permutation iterator that permute data in place.
/// It return an object of [HeapPermutation](struct.HeapPermutation.html)
/// which can be used as iterator or manual iterate for higher throughput.
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
/// - [HeapPermutation](struct.HeapPermutation.html) for more detail
/// about how to use [HeapPermutation](struct.HeapPermutation.html).
/// - [Example implementation](trait.Permutation.html#foreign-impls) on foreign type
pub trait Permutation<T> {
    /// Create a permutation based on Heap's algorithm.
    /// It return [HeapPermutation](struct.HeapPermutation.html) object.
    fn permutation(&mut self) -> HeapPermutation<T>;
}

impl<T> Permutation<T> for [T] {
    fn permutation(&mut self) -> HeapPermutation<T> {
        HeapPermutation {
            c : vec![0; self.len()],
            data : self,
            i : 0
        }
    }
}

impl<T> Permutation<T> for Vec<T> {
    fn permutation(&mut self) -> HeapPermutation<T> {
        HeapPermutation {
            c : vec![0; self.len()],
            data : self,
            i : 0
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
fn swap_k<'a, 'b : 'a, T>(subset_map : (&'a mut [&'b T], &mut u128), d : &'b[T]) -> Option<()> {
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
        let cart = CartesianProduct::new(&data);
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
    fn test_CartesianProduct_mimic_iterator() {
        use std::time::Instant;
        let data : &[&[usize]] = &[&[1, 2], &[3, 4, 5, 6], &[7, 8, 9]];
        let mut cart = CartesianProduct::new(&data);
        let mut counter = 0;
        let timer = Instant::now();

        while let Some(p) = cart.next() {
            // println!("{:?}", p);
            counter += 1;
        }

        assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
        println!("Total {} products done in {:?}", counter, timer.elapsed());
    }

    #[allow(unused)]
    #[test]
    fn test_k_permutation() {
        use std::time::{Instant};
        let data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
        let mut counter = 0;
        let timer = Instant::now();
        k_permutation(&data, 8, |permuted| {
            // uncomment line below to print all k-permutation
            // println!("{}:{:?}", counter, permuted);
            counter += 1;
        });

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
        assert_eq!(51891840, counter);
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
        println!("0:{:?}", data);
        let mut permutator = HeapPermutation::new(&mut data);
        let timer = Instant::now();
        let mut counter = 1;

        while let Some(permutated) = permutator.next() {
            // println!("{}:{:?}", counter, permutated);
            counter += 1;
        }

        assert_eq!(6, counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_HeapPermutationIterator() {
        use std::time::{Instant};
        let mut data : Vec<String> = (1..=3).map(|num| {format!("some ridiculously long word prefix without any point{}", num)}).collect();
        // let data = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        println!("0:{:?}", data);
        let permutator = HeapPermutation::new(&mut data);
        let timer = Instant::now();
        let mut counter = 1;

        for permutated in permutator {
            // println!("{}:{:?}", counter, permutated);
            counter += 1;
        }

        println!("Done {} permutations in {:?}", counter, timer.elapsed());
        assert_eq!(6, counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_HeapPermutationIntoIterator() {
        use std::time::{Instant};
        let mut data : Vec<String> = (1..=3).map(|num| {format!("some ridiculously long word prefix without any point{}", num)}).collect();
        // let data = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        println!("0:{:?}", data);
        let permutator = HeapPermutation::new(&mut data);
        let timer = Instant::now();
        let mut counter = 1;

        permutator.into_iter().for_each(|permutated| {counter += 1;});

        println!("Done {} permutations in {:?}", counter, timer.elapsed());
        assert_eq!(6, counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_GosperCombinationIterator() {
        use std::time::{Instant};
        let gosper = GosperCombination::new(&[1, 2, 3, 4, 5], 3);
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
    fn test_GosperCombinationIteratorAlike() {
        use std::time::{Instant};
        let data = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
        let r = 7;
        let mut gosper = GosperCombination::new(data, r);
        let mut counter = 0;
        let timer = Instant::now();
        let mut result = vec![&data[0]; r];

        while let Some(_) = gosper.next(&mut result) {
            // println!("{}:{:?}", counter, combination);
            counter += 1;
        }

        println!("Total {} combinations in {:?}", counter, timer.elapsed());
        // assert_eq!(10, counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_KPermutation() {
        use std::time::Instant;
        let data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
        let mut permutator = KPermutation::new(&data, 8);
        let mut counter = 0;
        // println!("Begin testing KPermutation");
        let timer = Instant::now();

        while let Some(permuted) = permutator.next() {
            // println!("{}:{:?}", counter, permuted);
            counter += 1;
        }

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
        assert_eq!(51891840, counter);
    }

    #[allow(non_snake_case, unused)]
    #[test]
    fn test_KPermutationIterator() {
        use std::time::Instant;
        let data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
        let permutator = KPermutation::new(&data, 8);
        let mut counter = 0;
        // println!("Begin testing KPermutation");
        let timer = Instant::now();

        for permuted in permutator {
            // println!("{}:{:?}", counter, permuted);
            counter += 1;
        }

        println!("Total {} permutations done in {:?}", counter, timer.elapsed());
        assert_eq!(51891840, counter);
    }

    #[allow(unused)]
    #[test]
    fn test_cartesian_product() {
        use std::time::Instant;
        let set = (1..14).map(|item| item).collect::<Vec<u64>>();
        let mut data = Vec::<&[u64]>::new();
        for _ in 0..7 {
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

    #[test]
    fn test_combination_trait() {
        let data = [1, 2, 3, 4, 5, 6, 7, 8];
        let k = 3;
        let mut counter = 0;
        for combination in data.combination(k) {
            println!("{:?}", combination);
            counter += 1;
        }

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
    fn test_k_permutation_primitive() {
        let data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
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
        let k = 8;
        let data = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
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
        let k = 7;
        let data = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
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
        let k = 7;
        let data = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
        let result = vec![&data[0]; k];
        let result_sync = Arc::new(RwLock::new(result));

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
        let (main_send, main_recv) = mpsc::sync_channel(0);
        let t1_local = main_send.clone();
        let t1_dat = Arc::clone(&result_sync);
        thread::spawn(move || {
            while let Some(_) = t1_recv.recv().unwrap() {
                let result : &Vec<&i32> = &*t1_dat.read().unwrap();
                // println!("Thread1: {:?}", result);
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
                let result : &Vec<&i32> = &*t2_dat.read().unwrap();
                // println!("Thread2: {:?}", result);
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
        let k = 7;
        let data : &[i32] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<Vec<&i32>>>(0);

        thread::spawn(move || {
            while let Some(c) = t1_recv.recv().unwrap() {
                let result : Vec<&i32> = c;
                // println!("Thread1: {:?}", result);
            }
            println!("Thread1 is done");
        });

        // worker thread 2
        let (t2_send, t2_recv) = mpsc::sync_channel::<Option<Vec<&i32>>>(0);
        thread::spawn(move || {
            while let Some(c) = t2_recv.recv().unwrap() {
                let result : Vec<&i32> = c;
                // println!("Thread2: {:?}", result);
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
        let k = 7;
        let data = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
        let mut result = vec![&data[0]; k];
        let result_cell = Rc::new(RefCell::new(result.as_mut_slice()));

        let worker1 = Worker1 {
            data : Rc::clone(&result_cell)
        };
        let worker2 = Worker2 {
            data : Rc::clone(&result_cell)
        };
        let consumers : Vec<Box<Consumer>> = vec![Box::new(worker1), Box::new(worker2)];
        let mut gosper = GosperCombination::new(data, k);
        let timer = Instant::now();
        let mut counter = 0;

        while let Some(_) = gosper.next_into_cell(&result_cell) {
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
            let mut cart = CartesianProduct::new(data);
            while let Some(_) = cart.next_into_cell(&cur_result) {
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
        let k = 7;
        let data : &[&[i32]]= &[&[1, 2, 3], &[4, 5], &[6, 7, 8, 9, 10], &[11, 12, 13, 14, 15, 16]];
        let result = vec![&data[0][0]; k];
        let result_sync = Arc::new(RwLock::new(result));

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
        let (main_send, main_recv) = mpsc::sync_channel(0);
        let t1_local = main_send.clone();
        let t1_dat = Arc::clone(&result_sync);
        thread::spawn(move || {
            while let Some(_) = t1_recv.recv().unwrap() {
                let result : &Vec<&i32> = &*t1_dat.read().unwrap();
                // println!("Thread1: {:?}", result);
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
                let result : &Vec<&i32> = &*t2_dat.read().unwrap();
                // println!("Thread2: {:?}", result);
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
    fn test_shared_CartesianProduct_result_sync_fn() {
        let k = 7;
        let data : &[&[i32]]= &[&[1, 2, 3], &[4, 5], &[6, 7, 8, 9, 10], &[11, 12, 13, 14, 15, 16]];
        let result = vec![&data[0][0]; k];
        let result_sync = Arc::new(RwLock::new(result));

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
        let t1_dat = Arc::clone(&result_sync);
        thread::spawn(move || {
            while let Some(_) = t1_recv.recv().unwrap() {
                let result : &Vec<&i32> = &*t1_dat.read().unwrap();
                // println!("Thread1: {:?}", result);
            }
            println!("Thread1 is done");
        });

        // worker thread 2
        let (t2_send, t2_recv) = mpsc::sync_channel::<Option<()>>(0);
        let t2_dat = Arc::clone(&result_sync);
        thread::spawn(move || {
            while let Some(_) = t2_recv.recv().unwrap() {
                let result : &Vec<&i32> = &*t2_dat.read().unwrap();
                // println!("Thread2: {:?}", result);
            }
            println!("Thread2 is done");
        });

        let consumers = vec![t1_send, t2_send];
        // main thread that generate result
        thread::spawn(move || {
            use std::time::Instant;
            let cart = CartesianProduct::new(data);
            let mut counter = 0;
            let timer = Instant::now();
            
            cart.into_iter().for_each(|p| {
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
            k_permutation_cell(data, k, cur_result, || {
                consumers.iter().for_each(|c| {
                    c.consume();
                })
            });
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
        
        let mut kperm = KPermutation::new(data, k);
        while let Some(_) = kperm.next_into_cell(&shared) {
            consumers.iter().for_each(|c| {c.consume();});
        }
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
        let k = 5;
        let data = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let result = vec![&data[0]; k];
        let result_sync = Arc::new(RwLock::new(result));

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<()>>(0);
        let (main_send, main_recv) = mpsc::sync_channel(0);
        let t1_local = main_send.clone();
        let t1_dat = Arc::clone(&result_sync);
        thread::spawn(move || {
            while let Some(_) = t1_recv.recv().unwrap() {
                let result : &Vec<&i32> = &*t1_dat.read().unwrap();
                // println!("Thread1: {:?}", result);
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
                let result : &Vec<&i32> = &*t2_dat.read().unwrap();
                // println!("Thread2: {:?}", result);
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
        let k = 5;
        let data : &[i32] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        // workter thread 1
        let (t1_send, t1_recv) = mpsc::sync_channel::<Option<Vec<&i32>>>(0);

        thread::spawn(move || {
            while let Some(c) = t1_recv.recv().unwrap() {
                let result : Vec<&i32> = c;
                // println!("Thread1: {:?}", result);
            }
            println!("Thread1 is done");
        });

        // worker thread 2
        let (t2_send, t2_recv) = mpsc::sync_channel::<Option<Vec<&i32>>>(0);
        thread::spawn(move || {
            while let Some(c) = t2_recv.recv().unwrap() {
                let result : Vec<&i32> = c;
                // println!("Thread2: {:?}", result);
            }
            println!("Thread2 is done");
        });

        let channels = vec![t1_send, t2_send];
        // main thread that generate result
        thread::spawn(move || {
            use std::time::Instant;
            let timer = Instant::now();
            let mut counter = 0;
            let kperm = KPermutation::new(data, k);
            
            kperm.into_iter().for_each(|c| {
                channels.iter().for_each(|t| {t.send(Some(c.to_owned())).unwrap();});
                counter += 1;
            });
            channels.iter().for_each(|t| {t.send(None).unwrap()});
            println!("Done {} combinations in {:?}", counter, timer.elapsed());
        }).join().unwrap();
    }

    #[test]
    fn test_unsafe_cartesian_product() {
        use std::time::Instant;
        let set = (1..14).map(|item| item).collect::<Vec<u64>>();
        let mut data = Vec::<&[u64]>::new();
        for _ in 0..7 {
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
        let data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
        let k = 8;
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
}