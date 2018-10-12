//! This crate provide generic permutators.
//! There's a function that can get a combination at any specific point of
//! lexicographic ordered permutation.
//! There's [k-permutation](fn.k_permutation.html) function to generate all possible permutation.
//! There's [KPermutation](struct.KPermutation.html) struct that provide Iterator style to do k-Permutation
//! over data.
//! There's [HeapPermutation](struct.HeapPermutation.html) struct that provide Iterator style permutation
//! iterator.
//! There's a [GosperCombination](struct.GosperCombination.html) struct that provide Iterator style combination
//! iterator.
//! 
//! The simplest usage is call [k_permutation](fn.k_permutation.html) function.

extern crate num;

use num::{PrimInt, Unsigned};
use std::collections::{VecDeque};
use std::iter::{Product};

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

/// Create a cartesian product over give slice. The result will be a slice
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

/// Generate k-permutation over slice of `d`. For example: d = &[1, 2, 3]; k = 2.
/// The result will be [1, 2], [2, 1], [1, 3], [3, 1], [2, 3], [3, 2]
/// 
/// The implementation calculate each combination by using
/// Gospel's algorithm then permute each combination 
/// use Heap's algorithm.
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

/// Heap's permutation in iterator style implementation.
/// It provide two way to iterate over the permutation.
/// - One conform to Iterator trait constraint where each
/// iteration return a moved value. However, Heap's algorithm
/// perform swap in place, it need to clone each permutation 
/// before return.
/// - Another more preferrable way is to manually call `next`
/// on each loop. It mimic Iterator trait style by returning an
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
/// - A much more faster way but has no iterator related functional paradigm is:
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
/// Iterator way. 
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
/// a reference to permuted value stored inside this struct.
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
fn heap_permutation<T>(d : &mut [T], mut cb : impl FnMut(&[T]) -> ()) where T : Clone {
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

#[test]
fn test_cartesian_product() {
    cartesian_product(&[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]], |product| {
        println!("{:?}", product);
    });
}

// #[test]
// fn test_lexicographic_combination() {
//     let mut x = 7;

//     for _ in 0..40 {
//         println!("{:0>8b}", x);
//         stanford_combination(&mut x);
//     }
// }