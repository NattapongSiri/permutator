# Permutator
It provide different way to get permutation of data.
## Get a permutation at specific point, not an iterator style.
It currently provide 2 functions to generate a combination.
- get_cartesian_for
- get_permutation_for
It also provide utilities functions like:
- get_cartesian_size
- get_permutation_size
## Complete permutation over data
### Single function, k-permutation with callback on each permutation.
It provide `k_permutation` function to generate all possible 
k-permutation over given data.
### Iterator style permutations/combinations
It provide 2 structs for this purpose:
- HeapPermutation
- GosperCombination
Both of it has `into_iter` function.
`HeapPermutation` implement `Iterator` trait. It can be directly
used inside for each loop.
GosperCombination implement `IntoIterator` trait.
There's a special function `next` inside HeapPermutation that
mimic `Iterator` by returning an `Option` contain the permuted value
or return `None` when all the permutations are return.
The special `next` function doesn't construct new Vec on returned 
value but a reference to internal slice of permuted value.

# Get a permutation at specific point examples
```Rust
use permutator::get_cartesian_size;

get_cartesian_size(3, 2); // return 9.
get_cartesian_size(3, 3); // return 27.

use permutator::get_cartesian_for;

let nums = [1, 2, 3];
get_cartesian_for(&nums, 2, 0); // Return Ok([1, 1])
get_cartesian_for(&nums, 2, 3); // Return Ok([2, 1])
get_cartesian_for(&nums, 2, 8); // Return Ok([3, 3])
get_cartesian_for(&nums, 2, 9); // Return Err("Parameter `i` is out of bound")
get_cartesian_for(&nums, 4, 0); // Return Err("Parameter `degree` cannot be larger than size of objects")

use permutator::get_permutation_size;

get_permutation_size(3, 2); // return = 6
get_permutation_size(4, 2); // return = 12

use permutator::get_permutation_for;

let nums = [1, 2, 3, 4];
get_permutation_for(&nums, 2, 0); // return Result([1, 2])
get_permutation_for(&nums, 3, 0); // return Result([1, 2, 3])
get_permutation_for(&nums, 2, 5); // return Result([2, 4])
get_permutation_for(&nums, 2, 11); // return Result([4, 3])
get_permutation_for(&nums, 2, 12); // return Err("parameter x is outside a possible length")
get_permutation_for(&nums, 5, 0); // return Err("Insufficient number of object in parameters objects for given parameter degree")
```
# Iterator style permutation example
```Rust
use permutator::HeapPermutation;
use std::time::{Instant};
let data = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
println!("0:{:?}", data);
let mut permutator = HeapPermutation::new(data);
let timer = Instant::now();
let mut counter = 1;

for permutated in permutator {
    // println!("{}:{:?}", counter, permutated);
    counter += 1;
}

// or use iterator related functional approach like line below.
// permutator.into_iter().for_each(|permutated| {counter += 1;});

println!("Done {} permutations in {:?}", counter, timer.elapsed());
```
# Mimic Iterator style permutation example
```Rust
use permutator::HeapPermutation;
use std::time::{Instant};

let data = &mut [1, 2, 3, 4];
// print original data before permutation
// println!("0:{:?}", data);
let mut permutator = HeapPermutation::new(data);
let timer = Instant::now();
let mut counter = 1;

while let Some(permutated) = permutator.next() {
    // uncomment the line below to print all possible permutation
    // println!("{}:{:?}", counter, permutated);
    counter += 1;
}

println!("Done {} permutations in {:?}", counter, timer.elapsed());
```
# Combination Iterator examples
```Rust
// Combination iterator
use permutator::GosperCombination;
use std::time::{Instant};
let gosper = GosperCombination::new(&[1, 2, 3, 4, 5], 3);
let mut counter = 0;
let timer = Instant::now();

for combination in gosper {
    // uncomment a line below to print each combination
    // println!("{}:{:?}", counter, combination);
    counter += 1;
}

println!("Total {} combinations in {:?}", counter, timer.elapsed());
```