# Permutator
It provides different way to get permutation of data.
## TLDR
Easiest generic use case
```Rust
use permutator::{Combination, Permutation};
let data = [1, 2, 3, 4, 5];
// It's k-permutation of size 3 over data.
data.combination(3).for_each(|mut c| { // need mut
    // print the 3 combination over data
    println!("{:?}", c);

    c.permutation().for_each(|p| {
        // print all the permutation of the 3 combination.
        println!("{:?}", p);
    });

    // It'll print the last permutation again because permutation permute the value in place.
    println!("{:?}", c);
});
```
## Get a permutation at specific point, not an iterator style.
It provides 2 functions to generate a combination.
- get_cartesian_for
- get_permutation_for
It also provide utilities functions like:
- get_cartesian_size
- get_permutation_size
## Get a cartesian product over multiple sets
It provides `cartesian_product` function to generate all possible
cartesian product over multiple sets of data.
## Complete permutation over data
### Two function, heap_permutation and k_permutation with callback on each permutation.
It provides `heap_permutation` function to generate all possible permutation
over data. It also provide `k_permutation` function to generate all possible 
k-permutation over given data.
### Iterator style permutations/combinations
It provides 3 structs for this purpose:
- GosperCombination
- HeapPermutation
- KPermutation

All of it has `into_iter` function.
`GosperCombination` implement `IntoIterator` trait.
`HeapPermutation` and `KPermutation` implement `Iterator` trait. 
It can be directly used inside for each loop.
There's a special function `next` inside `HeapPermutation` and
`KPermutation` that mimic `Iterator` by returning an `Option` 
contain the permuted value or return `None` when all the permutations 
are return. The special `next` function doesn't construct 
new Vec on returned value but a reference to internal slice of 
permuted value.
## Trait that added functions to existing type
It provides 2 traits that add function to existing type.
- Combination trait, add combination function to `[T]` and `Vec<T>`
- Permutation trait, add permutation function to `[T]` and `Vec<T>`

# Example
## Get a permutation at specific point examples
To get into 'n' specific lexicographic permutation, 
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
## Cartesian product of multiple sets of data.
To get cartesian product from 3 set of data.
```Rust
    cartesian_product(&[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]], |product| {
        println!("{:?}", product);
    });
```
## Combination Iterator examples
The struct offer two ways to get a combination. 
First it can be used as Iterator. Second
manually call next with borrowed mut variable that
will store the next combination.
```Rust
// Combination iterator
use permutator::GosperCombination;
use std::time::{Instant};
let data = [1, 2, 3, 4, 5];
let gosper = GosperCombination::new(&data, 3);
let mut counter = 0;
let timer = Instant::now();

for combination in gosper {
    // uncomment a line below to print each combination
    // println!("{}:{:?}", counter, combination);
    counter += 1;
}

println!("Total {} combinations in {:?}", counter, timer.elapsed());
```
```Rust
// combination in manual iteration

use permutator::GosperCombination;
use std::time::{Instant};

let combination = vec![&data[0], 3]; // store next combination.
let gosper = GosperCombination::new(&data, 3);
let mut counter = 0;

let timer = Instant::now();

while let Some(_) = gosper.next(&mut combination) {
    // uncomment a line below to print each combination
    // println!("{}:{:?}", counter, combination);
    counter += 1;
}

println!("Total {} combinations in {:?}", counter, timer.elapsed());
```
## Iterator style permutation example
There's `HeapPermutation` and `KPermutation` struct that can do 
permutation. Below is an example of `HeapPermutation`.
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
## Mimic Iterator style permutation example
There's `HeapPermutation` and `KPermutation` struct that offer
such functionality. Below is an example of `HeapPermutation`
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
## Traits that add new function to `[T]` or `Vec<T>`
`Combination` trait add `combination` function.
The function take 1 parameter. It's a size of combination frame.
The function return the same Iterator that also return by 
the [provided struct](#iterator-style-permutationscombinations)
so it can be used like [this example](#combination-iterator-examples)
```Rust
use permutator::Combination;
let data = [1, 2, 3, 4, 5];
data.combination(3).for_each(|comb| {
    // print all combination like [1, 2, 3], [1, 2, 4], ...
    println!("{:?}", comb);
});
```
`Permutation` trait add `permutation` function.
It permute the `[T]` or `Vec<T>` in place. 
The function return the same Iterator that also return by the [provided struct](#iterator-style-permutationscombinations)
so it can be used like [this example](#iterator-style-permutation-example)
or [this example](#mimic-iterator-style-permutation-example)
```Rust
use permutator::Permutation;
let mut data = [1, 2, 3];
data.permutation().for_each(|p| {
    // print all the permutation.
    println!("{:?}", p);
});
// The `data` at this point will also got permuted.
// It'll print the last permuted value twice.
println!("{:?}", data);
```