# Permutator
It provides multiple way to get permutation of data.
## TLDR
Easiest generic use case
```Rust
use permutator::{CartesianProduct, Combination, Permutation};
let domains : &[&[i32]] = &[&[1, 2], &[3, 4, 5], &[6], &[7, 8], &[9, 10, 11]];
domains.cart_prod().for_each(|cp| {
    // each cp will be &[&i32] with length equals to domains.len() which in this case 5

    // It's k-permutation of size 3 over data.
    cp.combination(3).for_each(|mut c| { // need mut
        // each `c` is not &[&&i32]
        // print the first 3-combination over data
        println!("{:?}", c);

        // start permute the 3-combination
        c.permutation().for_each(|p| {
            // each `p` is not &[&&&i32]
            // print each permutation of the 3-combination.
            println!("{:?}", p);
        });

        // It'll print the last 3-permutation again because permutation permute the value in place.
        println!("{:?}", c);
    })
});
```
Notice that each nested level get deeper reference.
If such behavior is undesired, use `copy` module.
Here's an example:
```Rust
use permutator::copy::{CartesianProduct, Combination, Permutation};
let domains : &[&[i32]] = &[&[1, 2], &[3, 4, 5], &[6], &[7, 8], &[9, 10, 11]];
domains.cart_prod().for_each(|cp| {
    // each cp will be &[i32] with length equals to domains.len() which in this case 5

    // It's k-permutation of size 3 over data.
    cp.combination(3).for_each(|mut c| { // need mut
        // each `c` is not &[i32]
        // print the first 3-combination over data
        println!("{:?}", c);

        // start permute the 3-combination
        c.permutation().for_each(|p| {
            // each `p` is not &[i32]
            // print each permutation of the 3-combination.
            println!("{:?}", p);
        });

        // It'll print the last 3-permutation again because permutation permute the value in place.
        println!("{:?}", c);
    })
});
```
## The `copy` module
This crate split into two modules. One is root module which can be used in most of the case. Another is `copy` module which require that the type implement `Copy` trait. The root module return value as a collection of `&T`, except all Heap permutaiton family. The `copy` module always return value as a collection of `T`. There's no Heap permutation function in `copy` module because it did permutation in place. There's no copy nor create any reference.
### Note
All heap permutation iterators are also in "copy" module. This is because `K-Permutation` iterator family depends on `HeapPermutation` iterator family but `HeapPermutation` iterator family in root module doesn't require `T` to implement `Copy` trait while `K-Permutation` iterator family require `T` to implement `Copy` trait. However, both `copy` and root module do exactly the same operation. There's no copy nor borrow operation as the algorithm itself do permutation in place.
## Get a permutation at specific point, not an iterator style.
It crate provides 2 functions to get a cartesian product or k-permutation:
- get_cartesian_for
- get_permutation_for
It perform mathematically calculation and return the result at that position. It doesn't skip the iteration. It useful when the domains is very large. Otherwise, simply skip the iteration may be faster. For example, in uncontrol test environment, heap_permutation function compile with --release flag can permute about 88 million permutations per second.

This crate also provides utilities functions like:
- get_cartesian_size
- get_permutation_size
## Get a cartesian product over a set itself multiple times
There are two distinct implementation to get cartesian product.
- Iterator that return product
- Function that call callback function to return product
### Iterator 
This crate provides `SelfCartesianProductIterator`, `SelfCartesianProductCellIter`, and `SelfCartesianProductRefIter` structs that implement `Iterator`, `IteratorReset`, `ExactSizeIterator` traits. Each struct serves different use cases:-
- `SelfCartesianProductIterator` can be used in any case that performance is least concern.
- `SelfCartesianProductCellIter` can be used in case performance is important as well as safety.
- `SelfCartesianProductRefIter` can be used in case performance is critical and safety will be handle by caller.
Every structs implements `IteratorReset` trait.
- use `reset` function instead of creating a new Iterator everytime you need to re-iterate.
### Trait
This crate provides `CartesianProduct` trait in both root module and `copy` module which add function `cart_prod` that return an Iterator to generate a `Cartesian Product` over a set itself multiple times. The types that currently support are:
- `(&'a [T], usize)` - Generate cartesian product over 'first paramter' for 'second paramater' times.
- `(&'a [T], usize, Rc<RefCell<&'a mut [&'a T]>>)` - Similar to above but keep overwrite the product into 'third parameter'. **This type require trait from root module.**
- `(&'a [T], usize, *mut [&'a T])` - Similar to above but use unsafe pointer to store value. **This type require trait from root module.** Each type above return different Iterator. For example `(&'a [T], usize)` return `SelfCartesianProductIterator` but on `(&'a [T], usize, *mut [&'a T])` return `SelfCartesianProductRefIter`.
- `(&'a [T], usize, Rc<RefCell<&'a mut [T]>>)` - Similar to above but keep overwrite the product into 'third parameter'. **This type require trait from `copy` module.**
- `(&'a [T], usize, *mut [T])` - Similar to above but use unsafe pointer to store value. **This type require trait from `copy` module.**
Each type above return different Iterator. For example `(&'a [T], usize)` return `copy::SelfCartesianProductIterator` but on `(&'a [T], usize, *mut [T])` return `copy::SelfCartesianProductRefIter`.
### Callback function
This crate provides 4 functions that serve different usecase.
- `self_cartesian_product` function that return product as callback parameter
- `self_cartesian_product_cell` function that return product into Rc<RefCell<>> given in function parameter
- `self_cartesian_product_sync` function that return product into Arc<RwLock<>> given in function parameter
- `unsafe_self_cartesian_product` unsafe function that return product into mutable pointer given in function parameter
## Get a cartesian product over multiple sets
There are three distinct implementation to get cartesian product.
- Iterator that return product
- Function that call callback function to return product
- `CartesianProduct` trait that add `cart_prod` function to `&[&[T]]`, `(&[&[T]], Rc<RefCell<&mut[&T]>>)`
### Iterator 
This crate provides `CartesianProductIterator`, `CartesianProductCellIter`, and `CartesianProductRefIter` structs that implement
`Iterator`, `IteratorReset`, `ExactSizeIterator` traits. Each struct serves different use cases:-
- `CartesianProductIterator` can be used in any case that performance is least concern.
- `CartesianProductCellIter` can be used in case performance is important as well as safety.
- `CartesianProductRefIter` can be used in case performance is critical and safety will be handle by caller.
Every structs implements `IteratorReset` trait.
- use `reset` function instead of creating a new Iterator everytime you need to re-iterate.
### Trait
This crate provides `CartesianProduct` trait in both root module and `copy` module. It is implemented on various types such as generic slice of slices, generic Vec of slices, tuple of `(&'a [&'a [T]], Rc<RefCell<&'a mut[&'a T]>>)`, and tuple of `(&'a [&'a [T]], *mut [&'a T])`.
It add `cart_prod()` function to it and return required iterator based on type of data. For example on generic Vec of slices return `CartesianProductIterator` but on `(&'a [&'a [T]], *mut [&'a T])` return `CartesianProductRefIter`.
### Callback function
This crate provides 4 similar functions on 2 modules that serve different usecase.
These 4 functions in root module:
- `cartesian_product` function that return product as callback parameter
- `cartesian_product_cell` function that return product into `Rc<RefCell<>>` given in function parameter
- `cartesian_product_sync` function that return product into `Arc<RwLock<>>` given in function parameter
- `unsafe_cartesian_product` unsafe function that return product into mutable pointer given in function 
and all 4 functions in `copy` module which do exactly the same except that each element is `T` rather than `&T`
## Get a combination from data
There are three distinct implementation to get k-combinations of n set.
- Iterator that return each combination on each iteration
- Trait that add function to slice, `Vec`, `Rc<RefCell<&mut[&T]>>`, etc.
- Function that call callback function to return product
### Iterator
This crate provides `LargeCombinationIterator`, `LargeCombinationCellIter`, and `LargeCombinationRefIter` structs in two modules that implement `Iterator`, `IteratorReset`, and `ExactSizeIterator` traits. Each struct serves different use cases:-
- `LargeCombinationIterator` can be used in any case that performance is least concern.
- `LargeCombinationCellIter` can be used in case performance is important as well as safety.
- `LargeCombinationRefIter` can be used in case performance is critical and safety will be handle by caller.
All 3 structs in two modules are only different on the return type. The root module has `&T` element in result while `copy` module has copied `T` element in result.
Every structs implements `IteratorReset` trait.
- use `reset` function instead of creating a new Iterator everytime you need to re-iterate.
### Trait
This crate provides `Combination` trait in both root module and `copy` module. It provides basic implementation on various types such as generic slice, generic `Vec`, tuple of `(&'a [T], Rc<RefCell<&'a mut[&'a T]>>)`, and tuple of `(&'a [T], * mut[&'a T])`.
It add `combination(usize)` function to it and return required iterator based on type of data. For example on generic Vec return `LargeCombinationIterator` but on `(&'a [T], * mut[&'a T])` return `LargeCombinationRefIter`.
### Callback function
This crate provide 4 functions in 2 modules that serve different usecase.
- `large_combination` function that return product as callback parameter
- `large_combination_cell` function that return product into `Rc<RefCell<>>` given in function parameter
- `large_combination_sync` function that return product into `Arc<RwLock<>>` given in function parameter
- `unsafe_large_combination` unsafe function that return product into mutable pointer given in function parameter
The different between root module and `copy` module is that the product contains `&T` in root module while in `copy` module contains copied `T`.
## Get a permutation from data
There are three distinct implementation to get permutation.
- Iterator that do permutation on data
- Trait that add function to slice, Vec, etc.
- Function that call callback function to return each permutation
### Iterator
This crate provides `HeapPermutationIterator`, `HeapPermutationCellIter`, and `HeapPermutationRefIter` structs in both root module and `copy` module that implement `Iterator`, `IteratorReset`, `ExactSizeIterator` traits. Each struct serves different use cases:-
- `HeapPermutationIterator` can be used in any case that performance is least concern.
- `HeapPermutationCellIter` can be used in case performance is important as well as safety.
- `HeapPermutationRefIter` can be used in case performance is critical and safety will be handle by caller.
The only different between root module and `copy` module is that in `copy` module type `T` need to implement `Copy` trait.
Every structs implements `IteratorReset` trait.
- use `reset` function instead of creating a new Iterator everytime you need to re-iterate.
### Trait
This crate provides `Permutation` trait in root module and `copy` module. It provide basic implementation various types such as generic slice, generic Vec, tuple of `(&'a mut[T], Rc<RefCell<&'a mut[T]>>`, and more type but used for [k-permutation](#get-a-k-permutation-from-data).
It add `permutation()` function to it and return required iterator based on type of data. For example on generic Vec return `HeapPermutationIterator` but on `(&'a mut [T], Rc<RefCell<&'a mut[T]>>)` return `HeapPermutationCellIter`.
### Callback function
This crate provide 3 functions in root module that serve different usecase.
- `heap_permutation` function that return product as callback parameter
- `heap_permutation_cell` function that return product into Rc<RefCell<>> given in function parameter
- `heap_permutation_sync` function that return product into Arc<RwLock<>> given in function parameter
**There is no heap permutation function family in `copy` module.**
## Get a k-permutation from data
There are three implementation to get k-permutations.
- Iterator that return product
- Trait that add functionality to some specific tuple.
- Function that call callback function to return product
### Iterator
This crate provides `KPermutationIterator`, `KPermutationCellIter`, and `KPermutationRefIter` structs in root module and `copy` module that implement `Iterator`, `IteratorReset`, `ExactSizeIterator` traits. Each struct serves different use cases:-
- `KPermutationIterator` can be used in any case that performance is least concern.
- `KPermutationCellIter` can be used in case performance is important as well as safety.
- `KPermutationRefIter` can be used in case performance is critical and safety will be handle by caller.
The different between root module produces collection of `&T` but `copy` module produces collection of copied `T`
Every structs implements `IteratorReset` trait.
- use `reset` function instead of creating a new Iterator everytime you need to re-iterate.
### Trait
This crate provides `Permutation` trait in root module that can be used to perform k-permutation on tuple of `(&'a [T], usize)`, tuple of `(&'a [T], usize, Rc<RefCell<&'a mut [&'a T]>>)`, and `(&'a [T], usize, *mut [&'a T])` to create different type of iterator.
The `Permutation` trait in `copy` module can be used to perform k-permutation on tuple of `(&'a [T], usize)`, tuple of `(&'a [T], usize, Rc<RefCell<&'a mut [T]>>)`, and `(&'a [T], usize, *mut [T])` to create different type of iterator.
It add `permutation()` function to it and return required iterator based on type of data. For example on (&'a [T], usize) return `KPermutationIterator` but on `(&'a [T], usize, *mut [&'a T])` return `KPermutationRefIter`.
### Callback function
This crate provide 4 functions in both root module and `copy` module that serve different usecase.
- `k_permutation` function that return product as callback parameter
- `k_permutation_cell` function that return product into Rc<RefCell<>> given in function parameter
- `k_permutation_sync` function that return product into Arc<RwLock<>> given in function parameter
- `unsafe_k_permutation` unsafe function that return product into mutable pointer given in function parameter
The different between root module and `copy` module is that the root module return a collection of `&T` while the `copy` module return collection of `T`
## Notes
### Struct with `RefIter` and `CellIter` suffix return empty Item on each Iteration
Struct like `CartesianProductIterator`, `CombinationIterator`, `HeapPermutationIterator`, `KPermutationIterator` return fresh new Vec on each iteration. All other structs that have other way to return value will return empty tuple on each iteration. For example, `CartesianProductCellIter`, `CombinationRefIter`, `HeapPermutationCellIter`, and `KPermutationRefIter` all return empty tuple on each iteration. It return result via parameter specified when instantiate an object. For example, method `new` on `CartesianProductCellIter` in root module requires `Rc<RefCell<&mut [&T]>>` parameter which will be used to store each cartesian product from each iteration.
It's important to keep in mind that these struct with suffix `RefIter` and `CellIter` **overwrite** the result of previous iteration on every iteration. If every result from each iteration need to be kept, consider using non-suffix version. For example, instead of using `KPermutationRefIter` and clone/copy every result into Vec, consider using `KPermutationIterator` instead.
### Performance concern
- For primitive data type, module `copy` and root module performance is roughly equivalent.
- For complex data type, module `copy` performance will depend on the implementation of `Copy` trait.
- Generally speaking, the standard callback function give highest throughput but the return result is a borrowed data with lifetime valid only in that callback scope.
- The crate provides three built-in methods to share result.
    1. callback function with "_cell" suffix.
    2. A struct with `CellIter` and `RefIter` suffix.
    3. Iterator that return an owned value.
The callback with "_cell" suffix way is about 10%-20% slower than using `CellIter` suffix method.
The return owned value method is slowest but most versatile. It's about 700%-1000% slower than using
`CellIter` suffix object. However, it is still faster than using standard callback function then
convert it to owned value to share result.
- This crate provides two built-in methods to send result to other threads.
    1. callback function with "_sync" suffix.
    2. Iterator that return an owned value.
The fastest and safest way to send result to other threads is to use an Iterator that return owned value. It's about 50%-200% faster than using callback function with "_sync" suffix.
### Mutating result is dangerous
Most of sharing result use interior mutability so that the function/struct only borrow the sharing result. It'll mutably borrow only when it's going to mutate result and drop the borrow immediately before calling a callback or return result from iteration. This mean that the result is also mutable on user side. However, doing so may result in undesired behavior. For example: `heap_permutation_cell` function swap a pair of element inside `Rc<RefCell<>>` in place. If user swap value inside result, some permutation return in the future may duplicate with the already return one. If user remove some value inside result, it'll panic because inside the `heap_permutation_cell` function unrecognize the size changed.
### Send result to other thread is complicated
This crate provides two built-in methods to send result across thread. The two usecase is strongly
against each other in term of performance. The callback with "_sync" suffix store borrowed result into Arc<RwLock<>> which reduce the cost of allocating additional memory and copy/clone the result into it. Each thread that read borrowed content may need additional overhead of communication especially if it cannot miss any of the data send to it. In such case, the following scenario is applied
1. The function generate new result
2. The function send notification via channel to every threads that new result is available.
3. The function block until every thread send notification back that they are all done with the data.

Another way is to use Iterator that return an owned value then clone that value on each thread.
This is much simpler to implement but require more memory. It'll simplify the scenario above to:
1. The iterator return new result.
2. It send notification with new data via channel to every threads.
The performance observed in uncontrolled test environment show that the iterator way
is faster than the callback by at least 50%.
### Unsafe way is fastest and hardest
It's because all "unsafe_" prefix function and struct with `RefIter` suffix return result throught mutable pointer that make it has lowest cost to send result back. It leave everything else to user to do the work. To use it, make sure that the memory is return when it no longer use, synchronization, initialization is properly done. The original variable owner outlive both user and generator.
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
## Cartesian product of multiple sets of data
To get cartesian product from 3 set of data.
```Rust
    use permutator::cartesian_product;

    cartesian_product(&[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]], |product| {
        println!("{:?}", product);
    });
```
Or do it in iterative style
```Rust
    use permutator::CartesianProductIterator
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
```
Import trait then skipping all object instantiation altogether.
```Rust
    use std::time::Instant;
    use permutator::CartesianProduct;
    let data : &[&[usize]] = &[&[1, 2], &[3, 4, 5, 6], &[7, 8, 9]];
    let mut counter = 0;
    let timer = Instant::now();

    data.cart_prod.for_each(|p| {
        // println!("{:?}", p);
        counter += 1;
    });

    assert_eq!(data.iter().fold(1, |cum, domain| {cum * domain.len()}), counter);
    println!("Total {} products done in {:?}", counter, timer.elapsed());
```
## Combination Iterator examples
The struct offer two ways to get a combination. 
First it can be used as Iterator. Second
manually call next with borrowed mut variable that
will store the next combination.
```Rust
// Combination iterator
use permutator::LargeCombinationIterator;
use std::time::{Instant};
let data = [1, 2, 3, 4, 5];
let combinations = LargeCombinationIterator::new(&data, 3);
let mut counter = 0;
let timer = Instant::now();

for combination in combinations {
    // uncomment a line below to print each combination
    println!("{}:{:?}", counter, combination);
    counter += 1;
}

println!("Total {} combinations in {:?}", counter, timer.elapsed());
```
```Rust
use permutator::Combination;
use std::time::{Instant};

let data = [1, 2, 3, 4, 5];
let mut counter = 0;

let timer = Instant::now();

data.combination(3).for_each(|combination| {
    // uncomment a line below to print each combination
    println!("{}:{:?}", counter, combination);
    counter += 1;
}

println!("Total {} combinations in {:?}", counter, timer.elapsed());
```
## Iterator style permutation example
There's `HeapPermutationIterator` and `KPermutationIterator` struct that can do 
permutation. Below is an example of `HeapPermutationIterator`.
```Rust
use permutator::HeapPermutationIterator;
use std::time::{Instant};
let data = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
println!("0:{:?}", data);
let mut permutator = HeapPermutationIterator::new(data);
let timer = Instant::now();
let mut counter = 1;

for permutated in permutator {
    println!("{}:{:?}", counter, permutated);
    counter += 1;
}

// or use iterator related functional approach like line below.
// permutator.into_iter().for_each(|permutated| {counter += 1;});

println!("Done {} permutations in {:?}", counter, timer.elapsed());
```
## Iterator into Rc<RefCell<>>
There's `HeapPermutationCellIter` and `KPermutationCellIter` struct that offer
such functionality. Below is an example of `HeapPermutationCellIter`
```Rust
use permutator::HeapPermutationCellIter;
use std::cell::RefCell;
use std::rc::Rc;
use std::time::{Instant};

let data = &mut [1, 2, 3, 4];
let result = Rc::new(RefCell::new(data));
// print original data before permutation
println!("0:{:?}", &*result.borrow());
let mut permutator = HeapPermutationCellIter::new(Rc::clone(&result));
let timer = Instant::now();
let mut counter = 1;

for _ in permutator {
    // uncomment the line below to print all possible permutation
    println!("{}:{:?}", counter, &*result.borrow());
    counter += 1;
}

println!("Done {} permutations in {:?}", counter, timer.elapsed());
```
The `KPermutationCellIter` example show below
```Rust
use permutator::KPermutationCellIter;
use std::cell::RefCell;
use std::rc::Rc;

let k = 3;
let data = &[1, 2, 3, 4, 5];
let mut result = vec![&data[0]; k];
let shared = Rc::new(RefCell::new(result.as_mut_slice()));

let mut kperm = KPermutationCellIter::new(data, k, Rc::clone(&shared));
for _ in kperm {
    // each permutation will be stored in `shared`
    println!("{:?}", &*shared.borrow());
}
```
## Traits that add new function to various types
`CartesianProduct` trait add `cart_prod` function.
The function take no parameter. The function return the same Iterator that also return by 
the [provided struct](#iterator)
so it can be used like [this example](#cartesian-product-of-multiple-sets-of-data)
```Rust
use permutator::CartesianProduct;
let data : &[&[i32]]= &[&[1, 2, 3], &[4, 5]];

data.cart_prod().for_each(|p| {
    // print all product like [1, 4], [1, 5], ...
    println!("{:?}", p);
});
```
or
```Rust
use permutator::CartesianProduct;
let data : &[&[i32]]= &[&[1, 2, 3], &[4, 5]];
let mut result = vec![&data[0][0]; data.len()];
let shared = Rc::new(RefCell::new(result.as_mut_slice()));
// shared can be owned by anyone who want to get cartesian product.
(&data, Rc::clone(&shared)).cart_prod().for_each(|_| {
    // print all product like [1, 4], [1, 5], ...
    println!("{:?}", &*shared.borrow());
    // and notify all owner of shared object so they know that new product is available.
});
```
`Combination` trait add `combination` function.
The function take 1 parameter. It's a size of combination frame, AKA `k`, `r`, etc.
The function return the same Iterator that also return by 
the [provided struct](#iterator-1)
so it can be used like [this example](#combination-iterator-examples)
```Rust
use permutator::Combination;
let data = [1, 2, 3, 4, 5];
data.combination(3).for_each(|comb| {
    // print all combination like [1, 2, 3], [1, 2, 4], ...
    println!("{:?}", comb);
});
```
or
```Rust
use permutator::Combination;
let data = [1, 2, 3, 4, 5];
let k = 3;
let mut result = vec![&data[0]; k];
let shared = Rc::new(RefCell::new(result.as_mut_slice()));
// shared can be owned by anyone who want to get combinations.
(&data, Rc::clone(&shared)).combination(k).for_each(|_| {
    // print all combination like [1, 2, 3], [1, 2, 4], ...
    println!("{:?}", &*shared.borrow());
    // and notify all owner of shared object so they know that new combination is available.
});
```
`Permutation` trait add `permutation` function.
It permute the `[T]`, `Vec<T>`, or Rc<RefCell<&mut [T]>> in place. 
The function return the same Iterator that also return by the either
this [provided struct](#iterator-2) or this [provided struct](#iterator-3)
depending on what types does this method is called upon
so it can be used like [this example](#iterator-style-permutation-example)
or [this example](#iterator-into-rcrefcell) or following example:
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
```Rust
use permutator::Permutation;
let mut data = [1, 2, 3];
let shared = Rc::new(RefCell::new(&mut data));
// shared can be owned by anyone that want to get a permutation
Rc::clone(&shared).permutation().for_each(|_| {
    // print all the permutation.
    println!("{:?}", &*shared.borrow());
    // and notify all owner of shared object so they know that new permutation is available.
});
// The same goes as previous example, the data inside shared on every owner will now has last permuted value.
```
or k-permutation into Rc<RefCell<>>
```Rust
use permutator::KPermutationCellIter;
use std::cell::RefCell;
use std::rc::Rc;

let k = 3;
let data = &[1, 2, 3, 4, 5];
let mut result = vec![&data[0]; k];
let shared = Rc::new(RefCell::new(result.as_mut_slice()));

(data, k, Rc::clone(&shared)).permutation().for_each(|_| {
    // each permutation will be stored in `shared`
    println!("{:?}", &*shared.borrow());
});
```
## Unsafe way for faster share result
In some circumstance, the combination result need to be shared but
the safe function don't allow you to share the result except copy/clone
the result for each share. When that's the case, using Iterator may answer
such situation. 

Another approach is to use `CellIer` suffix struct or callback function 
with `_cell` suffix. As long as each iteration doesn't reuse previous
result and result owner treat result as immutable data then it's safe
to use this approach.

Another way, if safety is less concern than performance, there's an 
unsafe side implementation that take a mutable pointer to store result. 
There's more thing to keep in mind than using struct with `CellIter` suffix 
and callback function `_cell` suffix. For example:
1. Pointer need to outlive the entire operation
2. The object that pointer is pointed to need to be release.
3. Result synchronization, both in single and multiple thread(s).
4. ...
5. All other unsafe Rust conditions may applied

Example:
- unsafe callback function
```Rust
    use permutator::unsafe_combination;
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
```
- unsafe Iterator object
```Rust
    use permutator::LargeCombinationRefIter;
    let data = [1, 2, 3, 4, 5];
    let r = 3;
    let mut counter = 0;
    let mut result = vec![&data[0]; r];
    let result_ptr = result.as_mut_slice() as *mut [&usize];

    unsafe {
        let comb = LargeCombinationRefIter::new(&data, r, result_ptr);
        for _ in comb {
            println!("{:?}", result);
            counter += 1;
        });
    }

    assert_eq!(counter, divide_factorial(data.len(), data.len() - r) / factorial(r));
```
## Share with multiple object from callback function
An example showing the built-in feature that save new cartesian product into
Rc<RefCell<>> so it can be easily share to other.
This example use two worker objects that read each cartesian product
and print it.
```Rust
    use std::fmt::Debug;
    use std::rc::Rc;
    use std::cell::RefCell;

    use permutator::cartesian_product_cell;

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
```
## Iterator that send data to other threads
This example generates a k-permutation and send it to multiple threads
by using KPermutation iterator.

The main thread will keep generating a new k-permutation and send it to
every thread while all other threads read new k-permutation via channel.
In this example, it use sync_channel with size 0. It doesn't hold anything
inside the buffer. The sender will block until the receiver read the data.
```Rust
    use permutator::KPermutation;
    use std::sync::mpsc;
    let k = 5;
    let data : &[i32] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // workter thread 1
    let (t1_send, t1_recv) = mpsc::sync_channel::<Option<Vec<&i32>>>(0);

    thread::spawn(move || {
        while let Some(c) = t1_recv.recv().unwrap() {
            let result : Vec<&i32> = c;
            println!("Thread1: {:?}", result);
        }
        println!("Thread1 is done");
    });

    // worker thread 2
    let (t2_send, t2_recv) = mpsc::sync_channel::<Option<Vec<&i32>>>(0);
    thread::spawn(move || {
        while let Some(c) = t2_recv.recv().unwrap() {
            let result : Vec<&i32> = c;
            println!("Thread2: {:?}", result);
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
```
## Callback function send data to other thread
This example generates a k-permutation and send it to multiple threads by
using a callback approach k_permutation_sync function.

The main thread will keep generating a new k-permutation and send it to
every thread while all other threads read new k-permutation via channel.
In this example, it use sync_channel with size 0. It doesn't hold anything
inside the buffer. The sender will block until the receiver read the data.
```Rust
    use std::sync::{Arc, RwLock};
    use std::sync::mpsc;
    use std::sync::mpsc::{Receiver, SyncSender};
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
```
## Breaking change from 0.2.x to 0.3.0
`combination` from root module and `copy` module now return "Large" combination family.
### Rationale
All "Gosper" combination family is supersede by "Large" combination family. It doesn't mark those family deprecated yet. There's only Rust document that state it being deprecated. This is because the reason for being deprecated is that the implementation in this crate is inefficient. Each time that gosper algorithm generate new value, it copied all value or create new ref for that combination. In contrast to "Large" family that only copy or create new ref when the combination at that position changed. This make "Large" family combination faster over 10 times. So unless more efficient implementation is available, after sometime, the "Gosper" family function may officially mark deprecated. There's also "Gosper" combination family limitation that it can generate combination as many as bits of variable that support fast bit operation, which Rust currently is capped to 128 bits so source be as large as 128 elements slice. In practical, this is more than enough on most case. But in some edge case, "Large" combination family permit a combination on data as many as `usize` max value, which is 2^32 on 32 bits platform and 2^64 on 64 bits platform. The result from "Large" combination family is lexicographic ordered if the source is lexicographic ordered.

Internally, k-permutation family are all migrated to use "Large" combination family instead of "Gosper" family.
## Migration guide from 0.2.x to 0.3.0
- `combination*` functions become `large_combination*` functions.
- `GosperCombination*` structs become `LargeCombination*` structs.
For example:
```Rust
    // This line will be error in 0.3.0
    let combinations : GosperCombinationIterator = [1, 2, 3, 4, 5].combination(3);
```
Become
```Rust
    let combinations : LargeCombinationIterator = [1, 2, 3, 4, 5].combination(3);
```
## Breaking change from 0.1.6 to 0.2.0
Version 0.2.0 has major overhaul on entire crate to make use case more consistent on each other functionalities. There are now only 2 major distinct styles. 1. Callback function 2. Iterator object. The Iterator object has 2 sub-style. 1. Plain `Iterator` style. 2. Shared `Iterator` style. The shared `Iterator` style has both safe and unsafe kind of share which is similar to callback style counterpart. It need to rename every structs. It add one more trait and some more types.
More detail on breaking change:
- An iterator style `next_into_cell` has been refactored into their own struct. Now it can be used like simple Iterator with slightly different way to return value.
- A mimic iterator style `next` that took `&mut[&T]` parameter has been refactored into their own struct. Now it can be used like simple Iterator with slightly different way to return value.
- `CartesianProduct` struct is renamed to `CartesianProductIterator`
- `HeapPermutation` struct is renamed to `HeapPermutationIterator`
- `GosperCombination` struct is renamed to `GosperCombinationIterator`
- `KPermutation` struct is renamed to `KPermutationIterator`
- `Combination` and `Permutation` traits now use associated type `combinator` and `permutator` respectively to define the struct that will be used to perform combination/permutation on slice/array/Vec and Rc<RefCell<&mut [T]>> instead of fixed return type. Now, all trait return an object that implement `Iterator` trait. It doesn't constrait the associated type `Item` defined in `Iterator` thought. The trait now take <'a> lifetime parameter and no longer take generic type `T`. The `combination` function change signature from `combination(&mut self)` to `combination(&'a mut self)`. The `permutation` function change signature from `permutation(&mut self)` to `permutation(&'a mut self)`.
## Migration guide from 0.1.6 to 0.2.0
- The mimic iterator style function now moved into it own iterator struct that have suffix "RefIter" in its' name. All of its become `unsafe` to use. Following is the list of such structs.
    - CartesianProductRefIter
    - CombinationRefIter
    - GosperCombinationRefIter
    - HeapPermutationRefIter
    - KPermutationRefIter
- All `next_into_cell` function now moved into it own iterator struct that have suffix "CellIter" in its' name. Following is the list of such structs.
    - CartesianProductCellIter
    - CombinationCellIter
    - GosperCombinationCellIter
    - HeapPermutationCellIter
    - KPermutationCellIter
- Rename all structs. Following is the renamed structs.
    - `CartesianProduct` struct is renamed to `CartesianProductIterator`
    - `HeapPermutation` struct is renamed to `HeapPermutationIterator`
    - `GosperCombination` struct is renamed to `GosperCombinationIterator`
    - `KPermutation` struct is renamed to `KPermutationIterator`
- Any implementation on other type for `Combination` and `Permutation` traits need to define the associated type as well as change `combination` and `permutation` function signature from taking `&self` to `&'a self` and `&mut self` to `&'a mut self` respectively.

Example:
New `Permutation` trait now look like this.
```Rust
// instead of this old implementation
// impl Permutation<T> for [T] {
//     fn permutation(&mut self) -> HeapPermutation<T> {
//          HeapPermutation {
//              c : vec![0; self.len],
//              data : self,
//              i : 0
//          }
//     }
// }
// now it become..
impl<'a, T> Permutation<'a> for [T] where T : 'a {
    type Permutator = HeapPermutation<'a, T>; // This struct implement `Iterator`

    fn permutation(&'a mut self) -> HeapPermutation<T> {
        HeapPermutation {
            c : vec![0; self.len()],
            data : self,
            i : 0
        }
    }
}
```
The added complexity make this trait applicable to wider type.
Here's new implemention on `Rc<RefCell<&mut [T]>>` which return `HeapPermutationCell`.
```Rust
impl<'a, T> Permutation<'a> for Rc<RefCell<&'a mut[T]>> where T :'a {
    type Permutator = HeapPermutationCell<'a, T>; // This struct also implement `Iterator`

    fn permutation(&'a mut self) -> HeapPermutationCell<T> {
        HeapPermutationCell {
            c : vec![0; self.borrow().len()],
            data : Rc::clone(self),
            i : 0
        }
    }
}
```