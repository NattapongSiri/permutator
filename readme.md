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
## Breaking change from 0.1.6 to 0.2.0
- An iterator style `next_into_cell` has been refactored into `IteratorCell` trait.
- The mimic `next` function that mimic `Iterator` trait implemented for `CartesianProduct` and `KPermutation` struct now borrow a mutable slice to store result instead. It's now consistent to all other Iterator style struct.
- `Permutation` trait now use associated type `permutator` to define the struct that will be used to perform permutation on slice/array/Vec and Rc<RefCell<&mut [T]>> instead of fix return on `HeapPermutation` struct but the type need to implement `Iterator` trait. It doesn't constrait the associated type `Item` defined in `Iterator` thought. The trait now take <'a> lifetime parameter and no longer take generic type `T`. The `permutation` function change signature from `permutation(&mut self)` to `permutation(&'a mut self)`.
## Migration guide from 0.1.6 to 0.2.0
- add `use permutator::IteratorCell;` when you use `next_into_cell` function from any struct in this crate.
- All `next` function that mimic `Iterator` in every struct now borrow a mutable slice to store result except `HeapPermutation` struct that is left untouch. 
- Any implementation on other type for `Permutation` trait need to define the associated type and change `permutation` function signature.

Example:
New `next` function signature
```Rust
    // instead of this
    // while let Some(prod) = cartesian_product_object.next() {
    // }
    // use this
    let result = vec![&data[0][0], data.len()];
    while let Some(_) = cartesian_product_object.next(result.as_mutable_slice()) {
    }
```
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
The added complexity let this trait add applicable to wider type.
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
## Get a permutation at specific point, not an iterator style.
It provides 2 functions to generate a combination.
- get_cartesian_for
- get_permutation_for
It also provide utilities functions like:
- get_cartesian_size
- get_permutation_size
## Get a cartesian product over multiple sets
There are two distinct implementation to get cartesian product.
- Iterator that return product
- Function that call callback function to return product
### Iterator 
This crate provides `CartesianProduct` struct that implement
`Iterator`, `IteratorCell`, `IteratorReset` trait. The struct provide 3 use cases.
- Use Rust builtin `Iterator` functionality.
- Use `next` function that return borrowed result into mutable slice.
- use `next_into_cell` function that return borrowed result into Rc<RefCell<>> of mutable slice.
- use `reset` function instead of creating a new Iterator everytime you need to reiterate.
### Callback function
This crate provides 4 functions that serve different usecase.
- `cartesian_product` function that return product as callback parameter
- `cartesian_product_cell` function that return product into Rc<RefCell<>> given in function parameter
- `cartesian_product_sync` function that return product into Arc<RwLock<>> given in function parameter
- `unsafe_cartesian_product` unsafe function that return product into mutable pointer given in function parameter
## Get a combination from data
There are three distinct implementation to get k-combinations of n set.
- Iterator that return product
- Trait that add function to slice and Vec
- Function that call callback function to return product
### Iterator
This crate provides `GosperCombination` struct that implement
`IntoIterator`, `IteratorCell`, `IteratorReset` trait. The struct provide 3 use cases.
- Use Rust builtin `Iterator` functionality.
- Use `next` function that return borrowed result into mutable slice.
- use `next_into_cell` function that return borrowed result into Rc<RefCell<>> of mutable slice.
- use `reset` function instead of creating a new Iterator everytime you need to reiterate.
### Trait
This crate provides `Combination` trait and basic implementation on generic slice and generic Vec.
It add `combination(usize)` function on the slice and Vec.
### Callback function
This crate provide 4 functions that serve different usecase.
- `combination` function that return product as callback parameter
- `combination_cell` function that return product into Rc<RefCell<>> given in function parameter
- `combination_sync` function that return product into Arc<RwLock<>> given in function parameter
- `unsafe_combination` unsafe function that return product into mutable pointer given in function parameter
## Get a permutation from data
There are three distinct implementation to get permutation.
- Iterator that do permutation on data
- Trait that add function to slice and Vec
- Function that call callback function to return a permutation
### Iterator
This crate provides `HeapPermutation` and `HeapPermutationCell` struct that implement
`Iterator`, `IteratorReset` trait. The struct provide 3 use cases.
- Use Rust builtin `Iterator` functionality from `HeapPermutation` or
Clone Rc<RefCell<&mut [T]>> then construct `HeapPermutationCell` and 
on each iteration of `HeapPermutationCell`, the cloned one will have
the permutated value inside it.
- Use `next` function from `HeapPermutation` that return borrowed result in an Option instead of an owned value like typical Iterator.
- use `reset` function instead of creating a new Iterator everytime you need to completely re-permutation again.
### Trait
This crate provides `Permutation` trait and basic implementation on generic slice/array and generic Vec as well as Rc<RefCell<&mut [T]>>. It add `permutation` function on the slice/array, Vec, and
Rc<RefCell<&mut [T]>>. There's some usage different on how to iterate over permutation of slice/array/Vec than Rc<RefCell<&mut [T]>>. See an example of permutation of [slice/array/Vec](#traits-that-add-new-function-to-t-or-vect) and [Rc<RefCell<&mut [T]>>]
### Callback function
This crate provide 3 functions that serve different usecase.
- `heap_permutation` function that return product as callback parameter
- `heap_permutation_cell` function that return product into Rc<RefCell<>> given in function parameter
- `heap_permutation_sync` function that return product into Arc<RwLock<>> given in function parameter
## Get a k-permutation from data
There are two distinct implementation to get k-permutations of n set.
- Iterator that return product
- Function that call callback function to return product
### Iterator
This crate provides `KPermutation` struct that implement
`Iterator`, `IteratorCell`, `IteratorReset` trait. The struct provide 3 use cases.
- Use Rust builtin `Iterator` functionality.
- Use `next` function that return borrowed result into mutable slice.
- use `next_into_cell` function that return borrowed result into Rc<RefCell<>> of mutable slice.
- use `reset` function instead of creating a new Iterator everytime you need to reiterate.
### Callback function
This crate provide 4 functions that serve different usecase.
- `k_permutation` function that return product as callback parameter
- `k_permutation_cell` function that return product into Rc<RefCell<>> given in function parameter
- `k_permutation_sync` function that return product into Arc<RwLock<>> given in function parameter
- `unsafe_k_permutation` unsafe function that return product into mutable pointer given in function parameter
## Notes
### HeapPermutation struct has inconsistent `next` function design than other
HeapPermutation struct provide two `next` functions.
One is conform to `Iterator` trait. Another is just a mimic to `Iterator` but return
a reference instead of an owned value. However, the way it return value is different 
comparing to all other struct in this crate. This is because the permutation is done
in place. This struct borrow mutable slice of data. If it take another `result` of
borrowed mutable slice again then it'll leave the borrowed data given on constructor
untouch and keep mutating the function parameter `result` instead. And since this 
struct borrow a mutable slice already, the same mutable slice cannot be mutable borrow
again in each next call. Thus, require user to duplicate data, one into constructor which
will be leave untouch, another into each next call.

To make it simpler and cleaner, the `next` function that mimic `Iterator` will not
borrow mutable slice like all other struct in this crate but return a result through
Option that return from function. 
### Performance concern
- Generally speaking, the standard callback function give highest throughput but the return result is a borrowed data with lifetime valid only in that callback scope.
- The crate provides three built-in methods to share result.
    1. callback function with "_cell" suffix.
    2. An object method "next_into_cell"
    3. Iterator that return an owned value.
The callback with "_cell" suffix way is about 10%-20% slower than using "next_into_cell" method.
The return owned value method is slowest but most versatile. It's about 1,000% slower than using
"next_into_cell" method. However, it is still faster than using standard callback function then
convert it to owned value to share result.
- This crate provides two built-in methods to send result to other threads.
    1. callback function with "_sync" suffix.
    2. Iterator that return an owned value.
The fastest and safest way to send result to other threads is to use an Iterator that return
owned value. It's about 50%-200% faster than using callback function.
### Mutating result is dangerous
Most of sharing result use interior mutability so that the function/struct only borrow the
sharing result. It'll mutably borrow only when it's going to mutate result and drop the mutable
borrow immediately before calling a callback or return result from iteration. 
This mean that the result is also mutable on user side. However, doing so may result in undesired
behavior. For example: heap_permutation_cell function swap a pair of element inside Rc<RefCell<>>
in place. If user swap value inside result, some permutation return in the future may duplicate with
the already return one. If user remove some value inside result, it'll panic because inside
the heap_permutation_cell function unrecognize the size change.
### Send result to other thread is complicated
This crate provides two built-in methods to send result across thread. The two usecase is strongly
against each other in term of performance.
The callback with "_sync" suffix store borrowed result into Arc<RwLock<>> which reduce the cost
of allocating additional memory and copy/clone the result into it. Each thread that read borrowed
content may need additional overhead of communication especially if it cannot miss any of the data
send to it. In such case, the following scenario is applied
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
It's because all "unsafe_" prefix function return result throught mutable pointer that
make it has lowest cost to send result back. It leave everything else to user to do the work.
To use it, make sure that the memory is return when it no longer use, synchronization, initialization
is properly done. The original variable owner outlive both user and generator.
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
    use permutator::cartesian_product;

    cartesian_product(&[&[1, 2, 3], &[4, 5, 6], &[7, 8, 9]], |product| {
        println!("{:?}", product);
    });
```
Or do it in iterative style
```Rust
    use permutator::CartesianProduct
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
```
Or just mimic an iterator but taking only a reference.
```Rust
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
## Iterator alike sharable permutation example
There's `HeapPermutationCell` and `KPermutation` struct that can do 
permutation like this. Below is an example of `HeapPermutationCell`.
```Rust
use permutator::HeapPermutationCell;
use std::time::{Instant};
let mut data : Vec<String> = (1..=3).map(|num| {format!("some ridiculously long word prefix without any point {}", num)}).collect();
let shared = Rc::new(RefCell::new(data.as_mut_slice()));
let permutator = HeapPermutationCell::new(Rc::clone(&shared));
println!("{}:{:?}", 0, &*shared.borrow()); 
let timer = Instant::now();
let mut counter = 1;

for _ in permutator {
    println!("{}:{:?}", counter, &*shared.borrow());
    counter += 1;
}

println!("Done {} permutations in {:?}", counter, timer.elapsed());
assert_eq!(6, counter);
```
The `KPermutation` example show below
```Rust
let k = 3;
let data = &[1, 2, 3, 4, 5];
let mut result = vec![&data[0]; k];
let shared = Rc::new(RefCell::new(result.as_mut_slice()));

let mut kperm = KPermutation::new(data, k);
while let Some(_) = kperm.next_into_cell(&shared) {
    // each permutation will be stored in `shared`
    println!("{:?}", &*shared.borrow());
}
```
## Traits that add new function to `[T]` or `Vec<T>`
`Combination` trait add `combination` function.
The function take 1 parameter. It's a size of combination frame.
The function return the same Iterator that also return by 
the [provided struct](#iterator-style-permutationscombinations)
so it can be used like [this example](#iterator-alike-sharable-permutation-example)
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
## Traits that add new function to `Rc<RefCell<&mut [T]>>`
`Permutation` trait add `permutation` function to Rc<RefCell<&mut [T]>>.
It permute the `[T]` in place. 
The function return the same Iterator an object of `HeapPermutationCell`
so it can be used like [this example](#iterator-alike-sharable-permutation-example)
```Rust
use permutator::Permutation;
let mut data : &mut [i32] = &mut [1, 2, 3];
let mut shared = Rc::new(RefCell::new(data));
let value = Rc::clone(&shared);
shared.permutation().for_each(|_| {
    // print all the permutation.
    println!("{:?}", &*value.borrow());
});
```
## Unsafe way for faster share result
In some circumstance, the combination result need to be shared but
the safe function don't allow you to share the result except copy/clone
the result for each share. When that's the case, using Iterator may answer
such situation. As long as the Iterator itself live longer than the shared 
result, it's safe to borrow that result to wherever it need. This has lower
cost than using callback function then clone/copy it for each share.
But If safety is less concern than performance, there's an unsafe side 
implementation that take a mutable pointer to store result.
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
## Iterator that produce data for sharing
This crate provide `IteratorCell` trait. 
The trait enforce that the return value need to be put into borrowed Rc<RefCell<>>.
There are 3 struct that implemented this trait.
- CartesianProduct
- KPermutation
- GosperCombination

An example showing the built-in feature that save new k-permutation into
Rc<RefCell<>> so it can be easily share to other.
This example use two worker objects that read each k-permutation
and print it.
```Rust
    use std::fmt::Debug;
    use std::cell::RefCell;
    use std::rc::Rc;

    use permutator::{KPermutation, IteratorCell};

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