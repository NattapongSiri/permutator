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
/// divide_factorial(5, 3); // return 5 * 4 = 20
/// // calculate 3!/5!
/// divide_factorial(3, 5); // return 1.
/// // calculate 5!/5!
/// divide_factorial(5, 5); // return 1.
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
/// multiply_factorial(5, 4); // calculate 4! and power it by 2 then multiply by 5.
/// multiply_factorial(4, 5); // perform similar to above step.
/// multiply_factorial(5, 5); // calculate 5! and power it by 2.
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