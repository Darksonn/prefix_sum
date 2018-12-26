# Prefix sum

This crate provides an implementation of the [prefix sum data structure][1].

## Usage

The use case of this crate is when you want to find the result of combining a
large number of interval modifications.

Example code:

```rust
use prefix_sum::PrefixSum;

let mut sum = PrefixSum::new(6);
// Each of these operations is O(1).
sum[2..4] += 2;
sum[1..3] += 3;
sum[0]    += 10;
sum[3..]  += 7;

// The build method is O(len).
assert_eq!(vec![10, 3, 5, 9, 7, 7], sum.build());
```

## Cargo.toml

```toml
[dependencies]
prefix_sum = "0.1"
```

  [1]: https://en.wikipedia.org/wiki/Prefix_sum
