# Solving Constrained Horn Clauses Using `shara`

Verifying that a given program satisfies a given _safety property_
(i.e., a property that specifies executions that should not happen)
can be reduced solving a class of logic-programming problems called
_Constrained Horn Clauses_ (CHCs). CHCs can express
safety-verification problems of imperative programs, recursive
programs, some concurrent programs, and functional programs.

`shara` is a CHC solver. It operates purely on CHC systems, and does
not require them to correspond to programs in particular languages, or
particular safety properties.

## Determining satisfiability of a CHC system

For example, consider the following implementation of the Fibonacci
function:
```java
int fib(int n) {
  int i = 2;
  int prev = 1;
  int cur = 1;
  while (i < n) {
    cur = prev + cur;
    prev = cur;
    i++; }
  return cur;
}
```

Proving that `fib` always returns a non-zero value can be reduced to
solving the following CHC system:
```shell
i = 2 /\ prev = cur = 1 => R5(prev, cur, i, n)
R5(n, i, prev, cur), i < n => R5(n, i + 1, cur, prev + cur)
R5(n, i, prev, cur), i >= n => cur != 0
```

where a _solution_ is an interpretation of the _relational predicate
symbol_ `R5` as a formula over variables `n`, `i`, `prev`, and `cur`
such that each of the entailments given above holds. One such solution
interprets `R5` as `prev > 0 /\ cur > 0`.

`shara`, given such a system, reports that it has a solution.

## Determining unsatisfiability of a CHC system

Not every CHC system has a solution. In particular, for program `P`
and property `Q` such that `P` does not satisfy `Q`, any CHC system
that corresponds to the problem of verifying that `P` satisfies `Q`
will not have a solution.

For example, consider the following erroneous implementation of the
Fibonacci function:
```java
int buggy_fib(int n) {
  int i = 2;
  int prev = 0;
  int cur = 0;
  while (i < n) {
    cur = prev + cur;
    prev = cur;
    i++; }
  return cur;
}
```

The corresponding CHC system
```shell
i = 2 /\ prev = cur = 0 => R5(prev, cur, i, n)
R5(n, i, prev, cur), i < n => R5(n, i + 1, cur, prev + cur)
R5(n, i, prev, cur), i >= n => cur != 0
```

has no solution. `shara`, given such a system, reports that it has no
solution.

## Building `shara`

`shara` is implemented as an alternative version of the `z3` automatic
theorem prover.  To build, run the following commands in package's
main directory `SHARA_DIR`:

```shell
$ python scripts/mk_make.py
$ cd build
$ make
```
When successful, the build system generates an implementation

## Using `shara`

`shara`, given a CHC system `S` in SMT2 format, attempts to determine
if `S` has a solution. 

After building `shara` in directory `SHARA_DIR`, to determine if a CHC
system in file `chcs.smt2` has a solution, run the command

```shell
$ SHARA_DIR/z3 chcs.smt2
```

## Implementation

`shara` is implemented as a fork of the `z3` automatic theorem prover
[z3](https://github.com/Z3Prover/z3). It supports an interface
identical to that supported by the interface supported by `z3` 4.5.

The internal behavior of `z3` and `shara` differ only when `shara` is
given a CHC system. The entire implementation of `shara` is
represented by alternative implementations of a solving algorithm used
within `z3`'s solver.

### References

`shara` implements a novel algorithm for solving _recursion-free_
CHCs, which is based on the observation that a novel class of
recursion-free CHCs can be solved efficiently. A technical report on
the algorithm implemented in `shara` is publicly available.

Qi Zhou and William Harris. _Solving Constrained Horn Clauses Using
Dependence-Disjoint Expansions_. [arxiv](BH)
