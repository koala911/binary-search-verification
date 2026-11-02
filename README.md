# Binary search verified in Lean 4

A small learning project by Konstantin Kovalyov: binary search on lists of
natural numbers, with correctness proofs in Lean 4.

The search returns `true` or `false`, indicating whether the target occurs in
the list. Correctness assumes the list is sorted in nondecreasing order;
duplicate values are allowed.

## What is proved

The development in [`BinSearch.lean`](BinSearch.lean) includes:

- A linear reference search and a binary search, including interval versions.
- `bin_search_interval_correct`: binary and linear search agree on every
  interval of a sorted list.
- `bin_search_correct`: the whole-list binary search agrees with linear search.
- `bin_search_interval_spec`: despite its name, this theorem gives the
  whole-list specification below.

```lean
theorem bin_search_interval_spec (a : Nat) (as : List Nat)
    (h_sorted : sorted as) :
    bin_search a as = true ↔ ∃ i, _root_.get as i = some a
```

In words: for a sorted list, binary search returns `true` if and only if the
target occurs at some index. Here `get` and `sorted` are defined in this file.

## Check the proofs

Install [Lean via elan](https://github.com/leanprover/elan#installation), then
run these commands from the repository directory:

```sh
lean --version
lean BinSearch.lean
```

The [`lean-toolchain`](lean-toolchain) file pins Lean to
`leanprover/lean4:v4.30.0-rc2`. No Mathlib or other external Lean packages are
required. A successful check exits with code 0; the current file has no active
evaluation commands, so no output is expected.

## Scope

This project proves functional correctness, not a running-time bound. It uses
linked lists, whose indexing requires traversal, rather than arrays. The search
does not return an index, and its correctness guarantee requires sorted input.

The implementation and proofs were copied unchanged from my formal-verification
study repository. This repository presents that development as a standalone
project.
