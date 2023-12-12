# 🌲 Arboreta 🌲

A small library for facilitating proofs about (rooted) labeled trees in Coq, and helping verifying C code that involves the use of array-based trees with VST (still, in Coq). 

## Install Requirements

Coq:
- 8.16.1

Required Coq package(s) for compiling the files inside `utils/` and `clocks/`:
- `stdpp` 1.8.0

Required Coq package(s) for compiling the files inside `vst/`:
- VST 2.11.1
- CompCert 3.11

The requirements above might be satisfied by installing [this version of Coq platform](https://github.com/coq/platform/blob/main/doc/README~8.16~2022.09.md). 

## Directory Organization

- `clocks`: Coq formalization of tree clock and degenerated tree clock (with no attached clock information). 
- `utils`: Coq utility files. 
- `extraction`: Originally for testing the Coq implementation via extraction; now for testing various things. Check [`extraction/README.md`](extraction/README.md) for details. 
- `vst`: VST verification of tree clock (in C). 
- `race-detector`: The data race detectors used in evaluation. 

Currently, the library related definitions described in the paper are intermixed with those about tree clocks. The pure part of the library (including **Arboreta-P** and the loop invariant template for non-recursive traversals) is in `clocks/treeclock.v`, and the separation logic related part is mainly in `vst/`. 

## Building Instructions

```shell
bash clightgen.sh   # only if you are going to compile the files inside `vst/`
make
```
