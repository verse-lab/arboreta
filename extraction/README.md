# Playground

Tests are done here. 

This directory is messy; many things were added on a temporary basis. 

## Organization

### Coq & OCaml Part

This part is mainly for extracting and running tree clocks. 
- `extract_driver.v`: For extracting Coq implementation of tree clock into OCaml files. 

`dune` defines a dune project here. 
- `lib`: A dune library directory. Extracted files will be placed here. 
- `main.ml`: The main file for various purposes. 

### Python & Shell Script Part

Utilities: 
- `tree_clock.py`: Encoder/decoder for tree clocks and some checking functions. As mentioned above, the actual implementation is written in Coq. 
- `matrix_clock.py`: Naive matrix clock implementation. 

For generating random data:
- `treegen.py`: Generating random tree clocks satisfying shape conditions. 
- `respect_treegen.py`: Generating two tree clocks such that the former one respects the latter one. 
- `historygen.py`: Generating random histories. The only type of event in the history is sending and receiving messages. 

For testing the join operation of tree clock: 
- `join_test.sh`

For testing the respect predicate: 
- `mutualrespect_test.sh`
- `mutualrespect_checker.py`

For testing the expresiveness of matrix clocks and tree clocks:
- `clock_simulator.py`
- `mc_vs_tc_main.py`
- `mc_vs_tc_test.sh`
- `mc_vs_tc_checker.py`

### Others

- `examples`: representative examples found during testing

## Encoding Format

For convenience, the input and output formats are peculiar. However, they can be pretty-printed. 

### Tree Clock Format

- Encoding tree clock: See the `treeprint` function in [`tree_clock.py`](tree_clock.py).
- Decoding tree clock: See `dune exec ./main.exe print` below. 

### History Format

- Encoding history: See the `read_event` function in [`main.ml`](main.ml).
- Decoding history: See `dune exec ./main.exe simulate` and  below. 

## How to Run

### Tree Clock Related

**Prerequisite: the Coq files are compiled.**

`dune exec ./main.exe testjoin <verbosity> [<output_path>]`: Takes the concatenation of the encoding of two tree clocks as input (from `stdin`), checks whether the result of join operation is legal, and outputs the result of join into `output_path` (optional). 
- `verbosity` larger than 0: the input and output will be printed
- Example: `dune exec ./main.exe testjoin 1 < examples/testjoin/2.test`

`dune exec ./main.exe print <number_of_trees>`: Takes the concatenation of the encoding of `number_of_trees` tree clock(s) as input (from `stdin`) and pretty-prints them. 
- Example: `dune exec ./main.exe print 2 < examples/testjoin/1.test`

`dune exec ./main.exe simulate <print_trace_or_not> [<path_prefix>]`: Takes the encoding of a history as input (from `stdin`), runs causal tracking with tree clocks on it and outputs the resulting tree clocks (optional). 
- `print_trace_or_not` larger than 0: the trace will be printed
  - By default the normalized tree (children sorted by process ID and attached clock erased) is output. If a different output format is needed, one may modify the `clock_simulate` function in [`main.ml`](main.ml). 
- `path_prefix`: if given, the resulting tree clock on `i`-th process will be stored into `${path_prefix}${i}.tr`
- Example: `dune exec ./main.exe simulate 1 < examples/mc_stronger_than_tc/history_1`

### Matrix Clock Related

`python3 clock_simulator.py <history_file>`: Takes the encoding of a history as input (from `history_file`), runs causal tracking with matrix clocks on it and outputs the resulting matrix clocks.  
- Example: `python3 clock_simulator.py examples/mc_same_tc_different/history_1`
