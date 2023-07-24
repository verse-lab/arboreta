# Verifying Distributed Clocks

## Requirements

- Coq 8.16.1
  - [`stdpp`](https://gitlab.mpi-sws.org/iris/stdpp) (latest?)
- ocaml >= 4.12.0?
- [`dune`](https://dune.build/install) 3.6
- Python3 with `cyaron` installed (`pip install cyaron`)

For VST:
- VST 2.11.1
- CompCert 3.11

## Organization

- `clocks`: Coq formalization of tree clock and degenerated tree clock (with no attached clock information). 
- `utils`: Coq utility files. 
- `extraction`: Originally for testing the Coq implementation via extraction; now for testing various things. Check [`extraction/README.md`](extraction/README.md) for details. 
- `vst`: VST verification of treeclock (in C). 

## Compile

```shell
make
```
