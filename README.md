# PoS-NSB

[![CI][action-shield]][action-link]

[action-shield]: https://github.com/AU-COBRA/PoS-NSB/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/AU-COBRA/PoS-NSB/actions?query=workflow%3ACI




This repository contains a formalization of Proof-of-Stake (PoS)
Nakamoto-style blockchain (NSB). Assuming a synchronous network
with a static set of corrupted parties we prove chain growth,
chain quality, and common prefix.

## Meta

- Author(s):
  - Søren Eller Thomsen
  - Bas Spitters
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.11 or later
- Additional dependencies:
  - [MathComp ssreflect 1.11.0](https://math-comp.github.io)
  - [MathComp finmap 1.5.0](https://github.com/math-comp/finmap)
  - [Equations 1.2.2](https://github.com/mattam82/Coq-Equations)
  - [Coq record update](https://github.com/tchajed/coq-record-update)
- Coq namespace: `AUChain`
- Related publication(s):
  - [Formalizing Nakamoto-Style Proof of Stake](https://arxiv.org/abs/2007.12105) 

## Building
The requirements can be installed via [OPAM](https://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.11.2 coq-mathcomp-ssreflect.1.11.0 \
  coq-mathcomp-finmap coq-equations coq-record-update
```
Then, run `make clean; make` from the root folder. This will build all
the libraries and check all the proofs.

## Project Structure

The top-level structure consists of the following folders:

- `Protocol` - parameters for the development, implementation of the
  actual protocol and definition of a block tree.
- `Model` - definition of the network, global state, and definition of
  reachable global states.
- `Properties` - proved properties about the protocol. `CG.v` contains
  the chain growth theorem, `CQ.v` contains the chain quality theorem,
  and `CP.v` contains the common prefix theorem.

Below is a depiction of the dependencies between the files.

<p align="center">
 <img src="deps.svg" width="500" title="File dependencies" />
</p>
