# Predicate Transformers

This repository contains a library written in [Lean 4.2.0](https://github.com/leanprover/lean4/tree/v4.2.0) with the goal of reproducing the results from the ICFP 2019 paper 'A predicate transformer semantics for effects (functional pearl)'[^1] by Wouter Swierstra and Tim Baanen. Therefore, the source code of the library, which is located in the PredicateTransformers.lean file, closely follows the structure of the [ICFP artefact of that paper](https://github.com/wouter-swierstra/predicate-transformers/tree/icfp-artefact), which is written in [Agda](https://github.com/agda/agda).

[^1]: W. Swierstra and T. Baanen, 'A predicate transformer semantics for effects (functional pearl)', Proceedings of the ACM on Programming Languages, vol. 3, no. ICFP, pp. 1–26, 2019.

## Building the library

This repository can be built using Lake - the build system and package manager for Lean 4. Instructions on how to install and setup Lake and Lean can be found in the [GitHub repository for Lean 4](https://github.com/leanprover/lean4). When you have Lake installed, you can compile this repository by navigating to its main directory in your terminal of choice and executing the command:

```console
$ lake build
```
