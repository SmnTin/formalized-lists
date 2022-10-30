![Build](https://github.com/smntin/formalized-lists/actions/workflows/build.yml/badge.svg)

# Formalized lists

This is a test assignment for the project "Mechanizing Denotational Semantics of Message-Passing Concurrency in the Coq Proof Assistant".

## Building

All the theories are located in [src/lists.v](src/lists.v). You can interpret this file interactively in an IDE. For example, you can use [VsCoq](https://github.com/coq-community/vscoq).

Otherwise, you can build it using [dune](https://dune.build/):
- First, you have to make sure that Coq is installed. For example, you can install it locally using [opam-switch](https://opam.ocaml.org/doc/man/opam-switch.html). If you already have a global installation, you can skip this step.
- Then invoke in the command line:
    ```
    dune build
    ```