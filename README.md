# TensorIR
Formal development of a type-safe intermediate language for tensor expressions.

This Coq development accompanies and builds on the presentation in the article
[TeIL: a type-safe imperative tensor intermediate language](https://dl.acm.org/doi/10.1145/3315454.3329959).
The article discusses type-safety for TeIL, a proof of which is developed in the `safety` subdirectory of this repository.

Generally, the contents of this repository are as follows:
* `safety` contains a Coq development culminating in a type-safety (memory-safety) proof for TeIL.
* `equations/deep` contains another deep embedding of TeIL into Coq using [paramteric higher-order abstract syntax (PHOAS)](https://doi.org/10.1145/1411204.1411226).
  This facilitates simple proofs of the equations in Section 3.6 of [TeIL: a type-safe imperative tensor intermediate language](https://dl.acm.org/doi/10.1145/3315454.3329959).
* `equations/shallow` contains a shallow embedding of TeIL expressions into Coq.
  This enables even simpler verification of the equations in Section 3.6 of [TeIL: a type-safe imperative tensor intermediate language](https://dl.acm.org/doi/10.1145/3315454.3329959).
  
Note that a precursor of TeIL is presented in the article [Modeling of languages for tensor manipulation](https://arxiv.org/abs/1801.08771), together with pen-and-paper proofs.
