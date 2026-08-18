# Equilibrium Pricing in Oligopolistic Data Markets

Lean formalization of Theorem 1 (1.363-approximate Nash equilibrium may not exist for linear pricing)
from the paper "Equilibrium Pricing in Oligopolistic Data Markets"
([arXiv:2608.14018](https://arxiv.org/abs/2608.14018)).

The three main results are listed in `DataMktOligo.lean`.

## Project structure

The lean files are split into 3 sub-directories:

* `LinDataMkt`: formally defines data markets and the pricing game.
* `NashInapprox`: states the main theorem and reduces it to an optimization problem.
* `MuOpt`: solves the optimization problem.
