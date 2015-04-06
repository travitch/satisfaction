[![Build Status](https://travis-ci.org/travitch/satisfaction.svg?branch=master)](https://travis-ci.org/travitch/satisfaction)

satisfaction is an implementation of a SAT solver in Haskell.  One day, it may evolve into an SMT solver.

The implementation is split across several Haskell packages:

* satisfaction-core

    The core contains the solver implementation.  It has minimal
    dependencies (containers and base).  The interesting modules are
    in the Satisfaction.* namespace.  There are some support data
    structures exposed, but their interfaces are guaranteed to be
    unstable.

* satisfaction

    The top-level package provides a binary that can understand DIMACS
    formatted problem instances.

# Build instructions

```{.bash}
cabal sandbox init
cabal sandbox add-source satisfaction-core
cabal sandbox add-source satisfaction

cabal install satisfaction
```
