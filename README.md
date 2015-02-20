satisfaction is an implementation of a SAT solver in Haskell.  One day, it may evolve into an SMT solver.

The implementation is split across several Haskell packages:

* satisfaction-core

    The core contains the solver implementation.  It has minimal
    dependencies (containers and base).  The interesting modules are
    in the SAT.* namespace.

* satisfaction

    The top-level package provides a binary that can understand DIMACS
    formatted problem instances.
