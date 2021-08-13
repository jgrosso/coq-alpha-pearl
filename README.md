# coq-alpha-pearl

## Summary

A Coq formalization of "Functional Pearls: α-conversion is easy" (Altenkirch, 2002).

To our knowledge, everything in the paper itself has been formalized. (Proving the equivalence to de Bruijn terms is still in progress, but because it is left to the reader in the original paper, we are comfortable sharing this formalization as-is.)

Ergonomic work is being done on the `compute-sets` branch of this repository. Specifically, we hope to implicitly compute the domains/codomains/etc. of functions/relations/etc. instead of requiring them to be provided explicitly (as is currently the case, viz. the `X`, `Y`, etc. parameters to many of the lemmas).

## Dependencies

This formalization relies on the following libraries:

  - [math-comp](https://github.com/math-comp/math-comp/)
  - [extructures](https://github.com/arthuraa/extructures/)
