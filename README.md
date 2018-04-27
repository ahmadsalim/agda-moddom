An Agda implementation of Modular Domains for Abstract Interpretation.

## Requirements
Agda 2.6+ and the Agda standard library

## Project structure
- Domains/
  + Concrete.agda -- Implementation of concrete domains
  + Abstract.agda -- Modular implementation of lattices for abstract interpretation
- Language/
  + Rec.agda -- Typed syntax for a simple language with recursive functions
  + Semantics.agda -- Compositionally-specified semantics for the recursive language. Contains both a concrete and abstract interpreter.
- Util.agda -- Various utility functions

## Type Checking
To type check the project, including the tests in `Language.Semantics`, call GNU `make` in the project root.
