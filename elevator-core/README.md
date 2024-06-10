# Elevator Prototype

### Requirement

- GHC 9.2.8
- Cabal 3.8 or higher (preferably Cabal 3.10.3)

### Syntax Difference

Unlike paper, we do not have two separate top-levels for
the type signature and term definition of a top-level term definition.
Instead, we use the following syntax:
```
<name> <args> : <type> = <exp>;;
```
Moreover, instead of the uparrow and downarrow symbols for the
up-shift and down-shift modalities, we use `Up` and `Down` for
them.
