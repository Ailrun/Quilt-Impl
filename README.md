# Adjoint Meta Prototype

### Requirement

- GHC 9.2.8
- Cabal 3.8 or higher (preferably Cabal 3.10.3)

### Example Modes
We provide the following example modes
- `TwoModes`  
  A mode spec with code mode (`C`) and program mode (`P`).
- `LinMeta`  
  A mode spec with code mode (`C`), garbage-collected mode (`GC`), and garbage-free mode (`GF`).
- `InfoFlowModes`__
  A mode spec with code mode (`C`), program mode (`P`), and a secure data mode (`S`).
  
### Examples
Some examples for the TwoModes and LinMeta mode specs are in the corresponding
subdirectory of `/examples` directory.
For example, `/examples/TwoModes` contains some example programs for
`TwoModes` such as `nth.elev`.

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

Also, identifiers starting with a captial letter is for
type/term constructor for datatypes, thus one cannot use
them for normal variables.

### Caveat

- When parse error happens in the type signature of a term definition,
  it reports the beginning of the term identifier.
- Currently a type error does not produce a pretty message.
- Omitting identity substitution is not yet supported. For example,
  ```
  let x = susp(y . y) in
  susp(y . force x)
  ```
  does not (yet) work. This requires
  ```
  let x = susp(y . y) in
  susp(y . force x @ (y))
  ```
