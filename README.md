# Adjoint Meta Prototype

### Requirement

- GHC 9.2.8
- Cabal 3.8 or higher (preferably Cabal 3.10.3)

### Usage

```
./elevatori <mode spec> [<optional module to load>]
```

- Required arguments:
  - `<mode spec>`
    Determines which mode spec one wants to use.
    Currently it can be one of
    - TwoModes
    - LinMeta
    - InfoFlowModes
    To use other modes, one can use the code base of this executable as a library
    and provide their own mode spec.
- Optional arguments:
  - `<optional module to load>`
    If provided, interpreter loads the module and then
    run commands under the definitions in the module

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

This implementation has several syntax difference with our paper
on adjoint metaprogramming as the syntax of this implementation is
limited within ASCII characters.

First, we do not have two separate top-levels for
the type signature and term definition of a top-level term definition.
Instead, we use the following syntax:
```
<name> <args> : <type> = <exp>;;
```
This `<type>` part is the type of `<name>`, thus
`add n m : Int<P> -> Int<P> -> Int<P> = ...` means
that `add` is of `Int<P> -> Int<P> -> Int<P>`.
This syntax is subject to change as it is unconventional.

Another difference is that we use `Up` and `Down` instead of
the uparrow and downarrow symbols for the up-shift and
down-shift modalities. Furthermore, we infer the mode of inner
type/kind for `Up`/`Down`, so for `Up^C_P`/`Down^C_P` in the
paper syntax, we use `Up <C>` and `Down <P>`. One can read this
as "`Up` to `<C>`" or "`Down` to `<P>`". Note that we use `<>`
instead of superscript or subscript, as they are not easy to use
in general.

Construction of data type values has some minor difference as well.
Instead of writing `Cons x xs` in the curried form, we use
`Cons (x, xs)`.

Also, to assign branches to nested `match`s easily, we use
`end` at the end of each `match`. Thus, instead of
```
match xs with
| Nil => ...
| Cons (x, xs) => ...
```
we write
```
match xs with
| Nil => ...
| Cons (x, xs) => ...
end
```

Last but not least, identifiers starting with captial letters are reserved
for type/term constructor for datatypes, thus one cannot use
them for normal variables.

### Caveat

- The evaluation output is dirty because of decorated identifiers.
  Instead of printing `susp(xs . xs)`, it prints something like
  `susp(xs~2139 . xs~2139)`.
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
