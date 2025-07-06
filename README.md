# Quilt Prototype

### Requirement

- GHC 9.4.8
- Cabal 3.8 or higher (preferably Cabal 3.14.2.0)

### Usage

```
./quilti <accessibility spec> [<optional module to load>]
```

- Required arguments:
  - `<accessibility spec>`
    Determines which accessibility spec one wants to use.
    Currently we have the following built-in specs:
    - ThreeModes
    - TwoIntModes
    - TwoModes

    To use other specs, one can use the code base of this executable as a library
    and provide their own accessibility spec.
- Optional arguments:
  - `<optional module to load>`
    If provided, interpreter loads the module and then
    run commands under the definitions in the module

### Example Modes
We provide the following example modes
- `ThreeModes`  
  An accessibility spec with one unrestricted mode `A` and two linear modes `B` and `C` where `A > B, C`, `B >= C`, and `C >= B`.
  Linear mutable arrays are available for `B` and `C`.
- `TwoIntModes`  
  An accessibility spec with two unrestricted modes `A` and `B` where `A > B`.
- `TwoModes`  
  An accessibility spec with one unrestricted mode `A` and one linear mode `B` where `A > B`.
  Linear mutable arrays are available for `B`.
  
### Examples
Some examples for the ThreeModes and TwoModes accessibility specs are
in the corresponding subdirectory of `/examples` directory.  For
example, `/examples/TwoModes` contains some example programs for
`TwoModes` such as `ffc.quilt`.

### Syntax Difference

This implementation has several syntax difference with our paper as
the syntax of this implementation is limited within ASCII characters.

First, we do not have two separate top-levels for the type signature
and term definition of a top-level term definition. Instead, we use
the following syntax: ``` <name> <args> : <type> = <exp>;; ``` This
`<type>` part is the type of `<name>`, thus `add n m : Int<A> ->
Int<A> -> Int<A> = ...` means that `add` is of `Int<A> -> Int<A> ->
Int<A>`.  This syntax is subject to change as it is unconventional.

Another difference is that we use `Up` and `Down` instead of the
uparrow and downarrow symbols for the up-shift and down-shift
modalities. Furthermore, we infer the language of inner type/kind for
`Up`/`Down`, so for `\uparrow^A_B`/`\downarrow^A_B` in the paper
syntax, we use `Up <A>` and `Down <B>`. One can read this as "`Up` to
`<A>`" or "`Down` to `<B>`". Note that we use `<>` instead of
superscript or subscript, as we cannot write them with ASCII.

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

The order of arguments in built-in interface for mutable array is a
bit different. `read` and `write` first take the index of an entry and
then take the array.

Last but not least, identifiers starting with captial letters are
reserved for type/term constructor for datatypes, thus one cannot use
them for normal variables.

### Caveat

- The evaluation output is dirty for functions and code because of
  decorated identifiers. For example, a printed result is something
  like `susp(fun xs~2139 -> xs~2139)` instead of `susp(fun xs -> xs)`.
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
