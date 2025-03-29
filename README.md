# About the Project

## Getting Started

### Prerequisites 

You should have stack installed [see the Haskell Stack docs](https://haskellstack.org/).

### How to use this?

In this section we will provide instructions and examples on how to use our code.

To interact with the full library in `ghci` run `stack ghci` in your terminal from the top level folder in this repository. Use `:reload` to update changes after editing the library, and `:quit` to exit GHCi.

#### Syntax and Semantics Example Usage

To create:
- a simple world state with 
```haskell
let ws = mkWorldState [(PPred "P" [StdName "n1"], True)] []
```
-  a model with 
```haskell
let m = Model ws (Set.singleton ws) (Set.fromList [StdName "n1"])
```
- and a formula 
```haskell
let f = Atom (Pred "P" [StdNameTerm (StdName "n1")])
```

To check if the formula holds use `checkModel m f`, which should return `True` since `P(n1)` is true in the model. Alternatively, evaluate satisfiability with `satisfiesModel m f`.

#### Satisfiability and Validity Checking Example Usage

 You can test the satisfiability and validity of formulas interactively. For example, define a formula like 
 ```haskell
 let f = Or (Atom (Pred "P" [StdNameTerm (StdName "n1")])) (Not (Atom (Pred "P" [StdNameTerm (StdName "n1")]))) 
 ```
 and check its *satisfiability* with `isSatisfiable f`, which should return `True` (since `P(n1) v ~ P(n1)` is satisfiable). Similarly, test *validity* with `isValid f`, which returns `False`.

### Ask and Tell Usage Examples

You can use AskTell module's `ASK`, `TELL`, and `INITIAL` operators interactively. For example, define:

- a domain with 
```haskell
let d = Set.fromList [StdName "n1"]
```
- an initial epistemic state with 
```haskell
let e = initial [PPred "P" [StdName "n1"]] [] [StdName "n1"]
```
- and a formula like 
```haskell
let f = Atom (Pred "P" [StdNameTerm (StdName "n1")])
``` 
Test the `ASK` operator with `ask d e f`, which checks if `P(n1)` is known across all worlds.
Apply `TELL` with `let e' = tell d e f` to filter worlds where `P(n1)` holds, then verify with `ask d e' f`, expecting `True`. Alternatively, use `askModel` and `tellModel` with a Model, such as `let m = Model (Set.findMin e) e d`, via `askModel m f` and `tellModel m f`.

### Translations Usage Examples

You can interactively test translations and model properties. To do so, you can, for example, define a KL formula like let `f = K (Atom (Pred "P" [StdNameTerm (StdName "n1")])))` and translate it to standard epistemic logic (SEL) with `translateFormToKr f`, expecting `Just (Box (P 1))`. Conversely, translate an SEL formula like `let g = Box (P 1)`
to KL with `translateFormToKL g`, yielding `K (Atom (Pred "P" [StdNameTerm (StdName "n1")])))`. 

For models, create a KL model with `let m = model1` and convert it to a Kripke model using `translateModToKr m`, then compare with `kripkeM1` via `test1`. You can try out the Kripke-to-KL translation by using `kripkeToKL exampleModel3 (makeWorldState 30)`, checking if it succeeds.

### Development

#### Using Stack in the Haskell programming environment

- To compile everything:
    ```bash 
    stack build
    ```
- To force a complete rebuild:
    ```bash
    stack clean && stack build
    ```
- To interact with the code base via `ghci`:
    ```bash
    stack ghci
    ```
- To run tests:
    ```bash
    stack clean && stack test --coverage
    ```
- To run a subset of tests based of the description:
    ```bash
    stack test --test-arguments="--match <description>"
    ```

# Extensive documentation 

For more extensive documentation see [report.pdf](report.pdf).

