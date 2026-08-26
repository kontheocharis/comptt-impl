## Type theory with erasure

Toy implementation of type theory with erasure as a phase distinction.

> To keep this self-contained and understandable, I have based it on András
> Kovács' `elaboration-zoo` which is reasonably well-known
> (specifically [`elaboration-zoo/04-implicit-args`](https://github.com/AndrasKovacs/elaboration-zoo/tree/master/04-implicit-args))


For type formers we only have mode-aware Π, and U. The notation is:

```haskell
(0 x : A) -> B -- erased Π
(x : A) -> B   -- runtime Π
```

Terms are split into two modes: `ω a : A` is a runtime term, and `0 a : A` is an erased term.

The rules are:
- If `ω a : A` then `0 (↓ a) : A`.
- If  `0 a : A` and a special symbol `#` is in scope, then `ω (↑ a) : A`.
- The symbol `#` is called the erasure marker and comes into scope when going under a `↓`.
- Types are always erased.
- The `↓`/`↑` coercions and the `#` symbol are fully elaborated in; the user cannot interact with them.
- On the surface, the language behaves just like `QTT({0, ω})`.

There are two implementations contained here: `explicit` and `implicit`. The
input language is the same, the difference is the elaborated output. We show
this difference with the Church encoding of `Fin`. First, this is the
source-level input:

```haskell
let 0 Fin : Nat -> U
= \n . (0 A : Nat -> U)
  -> ({0 k : Nat} -> A (succ k))
  -> ({0 k : Nat} -> A k -> A (succ k))
  -> A n;
```

- `explicit`: the syntax includes the coercions between runtime and erased
  terms, added during elaboration. `Fin` becomes

  ```haskell
  let 0 Fin : Nat → U
  = ↓ (λ n. ↑ ((0 A : Nat → U)
    → ({0 k : Nat} → ↓ (↑ A) (succ (↑ k)))
    → ({0 k : Nat} → (↓ (↑ A) (↑ k)) → ↓ (↑ A) (succ (↑ k)))
    → ↓ (↑ A) n));
  ```
  
  This means we see exactly when we use a term in a mode other than the one it is
  inherently from.

- `implicit`: this does not include explicit coercions; it is much closer to the
  way Idris2 or Agda implement erasure (QTT). The output looks very close to the input.
  `Fin` becomes
  
  ```haskell
  let 0 Fin : Nat → U
  = λ n. (0 A : Nat → U)
    → ({0 k : Nat} → A (succ k))
    → ({0 k : Nat} → A k → A (succ k))
    → A n;
  ```
  
  
  
### Discussion

I have not measured it yet but the performance gap should be negligible because
there is no deep traversal happening during eval/quote and the value
representation of coercions is quite efficient. 

There is a code extraction capability invoked with the `ex` flag, that spits
out untyped lambda calculus terms, removing all erased/compile-time data.

There is an [explanation](./notes/pattern-unification.md) about how to do
pattern unification in this system.
