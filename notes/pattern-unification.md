# Pattern unification with erasure

Pattern unification is about solving a certain subset of higher-order
unification problems, that allow us to implement implicit arguments and other
elaboration features. How does pattern unification generalise when we are
dealing with a language that has phase distinctions, like erasure?

We assume basic working knowledge of CwF-style type theory.

## Review of pattern unification

In standard dependent type theory, a higher-order unification problem has the form:

```
Γ ⊢ ?m[σ] ≡ t
```

where `Γ, Δ : Con`, `σ : Sub Γ Δ`, `t : Tm Γ A[σ]`, and `?m : Tm Δ A` is the
hole we want to solve for. We can think of `Δ` as the context in which
the metavariable is created, and `Γ` as the context in which a solution is being
attempted.

For a solution to exist, some additional conditions must hold, the first of which restricts the problem to the 'pattern fragment'.
These are:

1. `σ` is a linear renaming: it consists only of distinct variables in
  `Γ`. In other words, it is a `σ : LinRen Γ Δ ⊆ Ren Γ Δ ⊆ Sub Γ Δ`. We can
  alternatively characterise linear renamings as those renamings which are
  epimorphisms: those for which `u[σ] = v[σ]` implies `u = v`. Additionally, it
  is possible to *invert* such renamings: we have `σ⁻¹ : PRen Δ Γ` which has a
  partial substitution action on terms in Γ: specifically, it is defined on
  those terms in `Γ` which only use variables present in `σ`.
2. `t` only contains variables from `σ`. This means that `t[σ⁻¹]` is defined.
3. `t` does not contain `?m`.

If condition 1 is met, then if a solution exists, it is unique and most general.
If conditions 2 and 3 are additionally are met, then we can peform the following operation on the
problem:

```
Γ ⊢ ?m[σ] ≡ t

(apply σ⁻¹ to both sides)
⟹ Δ ⊢ ?m[σ][σ⁻¹] ≡ t[σ⁻¹]   

(LHS reduces to ?m so is defined, RHS is defined by requirement 2)
⟹ Δ ⊢ ?m ≡ t[σ⁻¹] 
```

The above is the unique solution for `?m` and is most general.

In a practical setting, we represent `?m[σ]` as a metavariable applied to an
argument spine: `?m σ`. We then represent the solution as a closed iterated
function type: `?m = Δ ⇒ t[σ⁻¹]`

There are further things we can do to 'pre-process' the problem, primarily to
*prune* metavariable spines ocurring inside `t`, so that those variables don't
need to appear in `σ` for a solution to be valid. This is orthogonal to the
rest of this document.

## Adding erasure

What happens when we add erasure to the language? There are two main things:

1. We now have both runtime terms `Tm ω` and erased terms `Tm 0`.
2. There is an additional proof-irrelevant sort `# ∈ Γ` with context extension
    `Γ ▷ #` whose (decidable) presence determines whether we can coerce `Tm 0`
    to `Tm ω`; we can always coerce `Tm ω` to `Tm 0`. More specifically, we have
    the definitional isomorphism
    ```
    (↑, ↓) : Tm ω (Γ ▷ #) A ≃ Tm 0 Γ A
    ```
    of mode shifts.
    
Point 1 is not of consequence. Up to definitional equality, every erased term is
of the form `↓ b : Tm 0 Γ A` for some runtime term `b : Tm ω (Γ ▷ #) A`. For
this reason, we only need metas in `Tm ω`.

We don't need to change pattern unification, because this formulation of erasure
is *structural*; in other words it is describable in HOAS as a universe closed
under some type formers.

A pattern unification problem now looks the same as before

```
Γ ⊢ ?m[σ] ≡ t
```

where `Γ, Δ : Con`, `σ : Sub Γ Δ`, `t : Tm ω Γ A[σ]`, and `?m : Tm ω Δ A` is the
 hole we want to solve for.

For a solution, we must have the same conditions as before:

1. `σ` is a linear renaming.
2. `t` only contains variables from `σ`.
3. `t` does not contain `?m`.

However, since `# ∈ Γ` is a representable sort, a renaming might
now a contain a witness of `#`. For example,
```
(p, x, y). (p, x) : LinRen (∙ ▷ # ▷[0] A ▷[ω] B) (∙ ▷ # ▷[0] A)
```
is a valid linear renaming.

There are some problems that do not fall under these conditions but that might
appear quite often. Consider the spine
```
(p, x). (p, ↑x) : Sub (∙ ▷ # ▷[0] A) (∙ ▷ # ▷[ω] A)
```
This is not a renaming because it is not only made of variables. However,
we can always invert it:
```
(p, x). (p, ↓x) : Sub (∙ ▷ # ▷[ω] A) (∙ ▷ # ▷[0] A)
```
This is a very special case of a more general approach to inverting terms that
are determined up to definitional isomorphism (see
https://cstheory.stackexchange.com/a/50918/77156)

Given this, we can refine the spine condition (1) to be:

1. `σ` is a linear renaming *up to mode shifts*: it consists only of distinct
  variables in `Γ` potentially wrapped in `↑` or `↓`.

These renamings are still epimorphisms (mode shifts form an iso), and it is
possible to invert them into partial 'generalised' renamings.

### Optimising the representation of `#`

The `# ∈ Γ` sort is proof-irrelevant, meaning for any two witnesses `p, q : # ∈
Γ` , we have `p ≡ q`. Therefore, in implementation:

- For typechecking, we (only) need a flag on contexts `Γ` that records if `# ∈ Γ`.
- For pattern unification, need a flag to appear on metavariable spines `σ : Sub Γ Δ` that records if `# ∈ Δ`.

To decide if a spine `σ` meets the condition (1), it is sufficient to check that
it contains only distinct variables up to `↑/↓`.

To decide if a term `t` meets condition (2), we must also check that if `Δ` does
not contain `#` then `t` does not contain any `↑` coercions, or anything else
depending on `#` (unless nested under `↓`).

Besides that, the implementation depends on if we choose to include the mode
shifts as part of the syntax in the compiler. We implement both approaches
in this repository.

*If mode shifts are part of the compiler syntax (`explicit`)*, we can decide
condition 2 by traversing `t` and remembering when we encounter `↑`/`↓`; a
`↑` counts as a usage of `#` and `↓` adds `#` to the context.

*If mode shifts aren't part of the compiler syntax (`implicit`)*, we can instead
look at where erased terms appear in the syntax. Every time we find an erased
application, it counts as a usage of `↓`, and every time we find a type or a
variable whose mode is 0, it counts as a usage of `↑`. For this, we need to
remember variable modes in the syntax itself.
