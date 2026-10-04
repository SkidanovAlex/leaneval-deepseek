import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Design notes: the finite-dimensional mountain-pass theorem with the index bound

This module has no content; it exists so that the delegated statements below can `import` it and
read this design.

## What is needed, and why

`Work.OddBound.MinimaxExtraction` (Klingenberg's loop-space minimax, the single remaining input of
the odd-dimensional length bound) is *proved* by running the minimax on a **finite-dimensional
model**: the space of closed polygons with `N` vertices (or the space of broken geodesics), which is
a compact manifold, with the polygon energy as the functional.  On that model the two analytic
ingredients of the minimax are:

1. **the value bound**: every competing family has a member of energy `≥ (2π/√K)²/2`
   (this comes from Klingenberg's long homotopy lemma, already a theorem in this directory);
2. **the minimax principle**: a minimax over *1-parameter* families is attained at a **critical
   point of index `≤ 1`**, i.e. one at which the second derivative has *no two-dimensional subspace
   on which it is negative definite*.

The second ingredient is a theorem of the calculus of variations which is completely independent of
Riemannian geometry, and this directory therefore builds it as a standalone result (a natural gap in
the library).  Its finite-dimensional form is the following.

## Standard proof (Milnor, *Morse theory*, §; Chang, *Infinite dimensional Morse theory*)

Let `Λ` be the minimax value.  Write `E_c := {f ≤ c}` for the sublevel sets (restricted to the open
set `U` in which the minimax is run).

* **(i) `Λ` is a critical value.**  If there were no critical points with `f ∈ [Λ-δ, Λ+δ]`, then
  `|∇f|` would be bounded below by `c > 0` on the compact set `{Λ-δ ≤ f ≤ Λ+δ}`, and the
  negative gradient flow (stationary near the endpoints `a`, `b`) would push the sublevel `E_{Λ+δ}`
  into `E_{Λ-δ}` — hence push any competing path below the minimax level, a contradiction.  So for
  every `δ > 0` there is a critical point in the annulus, and by compactness of the critical set a
  subsequence converges to a critical point `p` with `f p = Λ`.
* **(ii) one such `p` has index `≤ 1`.**  Suppose every critical point `p` with `f p = Λ` had a
  two-dimensional subspace `V ⊆ E` on which the second derivative is negative definite.  Then the
  Taylor expansion gives `f (p + v) < f (p)` for `0 ≠ v ∈ V` small (the first derivative vanishes at
  `p`, the second derivative is negative on `V`), so the small disk `D := {v ∈ V : ‖v‖ ≤ ε}` is a
  *descending disk* whose boundary `∂D ≅ S¹` is **connected**.  A path (a `1`-dimensional object)
  entering the high region near `p` can be rerouted through `∂D` (this is the statement
  `π_1(D^2, S^1) = 0`, equivalently: a `1`-complex in a `2`-disk whose boundary lies in `∂D` can be
  pushed into `∂D`), lowering its maximum.  Applying this to every high excursion of a competing
  path (the high region is a neighbourhood of the critical set at level `Λ`, each point of which is
  equipped with such a disk) produces a path with maximum `< Λ`, a contradiction.
  The same argument is the reason why the conclusion must be "**no negative-definite plane**" and
  not the stronger "any two negative directions are proportional": the latter is false for a
  consensus degeneracy (e.g. the function `-x² + (y²+z²)²` at the origin has index `1` and a
  two-dimensional negative cone).

Part (i) is the classical mountain-pass theorem (Ambrosetti--Rabinowitz; Palais--Smale); part (ii)
is the "index `≤` number of parameters" refinement.  Both are proved for `C²` functions on an open
subset of a finite-dimensional real inner product space, with compact sublevel sets (which on a
compact manifold is automatic).

For the *application* the open set `U` is the set of polygons all of whose sides are shorter than
the injectivity radius (where the distance function — hence the energy — is smooth); all polygons
of energy below the minimax value `+ 1` are automatically of that kind, so the restriction to `U`
does not lose anything.
-/
