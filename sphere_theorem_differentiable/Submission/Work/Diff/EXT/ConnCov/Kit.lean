import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.T.lc_variation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Kit for the *conversion* between the `∇^{G 0}`- and the `∇^{G t}`-towers of the connection
difference

The target `Work.Diff.EXT.ConnCov.covKAExt_bound` bounds the `k`-th covariant derivative of the
lowered connection difference `aOf G t = g_t(∇^{g_t} − ∇^{g_0})` with respect to the **fixed**
background connection `∇^{G 0}`, uniformly on `[T/2,T)`.

The only source of *uniform* information in the hypotheses is `ShiBounds`, which bounds the
**moving**-connection towers `∇^{G t, k}Rm` of the curvature.  Every known proof therefore has to
compare the two towers, and the comparison is the following algebraic fact: for connections
`cov' = cov + δ` one has, on smooth fields,
`step cov' τ = step cov τ + (insertion of δ) τ`, where the insertion replaces a slot of `τ` by the
field `δ(·, v 0)`.

This module collects the vocabulary of that comparison:

* `covDiff` — the connection difference as a `(1,2)`-tensor **field** (`δ`);
* `insAll` — the total insertion operator (the sum of `ATower.insD` over the derivative slots and of
  `ATower.insA`, `insB`, `insC`);
* `dAOfBase` — the base of the tower of the *time derivative* of the connection difference, i.e.
  `(A B C y) ↦ deriv (fun s ↦ aOf G s A B C y) t`; the Clairaut identity for the `∇^{G 0}`-tower
  (whose connection is time-independent) says
  `∂_t (covKAExt G t k ...) = (the same tower with `aOf G t` replaced by `dAOfBase G t`)`;
* `baseRic` — the Ricci tensor of a metric as an `Op3 0`, so that the `∇^{G 0}`-tower of `Ric`
  can be handled by the same `ATower` framework.

## Route (why these are the right objects)

Write `T_k(t) := ∇^{G 0, k} aOf G t` (the frozen `covKAExt G t k`) and `S_k(t) := ∇^{G t, k} aOf G t`.
Then

* `∂_t T_k = ∇^{G 0, k} (∂_t aOf G ·)` (Clairaut; `∇^{G 0}` does not depend on `t`), and
* `∂_t aOf G t = −(Koszul combination of `∇^{G 0}Ric`)`, because `∂_t g = −2 Ric` and `aOf` is the
  Koszul combination of `∇^{G 0}g` (linear in `g`).

So `∂_t T_k` is (an index-permutation of) `∇^{G 0, k+1} Ric`, and the level-`k` Gronwall closes as
soon as `∇^{G 0, m}Ric` is bounded by a *polynomial* in the `T_j` (`j < m`) and the Shi bounds: the
`∇^{G 0}`-tower of `Ric` is compared with the `∇^{G t}`-tower of `Ric` (which is a contraction of
`∇^{G t, ·}Rm`, hence bounded by `ShiBounds`), and the comparison needs the `∇^{G t}`-towers of `A`
at orders `< m`, which are compared back with the `T_j` (`j < m`).  The two comparisons are the
*same* statement: for a fixed tensor `T` and the one-parameter family of connections
`cov_s := ∇^{G s}`,

  `∂_s (tower cov_s T k) = Σ_{r<k} (step cov_s)^r (insAll (∂_s cov_s)) (tower cov_s T (k-1-r))`,

i.e. the variation of the tower in the connection.  Integrating in `s` from `0` to `t` expresses
`∇^{G t, k}T` in terms of `∇^{G 0, k}T` and of products of *lower*-order towers — a triangular
relation, which is what makes the whole estimate close.

The definitions below are deliberately `sorry`-free so that lemmas about them can be delegated
without importing the (still open) target.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The connection difference** `∇^{G t} − ∇^{G 0}` as a `(1,2)`-tensor field, in the form needed
by the insertion operators: `covDiff G t X Y : TF` is the field `y ↦ ∇^{G t}_X Y − ∇^{G 0}_X Y`. -/
noncomputable def covDiff (G : ℝ → SMet I M) (t : ℝ) :
    TF (I := I) (M := M) → TF (I := I) (M := M) → TF (I := I) (M := M) :=
  fun X Y y => (lcOf (G t)) X y (Y y) - (lcOf (G 0)) X y (Y y)

/-- **The total insertion operator.**  For a `(1,2)`-tensor field `δ` and an operator `τ`, `insAll δ τ`
is `τ` with the four correction slots of one recursion step replaced by `δ`-values.  It is exactly
the difference `step cov' τ − step cov τ` when `cov' = cov + δ`. -/
noncomputable def insAll {k : ℕ}
    (δ : TF (I := I) (M := M) → TF (I := I) (M := M) → TF (I := I) (M := M))
    (τ : Op3 (I := I) (M := M) k) : Op3 (I := I) (M := M) (k + 1) :=
  (∑ i : Fin k, insD i δ τ) + insA δ τ + insB δ τ + insC δ τ

/-- **The base of the tower of the time derivative of the connection difference**: the (fixed) tensor
`(A B C y) ↦ ∂_t (aOf G · A B C y)`, which is the Koszul combination of `−2 Ric(G t)`. -/
noncomputable def dAOfBase (G : ℝ → SMet I M) (t : ℝ) : Op3 (I := I) (M := M) 0 :=
  fun _ A B C y => deriv (fun s : ℝ => aOf G s A B C y) t

/-- **The Ricci tensor as an `Op3 0`** (the third value slot is unused): so that the `∇^{G 0}`-tower
of `Ric` is `tower (lcOf (G 0)) (baseRic g) k` and can be handled by the `ATower` framework. -/
noncomputable def baseRic (g : SMet I M) : Op3 (I := I) (M := M) 0 :=
  fun _ A B C y => ricAt (lcOf g) y (A y) (B y)

/-- The frozen tower of the connection difference is the `ATower` tower of `aOf` with the background
connection, with the value dependence (`valOp`) formulation used by the target. -/
theorem valOp_aOf_tower (G : ℝ → SMet I M) (t : ℝ) (k : ℕ)
    (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    valOp (tower (lcOf (G 0)) (fun _ => aOf G t) k) x v a b c
      = covKAExt G t k (fun i => smoothExt x (v i)) (smoothExt x a) (smoothExt x b)
          (smoothExt x c) x :=
  valOp_tower_eq_covKAExt (I := I) (M := M) G t k x v a b c

end Work.Diff.EXT.ConnCov
