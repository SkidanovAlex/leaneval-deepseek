import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_dense
import Submission.Commons.Geometry.Convex.Hadwiger.parallel_body_valuation
import Submission.Commons.Geometry.Convex.Hadwiger.parallel_body_linearIndependent
import Submission.Commons.Geometry.Convex.Hadwiger.continuous_parallel_body_volume
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_add_convexBody
import Submission.Commons.Geometry.Convex.Hadwiger.convexBody_interval_repr
import Submission.Commons.Geometry.Convex.Hadwiger.interval_interior_empty_iff
import Submission.Commons.Geometry.Convex.Hadwiger.interior_empty_iff_affineSpan_ne_top
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_inclusionExclusion
import Submission.Commons.Geometry.Convex.Hadwiger.simple_valuation_binary_union
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_split_interval
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_interval_additive_length
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_interval_zero_on_rational_lengths
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_interval_zero_all_lengths
import Submission.Commons.Geometry.Convex.Hadwiger.klain_333_dim_one
import Submission.Commons.Geometry.Convex.Hadwiger.dissection_additivity
import Submission.Commons.Geometry.Convex.Hadwiger.klain_333_box_vanishing
import Submission.Commons.Geometry.Convex.Hadwiger.hadwiger_span_parallelBody_generic

open Metric MeasureTheory
open scoped Classical Pointwise

/-!
# `valuation_mem_span_parallelBody` — proof status and plan

This theorem is **the hard half of Hadwiger's characterization theorem**:
every continuous rigid-motion-invariant valuation on the convex bodies of
`EuclideanSpace ℝ (Fin n)` lies in the real span of the `n+1` functionals
`K ↦ vol (K + iB)` (`i = 0, …, n`; `B` = unit ball).

Together with the already-proven commons results
* `Commons.Geometry.Convex.Hadwiger.parallel_body_valuation` (each `F i` is a valuation),
* `Commons.Geometry.Convex.Hadwiger.parallel_body_linearIndependent`
  (the `F i`, `i = 0..n`, are ℝ-linearly independent),
this yields the top-level theorem `Module.finrank ℝ (valuations n) = n + 1`
(see `Submission.lean`).

## Status (this session's commons work — all PROVED and published)

Dimension-1 base of the whole chain (Klain Thm 3.3, n = 1) is DONE in commons:
`convexBody_interval_repr`, `interval_interior_empty_iff`,
`interior_empty_iff_affineSpan_ne_top`, `valuation_inclusionExclusion`,
`simple_valuation_binary_union`, `valuation_split_interval`,
`valuation_interval_additive_length`, `valuation_interval_zero_on_rational_lengths`,
`valuation_interval_zero_all_lengths`, `klain_333_dim_one`
(all in `Commons.Geometry.Convex.Hadwiger`, files imported above).

IN FLIGHT (requested from colleagues):
* `dissection_additivity` — Groemer: for a continuous *simple* valuation, a convex
  body P = ∪ᵢ Aᵢ (Aᵢ convex, pairwise empty-interior intersections) satisfies
  φ(P) = Σᵢ φ(Aᵢ).  (The workhorse for all dissection/cut-and-paste arguments.)
* `klain_333_box_vanishing` — Klain Thm 3.3 for all n (box vanishing).
* `simple_rigid_invariant_eq_const_volume` — Thm 4.2 (simple + rigid ⇒ c·vol).
* `hadwiger_span_parallelBody_generic` — the Hadwiger classification for any
  finite-dim real inner product space V: every continuous rigid-motion-invariant
  valuation f lies in span of `K ↦ vol(K + iB)`, `i = 0..finrank V`.

## How the final assembly goes (verified compiling in scratch)

Once `Commons.Geometry.Convex.Hadwiger.hadwiger_span_parallelBody_generic` is in
commons, the body of the final theorem is exactly:

```
  dsimp
  rintro f ⟨hcont, hadd, hiso, htrans⟩
  exact hadwiger_span_parallelBody_generic (V := EuclideanSpace ℝ (Fin n)) (n := n)
    (hn := finrank_euclidean n) f hcont hadd hiso htrans
```

(The `dsimp` unfolds the four `let`-bindings of the statement; `finrank_euclidean`
is proved below.  Everything type-checks: `EuclideanSpace ℝ (Fin n)` is a
finite-dimensional real inner product Borel space and `B`, `F` in the statement
coincide definitionally with the generic theorem's `B`, `F`.)

## Mathematical route (background)

Klain, *A short proof of Hadwiger's characterization theorem*, Mathematika 42 (1995)
329–339 (full text in workspace file `.txt`).  Because the problem's `IsVal`
invariance group is the **full Euclidean group (reflections included)**, `φ(K)=φ(−K)`
is automatic and Klain Thm 4.2 needs no parity case and no Prop 4.1.  The chain is:
(1) dissection additivity (Groemer); (2) Thm 3.3 box vanishing (dimension-1 base done);
(3) Thm 3.4 (φ(K)+φ(−K) = c·vol); (4) Thm 4.2 ⇒ simple+rigid = c·vol;
(5) classification by induction on dimension via intrinsic volumes (restriction
property V_k|_H = V_k^{(n-1)}); (6) Steiner: V_k are the (normalized) coefficient
functionals of t ↦ vol(K + tB), i.e. Vandermonde combinations of the F_i.
Details and exact request statements: `PROOF_PLAN.md` in this directory.
-/

namespace Commons.Geometry.Convex.Hadwiger

/-- The dimension of `EuclideanSpace ℝ (Fin n)` as a real vector space is `n`. -/
lemma finrank_euclidean (n : ℕ) : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
  simp

theorem valuation_mem_span_parallelBody (n : ℕ) :
    let V := EuclideanSpace ℝ (Fin n)
    let B : ConvexBody V := ⟨Metric.closedBall (0 : V) 1, convex_closedBall (0 : V) 1, isCompact_closedBall (0 : V) 1, nonempty_closedBall.mpr zero_le_one⟩
    let F : Fin (n + 1) → ConvexBody V → ℝ := fun i K => (volume ((K + (i : ℝ) • B : ConvexBody V) : Set V)).toReal
    let IsVal : (ConvexBody V → ℝ) → Prop := fun f =>
      Continuous f ∧
      (∀ A B C D : ConvexBody V,
          (A : Set V) = (C : Set V) ∪ (D : Set V) →
          (B : Set V) = (C : Set V) ∩ (D : Set V) →
          f A + f B = f C + f D) ∧
      (∀ A B : ConvexBody V, ∀ e : V ≃ₗᵢ[ℝ] V,
          (B : Set V) = e '' (A : Set V) → f B = f A) ∧
      (∀ A B : ConvexBody V, ∀ t : V,
          (B : Set V) = (fun x => x + t) '' (A : Set V) → f A = f B)
    ∀ f : ConvexBody V → ℝ, IsVal f → f ∈ Submodule.span ℝ (Set.range F) := by
  dsimp
  rintro f ⟨hcont, hadd, hiso, htrans⟩
  exact hadwiger_span_parallelBody_generic (V := EuclideanSpace ℝ (Fin n)) (n := n)
    (hn := finrank_euclidean n) f hcont hadd hiso htrans

end Commons.Geometry.Convex.Hadwiger
