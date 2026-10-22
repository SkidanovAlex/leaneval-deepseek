import Mathlib
import Submission.Work.ANALYTIC.towerFEAsetup

/-!
# The zero slice of the truncation data

This file proves `Work.ANALYTIC.TruncDataElemZeroSlice`: the pullback of the truncation data
`truncDataElem S x` (the element of `∏^bnd ℤ` over `(ℕ∪{∞}) × S` whose `m`-th component is
`(k,s) ↦ x_m(s)·[k ≤ m]`) along the zero slice `zeroSlice S : S ⟶ (ℕ∪{∞}) × S`, `s ↦ (0,s)`,
is `x` itself:
`truncDataElem S x |_{k = 0} = x`,
because `[0 ≤ m] = 1` for every `m : ℕ`.

The computation is pointwise.  The element `↥(boundedSeq.obj.obj (op S))` is *definitionally* the
submodule `boundedSeqSet S` of `ℕ → C(S,ℤ)` (cf. `boundedSeq_obj_obj`), but the coercion `(·).1`
elaborated inside a statement with a metavariable for the variable resolves against the submodule
flavour, whereas the term produced by `truncDataElem` carries the `ModuleCat` flavour.  The
pointwise evaluation lemma `truncDataElem_at` below is therefore stated with the variable written
out explicitly; it is a `rfl` and is the version on which `rw` succeeds.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

/-- **Pointwise value of the truncation data.**  The `m`-th component of `truncDataElem S x` at the
point `(k, s)` is `x_m(s)·(1 - ∏_{i ≤ m}(1 - δ_i(k)))`. -/
lemma truncDataElem_at (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (m : ℕ) (k : ↥(ℕ∪{∞})) (s : ↥S) :
    ((truncDataElem S x).1 m) (k, s)
      = x.1 m s * (1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i k)) := rfl

/-- The `m`-th component of `truncDataElem S x` at the zero slice, `s ↦ (0,s)`, is `x_m(s)`:
the coefficient `1 - ∏_{i ≤ m}(1 - δ_i(0))` equals `1`, since the factor `i = 0` of the product
vanishes. -/
lemma truncDataElem_at_zero (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (m : ℕ) (s : ↥S) :
    ((truncDataElem S x).1 m) ((((0 : ℕ) : ℕ∪{∞}), s)) = x.1 m s := by
  rw [truncDataElem_at]
  have hmem : 0 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.succ_pos m)
  have hprod : (∏ i ∈ Finset.range (m + 1),
      (1 - deltaFun i ((0 : ℕ) : ℕ∪{∞}))) = 0 := by
    refine Finset.prod_eq_zero hmem ?_
    rw [deltaFun_at, sub_self]
  rw [hprod, sub_zero, mul_one]

/-- **The zero slice of `truncDataElem S x` is `x`.**  The `m`-th component of `truncDataElem S x`
at `(0,s)` is `x_m(s)·[0 ≤ m] = x_m(s)`. -/
theorem truncDataElemZeroSlice : Work.ANALYTIC.TruncDataElemZeroSlice := by
  intro S x
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro s
  rw [boundedSeq_map_apply, zeroSlice_apply]
  exact truncDataElem_at_zero S x m s

end Work.ANALYTIC
