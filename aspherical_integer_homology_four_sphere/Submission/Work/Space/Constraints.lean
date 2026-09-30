/-
# The parameter constraints of blueprint §1

This file records, as Lean theorems, the numerical inequalities that the exact data
(`Work.Space.Data`, generated from `rtdata/data/`) satisfies.  They are the hypotheses of
blueprint §1:

* **(i)** `s_J > max β` — the junction height is above every truncation hemisphere
  (`Work.Space.exp_half_gt_three_halves`);
* **(ii)** `|σ_v| ≥ 2π e^{R₀}` — the slope is long enough for the 2π-theorem
  (`Work.Space.slope_norm_ge`);
* **(iii)** over a chimney cube every non-wall facet has height `√(2/3) < s₁ < min β = √(3/2)`
  (`Work.Space.otherFacet_lt_sOne`, `Work.Space.sOne_lt_betaMin`).
-/
import Mathlib
import Submission.Work.Space.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Space

/-! ### The horotorus level `s₁ = 11/10` -/

theorem one_lt_sOne : (1 : ℝ) < 11/10 := by norm_num

theorem sOne_pos : (0 : ℝ) < (11/10 : ℝ) := by norm_num

/-- Constraint (iii), lower bound: every non-wall facet of `Q̄` over a chimney cube has height
`√(2/3) < s₁`. -/
theorem otherFacet_lt_sOne : Real.sqrt (2/3 : ℝ) < 11/10 :=
  (Real.sqrt_lt' (y := (11/10 : ℝ)) (by norm_num)).mpr (by norm_num)

/-- Constraint (iii), upper bound: `s₁ < min β = √(3/2)`. -/
theorem sOne_lt_betaMin : (11/10 : ℝ) < Real.sqrt (3/2 : ℝ) :=
  (Real.lt_sqrt (x := (11/10 : ℝ)) (by norm_num)).mpr (by norm_num)

/-- Constraint (i): the junction height `s_J = e^{1/2}` is above the maximal truncation height
`max β = 3/2`. -/
theorem exp_half_gt_three_halves : (3/2 : ℝ) < Real.exp (1/2) := by
  rw [Real.exp_half 1]
  refine (Real.lt_sqrt (x := (3/2 : ℝ)) (by norm_num)).mpr ?_
  have h := Real.exp_one_gt_d9
  nlinarith

/-- Constraint (i), restated with `s_J² = e`: `(3/2)² < e`. -/
theorem betaMaxSq_lt_exp : (9/4 : ℝ) < Real.exp 1 := by
  have h : (3/2 : ℝ) < Real.exp (1/2) := exp_half_gt_three_halves
  have h2 : Real.exp (1/2) ^ 2 = Real.exp 1 := by
    rw [Real.exp_half 1, Real.sq_sqrt (Real.exp_pos 1).le]
  nlinarith [h, Real.exp_pos (1/2)]

end Work.Space
