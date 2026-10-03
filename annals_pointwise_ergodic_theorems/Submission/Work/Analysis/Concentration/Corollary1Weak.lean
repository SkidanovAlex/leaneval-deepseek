/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.Analysis.Concentration.PrimeUniform
import Submission.Work.Analysis.Concentration.fiberLpBound_of_fiberWeakType

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# From the weak-type concentration bound to the `L^s` concentration bound (uniformly in the prime)

Appendix C proves the concentration estimate in the weak-type form (Proposition `prop:zero`(iii),
Corollary `cor:1`) and deduces from it the `L^s` form `‖h‖_{L^s(ℤ/p^jℤ)} ≲_{s,P} 1`.  This file
performs that deduction at the level of the statements recorded in `PrimeUniform`: the layer-cake
argument is the companion lemma `fiberLpBound_of_fiberWeakType`, and the constant it produces
(`fiberWeakTypeConstant`) depends only on the weak-type constant, so the resulting estimate is
uniform in the prime power.
-/

set_option autoImplicit false

namespace Work.Analysis.Concentration

open Polynomial Finset

noncomputable section

/-- The constant produced by the layer cake is positive. -/
lemma fiberWeakTypeConstant_pos {d s C : ℝ} (hd : 1 < d) (hs : 1 ≤ s) (hsd : s < d / (d - 1))
    (hC : 0 ≤ C) : 0 < fiberWeakTypeConstant d s C := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hα : 0 < d / (d - 1) := div_pos (by linarith) (by linarith)
  have hT : 1 ≤ max 1 (C ^ (1 / (d / (d - 1)))) := le_max_left _ _
  have hrpow : 0 < s * (max 1 (C ^ (1 / (d / (d - 1))))) ^ s :=
    mul_pos hs0 (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) s)
  have hsum : 0 < s * (max 1 (C ^ (1 / (d / (d - 1))))) ^ s
      + s * C * (max 1 (C ^ (1 / (d / (d - 1))))) ^ (s - d / (d - 1)) / (d / (d - 1) - s) := by
    refine add_pos_of_pos_of_nonneg hrpow ?_
    refine div_nonneg ?_ (by linarith)
    exact mul_nonneg (mul_nonneg hs0.le hC)
      (Real.rpow_nonneg (le_trans zero_le_one hT) _)
  unfold fiberWeakTypeConstant
  exact Real.rpow_pos_of_pos hsum _

/-- For `0 < s ≤ 1` the `L^s` concentration bound holds with constant `1`: this is just
`∑_y h(y)^s ≤ ∑_y h(y) = Q` (used for the exponents below the range of the layer cake). -/
lemma fiberLpBound_of_le_one {P : Polynomial ℤ} {Q : ℕ} [NeZero Q] {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) : FiberLpBound P Q s 1 := by
  unfold FiberLpBound
  have hsum : ∑ y : ZMod Q, (polyFiberCard P Q y : ℝ) ^ s
      ≤ ∑ y : ZMod Q, (polyFiberCard P Q y : ℝ) := by
    refine Finset.sum_le_sum (fun y _ => ?_)
    have h0 : (0 : ℝ) ≤ (polyFiberCard P Q y : ℝ) := by positivity
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h, Real.zero_rpow (ne_of_gt hs0)]
    · have hy1 : (1 : ℝ) ≤ (polyFiberCard P Q y : ℝ) := by
        have : 0 < polyFiberCard P Q y := by exact_mod_cast h
        exact_mod_cast this
      calc (polyFiberCard P Q y : ℝ) ^ s ≤ (polyFiberCard P Q y : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hy1 hs1
        _ = (polyFiberCard P Q y : ℝ) := Real.rpow_one _
  rw [Real.one_rpow, one_mul]
  exact hsum.trans (le_of_eq (by rw [← Nat.cast_sum, fiber_card_sum]))

/-- **Appendix C, Corollary `cor:1`, from its weak-type form.**  If the weak-type concentration
bound holds with a constant independent of the prime power, then so does the `L^s` form. -/
theorem corollary1_of_weakType {P : Polynomial ℤ} {d : ℕ} (hd : 1 < d)
    (h : Corollary1WeakType P d) : Corollary1 P d := by
  obtain ⟨C, hC, hCb⟩ := h
  intro s hs0 hsd
  by_cases hs1 : 1 ≤ s
  · refine ⟨fiberWeakTypeConstant (d : ℝ) s C,
      fiberWeakTypeConstant_pos (by exact_mod_cast hd) hs1 hsd hC.le, fun p j _ hj => ?_⟩
    exact fiberLpBound_of_fiberWeakType (by exact_mod_cast hd) hC.le (hCb p j hj) hs1 hsd
  · exact ⟨1, one_pos, fun p j _ hj =>
      fiberLpBound_of_le_one hs0 (le_of_lt (not_le.mp hs1))⟩

end

end Work.Analysis.Concentration
