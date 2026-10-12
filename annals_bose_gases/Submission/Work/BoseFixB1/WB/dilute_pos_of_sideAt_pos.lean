import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.WB

/-- **Positivity of the box side forces positivity of the diluteness.**

`sideAt μ a = K_ℓ(μa³)·(μa)^{-1/2}` (`Work.BoseBox.sideAt`, `Work.BoseBox.boxSide`),
so `0 < sideAt μ a` can only happen when the side really is a length: the factor
`(μa)^{-1/2}` has to be nonzero, and by the real-`rpow` conventions this happens
exactly for `0 < μa`.  Then `a ≠ 0` and `μa³ = (μa)·a² > 0`.

(No hypothesis on `K_ℓ` is needed: when `μa ≤ 0` the second factor *vanishes* —
`(μa)^{-1/2} = 0` for `μa < 0` because `cos(-π/2) = 0` in `Real.rpow_def_of_neg`,
and `0^{-1/2} = 0` — so the side is `K_ℓ·0 = 0`, never positive.) -/
theorem dilute_pos_of_sideAt_pos {μ a : ℝ} (h : 0 < Work.BoseBox.sideAt μ a) :
    0 < μ * a ^ 3 := by
  by_contra hle
  push Not at hle
  rcases le_or_gt (μ * a) 0 with hμa | hμa
  · -- The side is zero: the second factor vanishes.
    have hz : (μ * a) ^ (-(1 / 2 : ℝ)) = 0 := by
      rcases lt_or_eq_of_le hμa with hlt | heq
      · rw [Real.rpow_def_of_neg hlt]
        have hy : (-(1 / 2 : ℝ)) * Real.pi = -(Real.pi / 2) := by ring
        rw [hy, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
      · rw [heq, Real.zero_rpow]
        norm_num
    have h0 : Work.BoseBox.sideAt μ a = 0 := by
      rw [Work.BoseBox.sideAt, Work.BoseBox.boxSide, hz, mul_zero]
    rw [h0] at h
    exact lt_irrefl 0 h
  · -- `0 < μa` forces `a ≠ 0`, hence `μa³ = (μa)·a² > 0`.
    have ha : a ≠ 0 := by rintro rfl; simp at hμa
    have hpos : 0 < (μ * a) * a ^ 2 := mul_pos hμa (sq_pos_of_ne_zero ha)
    have he : μ * a ^ 3 = (μ * a) * a ^ 2 := by ring
    rw [he] at hle
    linarith

end Work.BoseFixB1.WB
