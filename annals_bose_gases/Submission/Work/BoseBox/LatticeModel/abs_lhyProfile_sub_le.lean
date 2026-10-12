import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Submission.Work.BoseBox.LatticeModel.abs_lhyD_le
import Submission.Work.BoseBox.LatticeModel.hasDerivAt_lhyF
import Submission.Work.BoseBox.LatticeModel.lhyProfile_eq_lhyF
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lipschitz estimate for the Bogoliubov bracket `lhyProfile`

`lhyProfile c` is, on `(0,∞)`, the differentiable function `lhyF c` whose
derivative `lhyD c r` satisfies `|lhyD c r| ≤ c²/r³`.  The mean value theorem
applied on `[s,t] ⊂ (0,∞)` therefore gives, for `0 < s ≤ t`,

`|lhyProfile c t − lhyProfile c s| ≤ (c²/s³)·(t−s) ≤ 8·c²·(t−s)/s³`.
-/

noncomputable section

open scoped Real

namespace Work.BoseBox.LatticeModel

theorem abs_lhyProfile_sub_le {c : ℝ} (hc : 0 < c) :
    ∀ s t : ℝ, 0 < s → s ≤ t →
      |lhyProfile c t - lhyProfile c s| ≤ 8 * c ^ 2 * (t - s) / s ^ 3 := by
  intro s t hs hst
  rcases lt_or_eq_of_le hst with hlt | rfl
  · have hs3 : (0 : ℝ) < s ^ 3 := by positivity
    have hcont : ContinuousOn (lhyF c) (Set.Icc s t) := by
      intro x hx
      exact ((hasDerivAt_lhyF c x hc (lt_of_lt_of_le hs hx.1)).continuousAt).continuousWithinAt
    obtain ⟨ξ, hξ, hderiv⟩ := exists_hasDerivAt_eq_slope (lhyF c) (lhyD c) hlt hcont
      (fun x hx => hasDerivAt_lhyF c x hc (lt_of_lt_of_le hs (le_of_lt hx.1)))
    have hξs : s ≤ ξ := le_of_lt hξ.1
    have hξpos : 0 < ξ := lt_of_lt_of_le hs hξs
    have htpos : 0 < t := lt_of_lt_of_le hs (le_of_lt hlt)
    have hns : t - s ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
    have hts : (0 : ℝ) ≤ t - s := le_of_lt (sub_pos.mpr hlt)
    have h1 : lhyF c t - lhyF c s = lhyD c ξ * (t - s) := by
      rw [hderiv, div_mul_cancel₀ _ hns]
    have hDt : lhyProfile c t = lhyF c t := lhyProfile_eq_lhyF c t hc htpos
    have hDs : lhyProfile c s = lhyF c s := lhyProfile_eq_lhyF c s hc hs
    have hDbd : |lhyD c ξ| ≤ c ^ 2 / s ^ 3 := by
      refine le_trans (abs_lhyD_le c ξ hc hξpos) ?_
      have hξ3 : s ^ 3 ≤ ξ ^ 3 := pow_le_pow_left₀ hs.le hξs 3
      exact div_le_div_of_nonneg_left (by positivity) hs3 hξ3
    calc |lhyProfile c t - lhyProfile c s|
        = |lhyD c ξ| * (t - s) := by
          rw [hDt, hDs, h1, abs_mul, abs_of_nonneg hts]
      _ ≤ (c ^ 2 / s ^ 3) * (t - s) := mul_le_mul_of_nonneg_right hDbd hts
      _ ≤ 8 * c ^ 2 * (t - s) / s ^ 3 := by
          rw [show (c ^ 2 / s ^ 3) * (t - s) = c ^ 2 * (t - s) / s ^ 3 by ring,
              show 8 * c ^ 2 * (t - s) / s ^ 3 = (8 * (c ^ 2 * (t - s))) / s ^ 3 by ring]
          exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg c, hts]) hs3.le
  · simp

end Work.BoseBox.LatticeModel
