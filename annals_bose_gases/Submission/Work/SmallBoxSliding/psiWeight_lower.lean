import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

lemma psiWeight_lower {c μ t : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (ht0 : 0 ≤ t) (ht : t ≤ 2 * μ) :
    c * (t - μ) ^ 2 / 3 ≤ Work.SmallBoxSliding.psiWeight c μ t := by
  unfold psiWeight
  have hA : 0 ≤ c * (t - μ) ^ 2 := mul_nonneg hc (sq_nonneg _)
  have hμinv : 0 < μ⁻¹ := inv_pos.mpr hμ
  have hBpos : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht0 (le_of_lt hμinv)
    linarith
  have hBle : 1 + t * μ⁻¹ ≤ 3 := by
    have h2 : t * μ⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hμ]
      linarith
    linarith
  exact div_le_div_of_nonneg_left hA hBpos hBle

end Work.SmallBoxSliding
