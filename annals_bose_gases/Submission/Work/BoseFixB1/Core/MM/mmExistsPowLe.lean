import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Core.MM

theorem mmExistsPowLe {K p : ℝ} (hK : 0 ≤ K) (hp : 0 < p) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, 0 < x → x ≤ x₀ → K * x ^ p ≤ 1 := by
  have hp' : (1 / p) * p = 1 := by field_simp
  refine ⟨(1 / (K + 1)) ^ (1 / p), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro x hx hxle
  have h1 : x ^ p ≤ ((1 / (K + 1)) ^ (1 / p)) ^ p := Real.rpow_le_rpow hx.le hxle hp.le
  have h2 : ((1 / (K + 1)) ^ (1 / p)) ^ p = 1 / (K + 1) := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / (K + 1)), hp', Real.rpow_one]
  have h3 : K * x ^ p ≤ K * (1 / (K + 1)) := by
    apply mul_le_mul_of_nonneg_left _ hK
    rw [← h2]
    exact h1
  have h4 : K * (1 / (K + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]
    linarith
  linarith

end Work.BoseFixB1.Core.MM
