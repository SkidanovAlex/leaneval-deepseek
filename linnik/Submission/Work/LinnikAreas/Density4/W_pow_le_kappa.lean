import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_kappa_lower

namespace Work.LinnikAreas.Density4

/-- For `0 < σ ≤ 1` and `exp M ≤ A` we have `exp (σ M) ≤ 3 Γ(σ) A^σ`. -/
theorem W_pow_le_kappa (M σ A : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : Real.exp M ≤ A) :
    Real.exp (σ * M) ≤ 3 * (Real.Gamma σ * A ^ σ) := by
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos M) hA
  -- `exp (σ M) = (exp M)^σ ≤ A^σ`
  have hexp_le : Real.exp (σ * M) ≤ A ^ σ := by
    have h1 : (Real.exp M) ^ σ ≤ A ^ σ := Real.rpow_le_rpow (Real.exp_pos M).le hA hσ.le
    have h2 : (Real.exp M) ^ σ = Real.exp (M * σ) := by rw [← Real.exp_mul]
    rw [h2, mul_comm M σ] at h1
    exact h1
  have hGpos : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos hσ
  -- `Γ σ ≥ 1/3` from `σ Γ σ ≥ 1/3` and `σ ≤ 1`
  have hthird : (1:ℝ)/3 ≤ Real.Gamma σ := by
    have h := Gamma_ge_inv_three_mul σ hσ hσ1
    have hle : σ * Real.Gamma σ ≤ Real.Gamma σ := mul_le_of_le_one_left hGpos.le hσ1
    linarith
  have hone : (1:ℝ) ≤ 3 * Real.Gamma σ := by linarith
  have hAσnonneg : (0:ℝ) ≤ A ^ σ := Real.rpow_nonneg hApos.le σ
  calc Real.exp (σ * M) ≤ A ^ σ := hexp_le
    _ = 1 * A ^ σ := (one_mul _).symm
    _ ≤ (3 * Real.Gamma σ) * A ^ σ := mul_le_mul_of_nonneg_right hone hAσnonneg
    _ = 3 * (Real.Gamma σ * A ^ σ) := by ring

end Work.LinnikAreas.Density4
