import Mathlib
import Submission.Commons.Combinatorics.Transference.davg_smul

namespace Commons.Combinatorics.Transference

theorem davg_div_bound {p : ℕ} [Fact p.Prime] {d : ℕ} {C : ℝ} (hC : 0 < C) (F : ZMod p → ℝ)
    {Mscaled : ℝ} (hM : ∀ x, |davg d (fun y => F y / (2 * C)) x| ≤ Mscaled) (x : ZMod p) :
    |davg d F x| ≤ (2 * C) ^ (2 ^ d - 1) * Mscaled := by
  have h2C : (0 : ℝ) < 2 * C := by linarith
  have hne : (2 * C) ≠ 0 := ne_of_gt h2C
  -- Homogeneity: scaling `F` by `(2*C)⁻¹` scales `davg` by `((2*C)⁻¹)^(2^d-1)`.
  have hcongr : (fun y => F y / (2 * C)) = fun y => (2 * C)⁻¹ * F y := by
    funext y; rw [div_eq_inv_mul]
  have hsmul := davg_smul (p := p) (d := d) ((2 * C)⁻¹) F
  have hsmul' : davg d (fun y => F y / (2 * C))
      = fun z => ((2 * C)⁻¹) ^ (2 ^ d - 1) * davg d F z := by
    rw [hcongr, hsmul]
  -- Undo the scaling.
  have hval : davg d F x = (2 * C) ^ (2 ^ d - 1) * davg d (fun y => F y / (2 * C)) x := by
    rw [congrFun hsmul' x]
    have : (2 * C) ^ (2 ^ d - 1) * (((2 * C)⁻¹) ^ (2 ^ d - 1) * davg d F x) = davg d F x := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul]
    rw [this]
  rw [hval, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt h2C) _)]
  exact mul_le_mul_of_nonneg_left (hM x) (pow_nonneg (le_of_lt h2C) _)

end Commons.Combinatorics.Transference
