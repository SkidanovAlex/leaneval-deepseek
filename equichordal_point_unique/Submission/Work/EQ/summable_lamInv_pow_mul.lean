import Mathlib

namespace Work.EQ

/-- The geometric series of ratio `lam ^ 2` converges when `0 < lam < 1`. -/
lemma summable_pow_lam_sq {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Summable (fun k : ℕ => (lam ^ 2) ^ k) :=
  summable_geometric_of_lt_one (sq_nonneg lam) (by nlinarith [sq_nonneg lam])

/-- The terms `lam^{-2k} * F (lam^{2k} * u)` are dominated, in norm, by the
convergent geometric series `C * ‖u‖² * (lam²)^k`. -/
lemma norm_lamInv_pow_mul_le {lam R C : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {F : ℂ → ℂ} (hF : ∀ z, ‖z‖ < R → ‖F z‖ ≤ C * ‖z‖ ^ 2) (u : ℂ) (hu : ‖u‖ < R) (k : ℕ) :
    ‖(((lam : ℂ) ^ (2 * k))⁻¹) * F (((lam : ℂ) ^ (2 * k)) * u)‖
      ≤ C * ‖u‖ ^ 2 * (lam ^ 2) ^ k := by
  have hlamcast : ‖(lam : ℂ)‖ = lam := Complex.norm_of_nonneg hlam0.le
  have hnorm_a : ‖((lam : ℂ) ^ (2 * k))‖ = lam ^ (2 * k) := by
    rw [norm_pow, hlamcast]
  have hpos : 0 < lam ^ (2 * k) := pow_pos hlam0 _
  have hle1 : lam ^ (2 * k) ≤ 1 := pow_le_one₀ hlam0.le hlam1.le
  have hnorm_zu : ‖((lam : ℂ) ^ (2 * k)) * u‖ = lam ^ (2 * k) * ‖u‖ := by
    rw [norm_mul, hnorm_a]
  have hzed : ‖((lam : ℂ) ^ (2 * k)) * u‖ < R := by
    rw [hnorm_zu]
    calc lam ^ (2 * k) * ‖u‖ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hle1 (norm_nonneg u)
      _ = ‖u‖ := one_mul _
      _ < R := hu
  have hFz := hF _ hzed
  have hnonneg : 0 ≤ (lam ^ (2 * k))⁻¹ := inv_nonneg.mpr hpos.le
  have heq : (lam ^ (2 * k))⁻¹ * (C * ‖((lam : ℂ) ^ (2 * k)) * u‖ ^ 2)
      = C * ‖u‖ ^ 2 * (lam ^ 2) ^ k := by
    rw [hnorm_zu, pow_mul]
    have hne : (lam ^ 2) ^ k ≠ 0 := by positivity
    field_simp
  rw [norm_mul, norm_inv, hnorm_a]
  calc (lam ^ (2 * k))⁻¹ * ‖F (((lam : ℂ) ^ (2 * k)) * u)‖
      ≤ (lam ^ (2 * k))⁻¹ * (C * ‖((lam : ℂ) ^ (2 * k)) * u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hFz hnonneg
    _ = C * ‖u‖ ^ 2 * (lam ^ 2) ^ k := heq

theorem summable_lamInv_pow_mul {lam R C : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R)
    {F : ℂ → ℂ} (hF : ∀ z, ‖z‖ < R → ‖F z‖ ≤ C * ‖z‖ ^ 2) (u : ℂ) (hu : ‖u‖ < R) :
    Summable (fun k : ℕ => (((lam : ℂ) ^ (2 * k))⁻¹) * F (((lam : ℂ) ^ (2 * k)) * u)) := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => C * ‖u‖ ^ 2 * (lam ^ 2) ^ k) ?_ ?_
  · exact (summable_pow_lam_sq hlam0 hlam1).mul_left _
  · intro k
    exact norm_lamInv_pow_mul_le hlam0 hlam1 hF u hu k

end Work.EQ
