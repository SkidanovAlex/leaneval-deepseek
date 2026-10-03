import Mathlib

namespace Work.Pert

/-- Perturbation bound (Shishikura, Appendix A.1): if `1 - σ·u(0) = exp(2πi α)` with
`‖α‖ ≤ 1/(2π)` and `‖u(0) - 1‖ ≤ 1/2`, then `σ/α` is `2πi` up to an error of order
`‖α‖ + ‖u(0) - 1‖`, and `σ` inherits the corresponding bound. -/
theorem sigma_alpha_close {u : ℂ → ℂ} {σ α : ℂ}
    (hα : α ≠ 0) (hαs : ‖α‖ ≤ 1 / (2 * Real.pi)) (hu0 : ‖u 0 - 1‖ ≤ 1 / 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α)) :
    ‖σ / α + 2 * Real.pi * Complex.I‖ ≤ 8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u 0 - 1‖ ∧
      ‖σ‖ ≤ ‖α‖ * (8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u 0 - 1‖ + 2 * Real.pi) := by
  set z : ℂ := 2 * Real.pi * Complex.I * α with hz
  have hzn : ‖z‖ = 2 * Real.pi * ‖α‖ := by
    rw [hz]; simp [Complex.norm_I, Real.norm_of_nonneg Real.pi_pos.le]
  have hz1 : ‖z‖ ≤ 1 := by
    rw [hzn]
    have h : 2 * Real.pi * ‖α‖ ≤ 2 * Real.pi * (1 / (2 * Real.pi)) := by gcongr
    have h2 : 2 * Real.pi * (1 / (2 * Real.pi)) = 1 := by field_simp
    linarith
  have hu0norm : (1 : ℝ) / 2 ≤ ‖u 0‖ := by
    have h := abs_norm_sub_norm_le (u 0) 1
    rw [norm_one] at h
    have h' := (abs_le.mp h).1
    linarith
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hu0nz : u 0 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hu0norm; linarith
  have hsig : σ = (1 - Complex.exp z) / u 0 := by
    have h : σ * u 0 = 1 - Complex.exp z := by rw [← hnorm]; ring
    exact (eq_div_iff hu0nz).mpr h
  have hkey : σ / α + 2 * Real.pi * Complex.I = (1 - Complex.exp z + z * u 0) / (α * u 0) := by
    rw [hsig]; field_simp; rw [hz]; ring
  have hnum : ‖1 - Complex.exp z + z * u 0‖
      ≤ 4 * Real.pi ^ 2 * ‖α‖ ^ 2 + 2 * Real.pi * ‖α‖ * ‖u 0 - 1‖ := by
    have heq : 1 - Complex.exp z + z * u 0 = (1 - Complex.exp z + z) + z * (u 0 - 1) := by ring
    calc ‖1 - Complex.exp z + z * u 0‖
        = ‖(1 - Complex.exp z + z) + z * (u 0 - 1)‖ := by rw [heq]
      _ ≤ ‖1 - Complex.exp z + z‖ + ‖z * (u 0 - 1)‖ := norm_add_le _ _
      _ = ‖Complex.exp z - 1 - z‖ + ‖z‖ * ‖u 0 - 1‖ := by
            rw [norm_mul]
            congr 1
            have h2 : (1 - Complex.exp z + z : ℂ) = -(Complex.exp z - 1 - z) := by ring
            rw [h2, norm_neg]
      _ ≤ ‖z‖ ^ 2 + ‖z‖ * ‖u 0 - 1‖ := by
            gcongr
            exact Complex.norm_exp_sub_one_sub_id_le hz1
      _ = 4 * Real.pi ^ 2 * ‖α‖ ^ 2 + 2 * Real.pi * ‖α‖ * ‖u 0 - 1‖ := by
            rw [hzn]; ring
  have hden : ‖α * u 0‖ ≥ ‖α‖ / 2 := by
    rw [norm_mul]; nlinarith [norm_nonneg α]
  have hhalfpos : 0 < ‖α‖ / 2 := by linarith
  have hDpos : 0 < ‖α * u 0‖ := by linarith
  have h1 : ‖σ / α + 2 * Real.pi * Complex.I‖
      ≤ 8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u 0 - 1‖ := by
    rw [hkey, norm_div]
    calc ‖1 - Complex.exp z + z * u 0‖ / ‖α * u 0‖
        ≤ ‖1 - Complex.exp z + z * u 0‖ / (‖α‖ / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) hhalfpos hden
      _ ≤ (4 * Real.pi ^ 2 * ‖α‖ ^ 2 + 2 * Real.pi * ‖α‖ * ‖u 0 - 1‖) / (‖α‖ / 2) :=
          div_le_div_of_nonneg_right hnum hhalfpos.le
      _ = 8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u 0 - 1‖ := by
          rw [div_eq_iff (by linarith : ‖α‖ / 2 ≠ 0)]
          ring
  have h2 : ‖σ‖ ≤ ‖α‖ * (8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u 0 - 1‖ + 2 * Real.pi) := by
    have heq2 : σ = α * (σ / α + 2 * Real.pi * Complex.I) - α * (2 * Real.pi * Complex.I) := by
      field_simp
      ring
    have hnorm2piI : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [Complex.norm_I, Real.norm_of_nonneg Real.pi_pos.le]
    calc ‖σ‖ = ‖α * (σ / α + 2 * Real.pi * Complex.I) - α * (2 * Real.pi * Complex.I)‖ :=
          congrArg (fun x : ℂ => ‖x‖) heq2
      _ ≤ ‖α * (σ / α + 2 * Real.pi * Complex.I)‖ + ‖α * (2 * Real.pi * Complex.I)‖ :=
          norm_sub_le _ _
      _ = ‖α‖ * ‖σ / α + 2 * Real.pi * Complex.I‖ + ‖α‖ * ‖(2 * Real.pi * Complex.I : ℂ)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖α‖ * (8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u 0 - 1‖) + ‖α‖ * (2 * Real.pi) := by
          rw [hnorm2piI]
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg α)) (le_refl _)
      _ = ‖α‖ * (8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u 0 - 1‖ + 2 * Real.pi) := by ring
  exact ⟨h1, h2⟩

end Work.Pert
