import Mathlib
import Submission.Work.CNum.C2_setup

namespace Work.CNum

open Complex

/-- On the `C₂` arc, `cos(θ/2)/C` lies in `[-1,1]`. -/
lemma C2_cos_half_div_bounds {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    -1 ≤ Real.cos (θ / 2) / C2C ∧ Real.cos (θ / 2) / C2C ≤ 1 := by
  have hle := C2_cos_sq_half_le h
  have habs : |Real.cos (θ / 2)| ≤ C2C := by
    rw [← Real.sqrt_sq_eq_abs (Real.cos (θ / 2))]
    calc Real.sqrt (Real.cos (θ / 2) ^ 2) ≤ Real.sqrt (C2C ^ 2) := Real.sqrt_le_sqrt hle
      _ = C2C := Real.sqrt_sq C2C_pos.le
  obtain ⟨h1, h2⟩ := abs_le.mp habs
  exact ⟨(le_div_iff₀ C2C_pos).mpr (by linarith), (div_le_iff₀ C2C_pos).mpr (by linarith)⟩

theorem C2_ratio_eq {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    ((C2u θ : ℂ) + (C2v θ : ℂ) * Complex.I) / (C2C : ℂ) =
      Complex.exp (Complex.I * (C2Psi (θ / 2) : ℂ)) := by
  obtain ⟨hb1, hb2⟩ := C2_cos_half_div_bounds h
  have hCne : C2C ≠ 0 := C2C_ne_zero
  set φ := Real.arcsin (Real.cos (θ / 2) / C2C) with hφ
  have hsinφ : Real.sin φ = Real.cos (θ / 2) / C2C := Real.sin_arcsin hb1 hb2
  have hcosφ_nn : 0 ≤ Real.cos φ :=
    Real.cos_nonneg_of_mem_Icc (x := φ) (by rw [hφ]; exact Real.arcsin_mem_Icc _)
  have hcosφ_sq : Real.cos φ ^ 2 = 1 - (Real.cos (θ / 2) / C2C) ^ 2 := by
    have h1 := Real.sin_sq_add_cos_sq φ
    rw [hsinφ] at h1
    linarith
  have hrad : 0 ≤ Real.sin (θ / 2) ^ 2 - C2σ ^ 2 := by
    have hlt := C2σ_lt_sin_half h
    nlinarith [C2σ_pos, hlt]
  have hw_sq : C2w θ ^ 2 = Real.sin (θ / 2) ^ 2 - C2σ ^ 2 := by
    rw [C2w, Real.sq_sqrt hrad]
  have hCcosφ_sq : (C2C * Real.cos φ) ^ 2 = Real.sin (θ / 2) ^ 2 - C2σ ^ 2 := by
    rw [mul_pow, hcosφ_sq]
    have h1 : C2C ^ 2 * (1 - (Real.cos (θ / 2) / C2C) ^ 2)
        = C2C ^ 2 - Real.cos (θ / 2) ^ 2 := by
      field_simp
    rw [h1]
    have h2 := C2C_sq_add
    have h3 := Real.sin_sq_add_cos_sq (θ / 2)
    nlinarith [h2, h3]
  have hCcosφ : C2C * Real.cos φ = C2w θ := by
    have hsq : (C2C * Real.cos φ) ^ 2 = C2w θ ^ 2 := by rw [hCcosφ_sq, hw_sq]
    have hwpos := C2w_pos h
    have hnn : 0 ≤ C2C * Real.cos φ := mul_nonneg C2C_pos.le hcosφ_nn
    have h2 : (C2C * Real.cos φ - C2w θ) * (C2C * Real.cos φ + C2w θ) = 0 := by
      nlinarith [hsq]
    have hpos : 0 < C2C * Real.cos φ + C2w θ := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · linarith
  have hCsinφ : C2C * Real.sin φ = Real.cos (θ / 2) := by
    rw [hsinφ]; exact mul_div_cancel₀ _ C2C_ne_zero
  have hcosΨ : Real.cos (C2Psi (θ / 2)) =
      Real.sin (θ / 2) * Real.cos φ + Real.cos (θ / 2) * Real.sin φ := by
    rw [C2Psi, ← hφ,
      show θ / 2 - Real.pi / 2 + φ = (θ / 2 - Real.pi / 2) + φ by ring,
      Real.cos_add, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    ring
  have hsinΨ : Real.sin (C2Psi (θ / 2)) =
      Real.sin (θ / 2) * Real.sin φ - Real.cos (θ / 2) * Real.cos φ := by
    rw [C2Psi, ← hφ,
      show θ / 2 - Real.pi / 2 + φ = (θ / 2 - Real.pi / 2) + φ by ring,
      Real.sin_add, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two]
    ring
  have hu : C2C * Real.cos (C2Psi (θ / 2)) = C2u θ := by
    rw [hcosΨ, C2u]
    have : C2C * (Real.sin (θ / 2) * Real.cos φ + Real.cos (θ / 2) * Real.sin φ)
        = Real.sin (θ / 2) * (C2C * Real.cos φ) + Real.cos (θ / 2) * (C2C * Real.sin φ) := by
      ring
    rw [this, hCcosφ, hCsinφ]
    ring
  have hv : C2C * Real.sin (C2Psi (θ / 2)) = C2v θ := by
    rw [hsinΨ, C2v]
    have : C2C * (Real.sin (θ / 2) * Real.sin φ - Real.cos (θ / 2) * Real.cos φ)
        = Real.sin (θ / 2) * (C2C * Real.sin φ) - Real.cos (θ / 2) * (C2C * Real.cos φ) := by
      ring
    rw [this, hCsinφ, hCcosφ]
    ring
  have hexp : Complex.exp (Complex.I * (C2Psi (θ / 2) : ℂ)) =
      (Real.cos (C2Psi (θ / 2)) : ℂ) + (Real.sin (C2Psi (θ / 2)) : ℂ) * Complex.I := by
    rw [mul_comm]
    exact Complex.exp_ofReal_mul_I _
  rw [← hu, ← hv, hexp]
  have hCneC : (C2C : ℂ) ≠ 0 := by exact_mod_cast C2C_ne_zero
  field_simp
  push_cast
  ring

end Work.CNum
