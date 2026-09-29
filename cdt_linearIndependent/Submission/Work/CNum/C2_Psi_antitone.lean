import Mathlib
import Submission.Work.CNum.C2_setup

/-!
# `Work.CNum.C2_Psi_antitone`

`C2Psi t = t - π/2 + arcsin (cos t / C)`, where `C = C2C = cos(α/2)` and `α = alpR`,
is strictly antitone on the interval `(α/2, π - α/2)`.

Indeed, on that interval `|cos t| < C`, so `C2Psi` is differentiable there with

  `C2Psi' t = 1 - sin t / √(C² - cos² t)`,

and since `sin² t + cos² t = 1 > C²` we get `√(C² - cos² t) < sin t`, hence the
derivative is negative.  Strict antitonicity follows from
`strictAntiOn_of_deriv_neg`.
-/

namespace Work.CNum

noncomputable section

open Real

/-! ## Elementary facts on the interval `(α/2, π - α/2)` -/

/-- On `(α/2, π - α/2)`, `sin t > σ = sin(α/2)`. -/
private lemma C2σ_lt_sin_of_mem {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) : C2σ < Real.sin t := by
  have h := C2σ_lt_sin_half (show (2 * t) ∈ Set.Ioo alpR (2 * Real.pi - alpR) from
    ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  simpa [mul_div_cancel_left₀] using h

/-- On `(α/2, π - α/2)`, `cos t ^ 2 < C2C ^ 2`. -/
private lemma cos_sq_lt_C2C_sq_of_mem {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) : Real.cos t ^ 2 < C2C ^ 2 := by
  have hsin := C2σ_lt_sin_of_mem ht
  have h1 : C2σ ^ 2 < Real.sin t ^ 2 := by nlinarith [C2σ_pos.le, hsin]
  have h2 : Real.cos t ^ 2 = 1 - Real.sin t ^ 2 := by linarith [Real.sin_sq_add_cos_sq t]
  rw [h2, ← one_sub_C2σ_sq]; linarith

/-- `√(1 - (cos t / C)²) = √(C² - cos² t) / C` on the interval. -/
private lemma sqrt_one_sub_sq {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) :
    Real.sqrt (1 - (Real.cos t / C2C) ^ 2)
      = Real.sqrt (C2C ^ 2 - Real.cos t ^ 2) / C2C := by
  have hcos := cos_sq_lt_C2C_sq_of_mem ht
  have hC2 : (1 - (Real.cos t / C2C) ^ 2) = (C2C ^ 2 - Real.cos t ^ 2) / C2C ^ 2 := by
    field_simp [C2C_ne_zero]
  rw [hC2, Real.sqrt_div (by linarith [hcos]) (C2C ^ 2), Real.sqrt_sq C2C_pos.le]

/-- The chain-rule factor simplifies to `- sin t / √(C² - cos² t)`. -/
private lemma chain_val_eq {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) :
    (1 / Real.sqrt (1 - (Real.cos t / C2C) ^ 2)) * (-(Real.sin t) / C2C)
      = -(Real.sin t / Real.sqrt (C2C ^ 2 - Real.cos t ^ 2)) := by
  rw [sqrt_one_sub_sq ht]
  field_simp [C2C_ne_zero]

/-! ## Differentiability and the sign of the derivative -/

/-- `C2Psi` is differentiable on the interval, with the stated derivative. -/
private lemma hasDerivAt_C2Psi {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) :
    HasDerivAt C2Psi
      (1 + (1 / Real.sqrt (1 - (Real.cos t / C2C) ^ 2)) * (-(Real.sin t) / C2C)) t := by
  have hcos_lt := cos_sq_lt_C2C_sq_of_mem ht
  have hne1 : Real.cos t / C2C ≠ 1 := by
    intro h
    have h' := (div_eq_one_iff_eq C2C_ne_zero).mp h
    rw [h'] at hcos_lt; exact absurd hcos_lt (lt_irrefl _)
  have hne_neg1 : Real.cos t / C2C ≠ -1 := by
    intro h
    have h' : Real.cos t = -C2C := by
      rw [div_eq_iff C2C_ne_zero] at h; linarith
    rw [h'] at hcos_lt
    nlinarith [hcos_lt]
  have hid : HasDerivAt (fun s => s - Real.pi / 2) 1 t :=
    (hasDerivAt_id t).sub_const (Real.pi / 2)
  have harc : HasDerivAt (fun s => Real.arcsin (Real.cos s / C2C))
      ((1 / Real.sqrt (1 - (Real.cos t / C2C) ^ 2)) * (-(Real.sin t) / C2C)) t := by
    have hcos : HasDerivAt (fun s => Real.cos s / C2C) (-(Real.sin t) / C2C) t :=
      (Real.hasDerivAt_cos t).div_const C2C
    have h2 := (Real.hasDerivAt_arcsin hne_neg1 hne1).comp t hcos
    simpa only [Function.comp_def] using h2
  exact hid.add harc

/-- `deriv C2Psi t = 1 - sin t / √(C² - cos² t)` on the interval. -/
private lemma deriv_C2Psi {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) :
    deriv C2Psi t = 1 - Real.sin t / Real.sqrt (C2C ^ 2 - Real.cos t ^ 2) := by
  rw [(hasDerivAt_C2Psi ht).deriv, chain_val_eq ht]
  ring

/-- The derivative is negative on the interval. -/
private lemma deriv_C2Psi_neg {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) : deriv C2Psi t < 0 := by
  rw [deriv_C2Psi ht]
  have hsin := C2σ_lt_sin_of_mem ht
  have hcos := cos_sq_lt_C2C_sq_of_mem ht
  have hsinpos : 0 < Real.sin t := by linarith [C2σ_pos]
  have hpos : 0 < Real.sqrt (C2C ^ 2 - Real.cos t ^ 2) := Real.sqrt_pos.mpr (by linarith [hcos])
  have hsq_lt : Real.sqrt (C2C ^ 2 - Real.cos t ^ 2) < Real.sin t := by
    rw [Real.sqrt_lt' hsinpos]
    have h1 : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
    have h2 : C2C ^ 2 < 1 := by norm_num [C2C]
    linarith
  have : 1 < Real.sin t / Real.sqrt (C2C ^ 2 - Real.cos t ^ 2) := by
    rw [one_lt_div hpos]; linarith
  linarith

/-! ## The main theorem -/

theorem C2_Psi_antitone :
    StrictAntiOn C2Psi (Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) ?_ ?_
  · apply Continuous.continuousOn
    unfold C2Psi
    continuity
  · intro x hx
    rw [interior_Ioo] at hx
    exact deriv_C2Psi_neg hx

end

end Work.CNum
