import Mathlib
import Submission.Work.CNum.C2_Psi_antitone
import Submission.Work.CNum.C2_Psi_mem
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.AlpBound

/-!
# `Work.CNum.PsiRange`

`C2Psi t = t - π/2 + arcsin (cos t / C)`, where `C = C2C = cos(α/2)` and `α = alpR`.

On the *closed* interval `[α/2, π - α/2]` the function `C2Psi` takes its values in
`[-α/2, α/2]`: it is strictly antitone there (the derivative is computed on the open
interval `(α/2, π - α/2)`, where it is negative), with endpoint values

* `C2Psi (α/2) = α/2`      (because `cos (α/2) / C = 1`),
* `C2Psi (π - α/2) = -α/2` (because `cos (π - α/2) / C = -1`).

Together with `1.4973 < α < 1.5031` (`AlpBound`) and `3.1415 < π < 3.1416`
(`Real.pi_gt_d4`, `Real.pi_lt_d4`) this yields

  `-3.9 ≤ C2Psi (θ/2) - π ≤ -2.39`   for `α ≤ θ ≤ 2π - α`.
-/

namespace Work.CNum

noncomputable section

open Real

/-! ## Elementary facts on the interval `(α/2, π - α/2)` -/

private lemma Psi_sigma_lt_sin {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) : C2σ < Real.sin t := by
  have h := C2σ_lt_sin_half (show (2 * t) ∈ Set.Ioo alpR (2 * Real.pi - alpR) from
    ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  simpa [mul_div_cancel_left₀] using h

private lemma Psi_cos_sq_lt {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) : Real.cos t ^ 2 < C2C ^ 2 := by
  have hsin := Psi_sigma_lt_sin ht
  have h1 : C2σ ^ 2 < Real.sin t ^ 2 := by nlinarith [C2σ_pos.le, hsin]
  have h2 : Real.cos t ^ 2 = 1 - Real.sin t ^ 2 := by linarith [Real.sin_sq_add_cos_sq t]
  rw [h2, ← one_sub_C2σ_sq]; linarith

private lemma Psi_sqrt_one_sub_sq {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) :
    Real.sqrt (1 - (Real.cos t / C2C) ^ 2)
      = Real.sqrt (C2C ^ 2 - Real.cos t ^ 2) / C2C := by
  have hcos := Psi_cos_sq_lt ht
  have hC2 : (1 - (Real.cos t / C2C) ^ 2) = (C2C ^ 2 - Real.cos t ^ 2) / C2C ^ 2 := by
    field_simp [C2C_ne_zero]
  rw [hC2, Real.sqrt_div (by linarith [hcos]) (C2C ^ 2), Real.sqrt_sq C2C_pos.le]

private lemma Psi_chain_val_eq {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) :
    (1 / Real.sqrt (1 - (Real.cos t / C2C) ^ 2)) * (-(Real.sin t) / C2C)
      = -(Real.sin t / Real.sqrt (C2C ^ 2 - Real.cos t ^ 2)) := by
  rw [Psi_sqrt_one_sub_sq ht]
  field_simp [C2C_ne_zero]

/-! ## Differentiability and the sign of the derivative -/

private lemma Psi_hasDerivAt {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) :
    HasDerivAt C2Psi
      (1 + (1 / Real.sqrt (1 - (Real.cos t / C2C) ^ 2)) * (-(Real.sin t) / C2C)) t := by
  have hcos_lt := Psi_cos_sq_lt ht
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

private lemma Psi_deriv {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) :
    deriv C2Psi t = 1 - Real.sin t / Real.sqrt (C2C ^ 2 - Real.cos t ^ 2) := by
  rw [(Psi_hasDerivAt ht).deriv, Psi_chain_val_eq ht]
  ring

private lemma Psi_deriv_neg {t : ℝ}
    (ht : t ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2)) : deriv C2Psi t < 0 := by
  rw [Psi_deriv ht]
  have hsin := Psi_sigma_lt_sin ht
  have hcos := Psi_cos_sq_lt ht
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

/-! ## `C2Psi` on the closed interval -/

private lemma Psi_antitone_Icc :
    StrictAntiOn C2Psi (Set.Icc (alpR / 2) (Real.pi - alpR / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
  · apply Continuous.continuousOn
    unfold C2Psi
    continuity
  · intro x hx
    rw [interior_Icc] at hx
    exact Psi_deriv_neg hx

private lemma Psi_left_end : C2Psi (alpR / 2) = alpR / 2 := by
  rw [C2Psi, cos_half_alpR, div_self C2C_ne_zero, Real.arcsin_one]
  ring

private lemma Psi_right_end : C2Psi (Real.pi - alpR / 2) = -(alpR / 2) := by
  have h1 : Real.cos (Real.pi - alpR / 2) / C2C = -1 := by
    rw [Real.cos_pi_sub, cos_half_alpR, neg_div, div_self C2C_ne_zero]
  rw [C2Psi, h1, Real.arcsin_neg_one]
  ring

private lemma Psi_le_left {t : ℝ} (ht : t ∈ Set.Icc (alpR / 2) (Real.pi - alpR / 2)) :
    C2Psi t ≤ alpR / 2 := by
  have hle : alpR / 2 ≤ Real.pi - alpR / 2 := by linarith [alpR_lt_pi]
  rcases eq_or_lt_of_le ht.1 with h | h
  · exact le_of_eq (by rw [← h, Psi_left_end])
  · have := Psi_antitone_Icc (Set.left_mem_Icc.mpr hle) ht h
    rw [Psi_left_end] at this
    exact this.le

private lemma Psi_ge_right {t : ℝ} (ht : t ∈ Set.Icc (alpR / 2) (Real.pi - alpR / 2)) :
    -(alpR / 2) ≤ C2Psi t := by
  have hle : alpR / 2 ≤ Real.pi - alpR / 2 := by linarith [alpR_lt_pi]
  rcases eq_or_lt_of_le ht.2 with h | h
  · exact le_of_eq (by rw [h, Psi_right_end])
  · have := Psi_antitone_Icc ht (Set.right_mem_Icc.mpr hle) h
    rw [Psi_right_end] at this
    exact this.le

/-! ## The range statement -/

theorem PsiRange {θ : ℝ} (h1 : Work.CNum.alpR ≤ θ) (h2 : θ ≤ 2 * Real.pi - Work.CNum.alpR) : -(3.9 : ℝ) ≤ Work.CNum.C2Psi (θ / 2) - Real.pi ∧ Work.CNum.C2Psi (θ / 2) - Real.pi ≤ -(2.39 : ℝ) := by
  have hα := AlpBound
  have hmem : θ / 2 ∈ Set.Icc (alpR / 2) (Real.pi - alpR / 2) :=
    ⟨by linarith, by linarith⟩
  have hmax := Psi_le_left hmem
  have hmin := Psi_ge_right hmem
  constructor
  · have h1' : -(3.9 : ℝ) ≤ -(alpR / 2) - Real.pi := by
      linarith [hα.2, Real.pi_lt_d20]
    linarith
  · have h1' : alpR / 2 - Real.pi ≤ -(2.39 : ℝ) := by
      linarith [hα.2, Real.pi_gt_d20]
    linarith

end

end Work.CNum
