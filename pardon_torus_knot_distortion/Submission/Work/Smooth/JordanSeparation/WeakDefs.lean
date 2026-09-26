import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs

/-!
# The index jump at a *regular* point: the basic lemmas without the immersion hypothesis

The whole chain proving the index jump
(`Work.Smooth.JordanSeparation.ind_jump`) uses the hypothesis `c.IsImmersion` only at the parameter
`0`.  This file collects the elementary restatements needed to run the same chain for a `C¹` curve
which is merely *regular at `0`* (`deriv c.γ 0 ≠ 0`) — the curve may well have cusps elsewhere.

* `norm_unitTangent_of_deriv_ne_zero`, `norm_normalField_of_deriv_ne_zero`,
  `detV_deriv_normalField_of_deriv_ne_zero` — the unit normal at a regular parameter;
* `deriv_eq_norm_mul_unitTangent` — the identity `γ'(t) = ‖γ'(t)‖·unitTangent c t`, which holds for
  **every** `C¹` curve (both sides vanish where the derivative does);
* `deriv_global_norm_upper` — the upper bound on `‖γ'‖` over one period, which needs no immersion.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- The unit tangent is a unit vector at a regular parameter. -/
theorem norm_unitTangent_of_deriv_ne_zero (c : SmoothPlaneCurve) {t : ℝ}
    (h : deriv c.γ t ≠ 0) : ‖unitTangent c t‖ = 1 := by
  have hpos : (0 : ℝ) < ‖deriv c.γ t‖ := norm_pos_iff.mpr h
  refine Eq.trans ?_ (div_self (ne_of_gt hpos))
  rw [unitTangent, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le]

/-- The normal field is a unit vector at a regular parameter. -/
theorem norm_normalField_of_deriv_ne_zero (c : SmoothPlaneCurve) {t : ℝ}
    (h : deriv c.γ t ≠ 0) : ‖normalField c t‖ = 1 := by
  rw [normalField, norm_mul, Complex.norm_I, one_mul, norm_unitTangent_of_deriv_ne_zero c h]

/-- The normal field is exactly transverse to the curve at a regular parameter. -/
theorem detV_deriv_normalField_of_deriv_ne_zero (c : SmoothPlaneCurve) {t : ℝ}
    (h : deriv c.γ t ≠ 0) : detV (deriv c.γ t) (normalField c t) = ‖deriv c.γ t‖ := by
  have hr : (0 : ℝ) < ‖deriv c.γ t‖ := norm_pos_iff.mpr h
  have hreal : normalField c t
      = (((‖deriv c.γ t‖)⁻¹ : ℝ) : ℂ) * (Complex.I * deriv c.γ t) := by
    rw [normalField, unitTangent, div_eq_mul_inv, ← Complex.ofReal_inv]; ring
  have hsq : detV (deriv c.γ t) (Complex.I * deriv c.γ t) = ‖deriv c.γ t‖ ^ 2 := by
    rw [detV_eq, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    simp only [zero_mul, zero_sub, one_mul, sub_zero, sub_neg_eq_add]
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hreal, detV_smul_right, hsq, pow_two, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), one_mul]

/-- **`γ'(t) = ‖γ'(t)‖·unitTangent c t` for every `C¹` curve** (no immersion needed: both sides
vanish when the derivative does). -/
theorem deriv_eq_norm_mul_unitTangent' (c : SmoothPlaneCurve) (t : ℝ) :
    deriv c.γ t = ((‖deriv c.γ t‖ : ℝ) : ℂ) * unitTangent c t := by
  rcases eq_or_ne (deriv c.γ t) 0 with h | h
  · rw [h, unitTangent, h, zero_div, mul_zero]
  · have hp : (((‖deriv c.γ t‖ : ℝ)) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]; exact h
    rw [unitTangent]
    exact (mul_div_cancel₀ (deriv c.γ t) hp).symm

/-- **Upper bound for `‖γ'‖` over one period**, for any `C¹` `2π`-periodic curve: compactness of
`[0, 2π]` plus `2π`-periodicity of `γ'`.  No immersion hypothesis. -/
theorem deriv_global_norm_upper (c : SmoothPlaneCurve) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, ‖deriv c.γ t‖ ≤ M := by
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  have hper : Function.Periodic (deriv c.γ) (2 * Real.pi) := by
    intro t
    have hfun : (fun s : ℝ => c.γ (s + 2 * Real.pi)) = c.γ :=
      funext fun s => c.periodic_apply s
    have hh : deriv (fun s : ℝ => c.γ (s + 2 * Real.pi)) t
        = deriv c.γ (t + 2 * Real.pi) := deriv_comp_add_const c.γ (2 * Real.pi) t
    rw [← hh, hfun]
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))
    |>.exists_bound_of_continuousOn c.continuous_deriv.continuousOn
  refine ⟨max M0 1, lt_max_iff.mpr (Or.inr zero_lt_one), fun t => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, t - (k : ℝ) * (2 * Real.pi) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    refine ⟨⌊t / (2 * Real.pi)⌋, ?_⟩
    have h : t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)
        = Int.fract (t / (2 * Real.pi)) * (2 * Real.pi) := by
      rw [Int.fract]; field_simp
    rw [Set.mem_Icc, h]
    exact ⟨mul_nonneg (Int.fract_nonneg _) (le_of_lt hT),
      by simpa using (mul_lt_mul_of_pos_right (Int.fract_lt_one _) hT).le⟩
  have heq : deriv c.γ t = deriv c.γ (t - (k : ℝ) * (2 * Real.pi)) := by
    have hh := hper.int_mul k (t - (k : ℝ) * (2 * Real.pi))
    rwa [show t - (k : ℝ) * (2 * Real.pi) + (k : ℝ) * (2 * Real.pi) = t by ring] at hh
  rw [heq]
  exact le_trans (hM0 _ hk) (le_max_left _ _)

end

end Work.Smooth.JordanSeparation
