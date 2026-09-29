import Mathlib
import Submission.Work.CNum.Jfun_defs

/-!
# CNum: derivatives of `LL` and the lower bound `LLDD ≥ -2`

`LL ψ = (1/2) log (KK ψ)` where `KK ψ = c₂² + ρ₂² + 2 c₂ ρ₂ cos ψ = ‖wf ψ‖²`
is the squared modulus of the circle point `wf ψ = c₂ + ρ₂ e^{iψ}`.

We prove, for **every** `ψ : ℝ` (the arc hypothesis of the target is not needed):

* `LL ψ = Real.log ‖wf ψ‖`,
* `HasDerivAt LL (LLD ψ) ψ`,
* `HasDerivAt LLD (LLDD ψ) ψ`,
* `-2 ≤ LLDD ψ`.

The last inequality is purely algebraic: writing `m = cJ * uJ`, `A = cJ² + uJ²`,
`c = cos ψ`, `K = A + 2 m c` one has
`LLDD ψ + 2 = (8 m² c² + 7 A m c + 2 A² - 2 m²) / K²`, and the numerator is
`8 m² (c + 7A/(16m))² + (15 A² - 64 m²)/32 ≥ 0` because
`15 A² - 64 m² = (3 cJ² - 5 uJ²)(5 cJ² - 3 uJ²) > 0`.
-/

namespace Work.CNum

open Complex

/-- `KK ψ = ‖wf ψ‖²` is strictly positive (it dominates `(cJ - uJ)² = (169/572)²`). -/
lemma KK_pos (ψ : ℝ) : 0 < KK ψ := by
  have h : KK ψ = (cJ - uJ)^2 + 2*cJ*uJ*(1 + Real.cos ψ) := by rw [KK]; ring
  rw [h]
  have hc2 : 0 ≤ 2*cJ*uJ := by rw [cJ, uJ]; norm_num
  have hc1 : 0 ≤ 1 + Real.cos ψ := by linarith [Real.neg_one_le_cos ψ]
  have hc : 0 ≤ 2*cJ*uJ*(1 + Real.cos ψ) := mul_nonneg hc2 hc1
  have h2 : 0 < (cJ - uJ)^2 := by
    apply sq_pos_of_ne_zero
    rw [cJ, uJ]; norm_num
  linarith

/-- The modulus identity: `normSq (wf ψ) = KK ψ`. -/
lemma normSq_wf (ψ : ℝ) : Complex.normSq (wf ψ) = KK ψ := by
  have hexp : Complex.exp (Complex.I * (ψ:ℂ)) = ↑(Real.cos ψ) + ↑(Real.sin ψ) * Complex.I := by
    rw [mul_comm, Complex.exp_ofReal_mul_I]
  rw [wf, hexp, KK, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq ψ, Real.cos_sq ψ]

/-- `LL ψ = log ‖wf ψ‖`. -/
lemma LL_eq_log (ψ : ℝ) : LL ψ = Real.log ‖wf ψ‖ := by
  have hsqrt : ‖wf ψ‖ = Real.sqrt (KK ψ) := by
    have h1 : Complex.normSq (wf ψ) = KK ψ := normSq_wf ψ
    have h2 : ‖wf ψ‖ ^ 2 = KK ψ := by rw [← Complex.normSq_eq_norm_sq, h1]
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [hsqrt, Real.log_sqrt (le_of_lt (KK_pos ψ))]
  unfold LL
  ring

/-- Derivative of `KK`: `KK' ψ = -(2 cJ uJ sin ψ)`. -/
lemma hasDerivAt_KK (ψ : ℝ) : HasDerivAt KK (-(2*cJ*uJ*Real.sin ψ)) ψ := by
  have h1 : HasDerivAt (fun ψ : ℝ => 2*cJ*uJ * Real.cos ψ) (2*cJ*uJ * (-Real.sin ψ)) ψ :=
    (Real.hasDerivAt_cos ψ).const_mul (2*cJ*uJ)
  have h2 := h1.const_add (cJ^2+uJ^2)
  change HasDerivAt (fun ψ : ℝ => cJ^2+uJ^2 + 2*cJ*uJ * Real.cos ψ) (-(2*cJ*uJ*Real.sin ψ)) ψ
  convert h2 using 1
  all_goals first | (rw [mul_neg]) | rfl

/-- First derivative: `LL' ψ = LLD ψ`. -/
lemma hasDerivAt_LL (ψ : ℝ) : HasDerivAt LL (LLD ψ) ψ := by
  have hK := hasDerivAt_KK ψ
  have hlog : HasDerivAt (Real.log ∘ KK) (((KK ψ)⁻¹) * (-(2*cJ*uJ*Real.sin ψ))) ψ :=
    (Real.hasDerivAt_log (ne_of_gt (KK_pos ψ))).comp ψ hK
  have hhalf := hlog.const_mul (1/2:ℝ)
  change HasDerivAt (fun ψ : ℝ => (1/2) * Real.log (KK ψ)) (LLD ψ) ψ
  convert hhalf using 1
  all_goals first | (unfold LLD; rw [inv_mul_eq_div]; field_simp) | rfl

/-- Second derivative: `LLD' ψ = LLDD ψ`. -/
lemma hasDerivAt_LLD (ψ : ℝ) : HasDerivAt LLD (LLDD ψ) ψ := by
  have hK := hasDerivAt_KK ψ
  have hnum : HasDerivAt (fun ψ : ℝ => -cJ*uJ*Real.sin ψ) (-cJ*uJ*Real.cos ψ) ψ := by
    have h := (Real.hasDerivAt_sin ψ).const_mul (-cJ*uJ)
    convert h using 1
  have hdiv := hnum.div hK (ne_of_gt (KK_pos ψ))
  change HasDerivAt (fun ψ : ℝ => -cJ*uJ*Real.sin ψ / KK ψ) (LLDD ψ) ψ
  convert hdiv using 1
  all_goals first | (unfold LLDD; field_simp [ne_of_gt (KK_pos ψ)]; try ring) | rfl

/-- The lower bound `LLDD ψ ≥ -2`, valid for every `ψ`. -/
lemma LLDD_ge_neg_two (ψ : ℝ) : -2 ≤ LLDD ψ := by
  -- the numerator of `LLDD ψ + 2` after clearing `KK ψ ^ 2`, as a quadratic in `cos ψ`
  have hmain : 0 ≤ 8*(cJ*uJ)^2*(Real.cos ψ)^2 + 7*(cJ^2+uJ^2)*(cJ*uJ)*Real.cos ψ
      + 2*(cJ^2+uJ^2)^2 - 2*(cJ*uJ)^2 := by
    have hfac : 0 ≤ 15*(cJ^2+uJ^2)^2 - 64*(cJ*uJ)^2 := by
      have he : 15*(cJ^2+uJ^2)^2 - 64*(cJ*uJ)^2
          = (3*cJ^2 - 5*uJ^2)*(5*cJ^2 - 3*uJ^2) := by ring
      rw [he]
      apply mul_nonneg <;> · rw [cJ, uJ]; norm_num
    nlinarith [sq_nonneg (16*(cJ*uJ)*Real.cos ψ + 7*(cJ^2+uJ^2)), hfac]
  have hLLDDeq : LLDD ψ = -cJ*uJ*Real.cos ψ/KK ψ - 2*(cJ*uJ*Real.sin ψ)^2/(KK ψ)^2 := by
    unfold LLDD; rfl
  have hsq : LLDD ψ * (KK ψ)^2 = -cJ*uJ*Real.cos ψ*KK ψ - 2*(cJ*uJ*Real.sin ψ)^2 := by
    rw [hLLDDeq]; field_simp [ne_of_gt (KK_pos ψ)]
  have hK_eq : KK ψ = (cJ^2+uJ^2) + 2*(cJ*uJ)*Real.cos ψ := by unfold KK; ring
  have hs : Real.sin ψ ^ 2 = 1 - Real.cos ψ ^ 2 := by linarith [Real.sin_sq_add_cos_sq ψ]
  have hB : -cJ*uJ*Real.cos ψ*KK ψ - 2*(cJ*uJ*Real.sin ψ)^2 + 2*(KK ψ)^2
      = 8*(cJ*uJ)^2*(Real.cos ψ)^2 + 7*(cJ^2+uJ^2)*(cJ*uJ)*Real.cos ψ
      + 2*(cJ^2+uJ^2)^2 - 2*(cJ*uJ)^2 := by
    rw [hK_eq, show (cJ*uJ*Real.sin ψ)^2 = (cJ*uJ)^2 * Real.sin ψ^2 by ring]
    rw [hs]; ring
  have hden : 0 < (KK ψ)^2 := pow_pos (KK_pos ψ) 2
  have hmul : (LLDD ψ + 2) * (KK ψ)^2
      = 8*(cJ*uJ)^2*(Real.cos ψ)^2 + 7*(cJ^2+uJ^2)*(cJ*uJ)*Real.cos ψ
      + 2*(cJ^2+uJ^2)^2 - 2*(cJ*uJ)^2 := by
    have : (LLDD ψ + 2) * (KK ψ)^2 = LLDD ψ * (KK ψ)^2 + 2*(KK ψ)^2 := by ring
    rw [this, hsq, hB]
  have h2 : 0 ≤ (LLDD ψ + 2) * (KK ψ)^2 := by rw [hmul]; exact hmain
  have h3 : 0 ≤ LLDD ψ + 2 := (mul_nonneg_iff_of_pos_right hden).mp h2
  linarith

theorem LL_derivs {ψ : ℝ} (hψ : ψ ∈ Set.Ioo (-3.905) (-2.385)) :
    LL ψ = Real.log ‖wf ψ‖ ∧ HasDerivAt LL (LLD ψ) ψ ∧ HasDerivAt LLD (LLDD ψ) ψ ∧ -2 ≤ LLDD ψ :=
  ⟨LL_eq_log ψ, hasDerivAt_LL ψ, hasDerivAt_LLD ψ, LLDD_ge_neg_two ψ⟩

end Work.CNum
