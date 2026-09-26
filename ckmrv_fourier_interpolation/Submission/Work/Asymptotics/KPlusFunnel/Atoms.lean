/-
# The cancelled forms of `Ξ₈` and `Ξ₂₄`, and the funnel growth of the `τ`-atoms

This file prepares the proof of the funnel bound `KPlus_slash_bound_funnel`.

The numerators `Ξ_d` (`d = 8, 24`) of `KPlusXiDefs` are sums of products of `τ`-atoms and
`z`-atoms.  On the *funnel* `{τ ∈ 𝒟 : 2 ≤ Im τ}` the `τ`-atom `j(τ) = E₄(τ)³/Δ(τ)` grows like
`exp (2 π Im τ)` while `Δ(τ)` decays like `exp (-2 π Im τ)`, so the terms carrying powers of
`j(τ)` have to cancel.  The identities `Xi8_cancelled` and `Xi24_cancelled` perform that
cancellation: they rewrite `Ξ₈` and `Ξ₂₄` in terms of the `τ`-quantity

  `phi8 τ = E₄(τ)(τ E₆(τ) - 2φ₀(τ)E₄(τ)) + E₆(τ)φ₂(τ)  =  O(q(τ))`,

the `z`-cusp forms `E₄ - E₂²`, `E₂E₆ - E₄²`, `5E₄² - 7E₄E₂² + 2E₆E₂` (all `O(q(z))`), and
`j(z)(E₄ - E₂²) - 288 = O(q(z))`.

## Main results

* `phi8`, `phi8_eq`, `phi8_bound` : the `τ`-atom and its `O((1+‖τ‖) q)` bound;
* `Xi8_cancelled`, `Xi24_cancelled` : the cancelled forms of `Ξ₈`, `Ξ₂₄`;
* `tau_cusp_forms`, `deltaFunnel_upper`, `jFunnel_bound` : growth of the `τ`-atoms;
* `Xi8_bound_funnel`, `Xi24_bound_funnel` : the funnel bounds on `Ξ₈`, `Ξ₂₄`, taking the
  `z`-estimates as explicit hypotheses.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.Xi8_eq
import Submission.Work.Asymptotics.Xi24_eq

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups

noncomputable section

open Work.Kernels

/-! ## The weight-twelve `τ`-quantity `Φ₈` -/

/-- `Φ₈(τ) = E₄(τ)(τ E₆(τ) - 2φ₀(τ)E₄(τ)) + E₆(τ)φ₂(τ)`. -/
def phi8 (τ : ℍ) : ℂ :=
  E4Fun τ * ((τ : ℂ) * E6Fun τ - 2 * phi0 τ * E4Fun τ) + E6Fun τ * phi2 τ

/-- The factorisation of `Φ₈` through the two `τ`-cusp forms `E₂E₆ - E₄²`, `E₂E₄ - E₆`. -/
theorem phi8_eq (τ : ℍ) :
    phi8 τ = (phi0 τ - 3 * Complex.I / (Real.pi : ℂ)) *
        (E2Fun τ * E6Fun τ - E4Fun τ ^ 2)
      - (τ : ℂ) * E4Fun τ * (E2Fun τ * E4Fun τ - E6Fun τ) := by
  simp only [phi8, phi0, phi2]
  ring

/-! ## The cancelled forms -/

/-- **The cancelled form of `Ξ₈`.** -/
theorem Xi8_cancelled (τ z : ℍ) (hDt : DeltaFun τ ≠ 0) (hDz : DeltaFun z ≠ 0) :
    Xi8 τ z = DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ
      - (τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)
      - 2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2) := by
  have hDt' : ModularForm.discriminant τ ≠ 0 := hDt
  have hDz' : ModularForm.discriminant z ≠ 0 := hDz
  simp only [Xi8, Fin.sum_univ_three, phiVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, Fin.val_zero,
    Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one, jInvariantFun, phi8,
    phi0, phi2, phiNeg2]
  simp only [fk]
  norm_num
  field_simp [hDt', hDz']
  ring

/-- **The cancelled form of `Ξ₂₄`.** -/
theorem Xi24_cancelled (τ z : ℍ) (hDt : DeltaFun τ ≠ 0) (hDz : DeltaFun z ≠ 0) :
    Xi24 τ z =
      6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
          * (jInvariantFun τ - jInvariantFun z)
      + 1728 * E4Fun τ * phi8 τ
      + 1728 * phi0 τ * E4Fun τ ^ 3
          * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))
      + 1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)
      + 1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)
      - 1728 * phi0 τ * DeltaFun τ
          * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2 / DeltaFun z := by
  have hDt' : ModularForm.discriminant τ ≠ 0 := hDt
  have hDz' : ModularForm.discriminant z ≠ 0 := hDz
  simp only [Xi24, Fin.sum_univ_three, phiVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, Fin.val_zero,
    Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one, jInvariantFun, phi8,
    phi0, phi2, phiNeg2]
  simp only [fk]
  rw [show E14Fun τ = E4Fun τ ^ 2 * E6Fun τ from rfl,
      show E10Fun τ = E4Fun τ * E6Fun τ from rfl,
      show E14Fun z = E4Fun z ^ 2 * E6Fun z from rfl,
      show Work.Kernels.c1728 = (1728 : ℂ) from rfl]
  norm_num
  field_simp [hDt', hDz']
  ring

/-! ## Growth of the `τ`-atoms on the funnel -/

/-- `‖qParamFun τ‖ ≤ 1` for `1 ≤ Im τ`. -/
lemma norm_qParamFun_le_one' {τ : ℍ} (hτ : 1 ≤ τ.im) : ‖qParamFun τ‖ ≤ 1 := by
  rw [norm_qParamFun, ← Real.exp_zero, Real.exp_le_exp]
  nlinarith [Real.pi_pos]

/-- The two `τ`-cusp forms are `O(q)` for `1 ≤ Im τ`. -/
theorem tau_cusp_forms :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖E2Fun τ * E6Fun τ - E4Fun τ ^ 2‖ ≤ C * ‖qParamFun τ‖ ∧
      ‖E2Fun τ * E4Fun τ - E6Fun τ‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C0, hC0, hB⟩ := eps_isBigOq
  obtain ⟨C2, hC2, h2⟩ := E2Fun_two_term
  obtain ⟨C4, hC4, h4⟩ := E4Fun_two_term
  obtain ⟨C6, hC6, h6⟩ := E6Fun_two_term
  obtain ⟨C4b, hC4b, hE4b⟩ := E4Fun_bound
  set K : ℝ := C2 * C4b + (1 + 24) * C4 + C6 + 720 + 5760 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨max C0 (K + 1) + 1, by positivity, fun τ hτ => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hq1 : ‖qParamFun τ‖ ≤ 1 := norm_qParamFun_le_one' hτ
  have hq2 : ‖qParamFun τ‖ ^ 2 ≤ ‖qParamFun τ‖ := by nlinarith
  have hKq : K * ‖qParamFun τ‖ ≤ (max C0 (K + 1) + 1) * ‖qParamFun τ‖ := by
    apply mul_le_mul_of_nonneg_right _ hq0
    linarith [le_max_right C0 (K + 1)]
  constructor
  · have h := hB τ hτ
    have h1 : C0 * ‖qParamFun τ‖ ^ 1 ≤ (max C0 (K + 1) + 1) * ‖qParamFun τ‖ := by
      rw [pow_one]
      apply mul_le_mul_of_nonneg_right _ hq0
      linarith [le_max_left C0 (K + 1)]
    calc ‖E2Fun τ * E6Fun τ - E4Fun τ ^ 2‖
        = ‖-(E4Fun τ ^ 2 - E6Fun τ * E2Fun τ)‖ := by ring_nf
      _ = ‖E4Fun τ ^ 2 - E6Fun τ * E2Fun τ‖ := norm_neg _
      _ ≤ (max C0 (K + 1) + 1) * ‖qParamFun τ‖ := le_trans h h1
  · have hh2 := h2 τ hτ
    have hh4 := h4 τ hτ
    have hh6 := h6 τ hτ
    have hE4 := hE4b τ hτ
    have hA : ‖(E2Fun τ - 1 + 24 * qParamFun τ) * E4Fun τ‖ ≤ C2 * C4b * ‖qParamFun τ‖ := by
      rw [norm_mul]
      calc ‖E2Fun τ - 1 + 24 * qParamFun τ‖ * ‖E4Fun τ‖
          ≤ (C2 * ‖qParamFun τ‖ ^ 2) * C4b := mul_le_mul hh2 hE4 (norm_nonneg _) (by positivity)
        _ = C2 * C4b * ‖qParamFun τ‖ ^ 2 := by ring
        _ ≤ C2 * C4b * ‖qParamFun τ‖ := mul_le_mul_of_nonneg_left hq2 (by positivity)
    have h1q : ‖(1 : ℂ) - 24 * qParamFun τ‖ ≤ 1 + 24 * ‖qParamFun τ‖ := by
      calc ‖(1 : ℂ) - 24 * qParamFun τ‖
          ≤ ‖(1 : ℂ)‖ + ‖(24 : ℂ) * qParamFun τ‖ := norm_sub_le _ _
        _ = 1 + 24 * ‖qParamFun τ‖ := by rw [norm_one, norm_mul, Complex.norm_ofNat]
    have hB2 : ‖(1 - 24 * qParamFun τ) * (E4Fun τ - 1 - 240 * qParamFun τ)‖
        ≤ (1 + 24) * C4 * ‖qParamFun τ‖ := by
      rw [norm_mul]
      calc ‖(1 : ℂ) - 24 * qParamFun τ‖ * ‖E4Fun τ - 1 - 240 * qParamFun τ‖
          ≤ (1 + 24 * ‖qParamFun τ‖) * (C4 * ‖qParamFun τ‖ ^ 2) :=
            mul_le_mul h1q hh4 (norm_nonneg _) (by positivity)
        _ ≤ (1 + 24 * ‖qParamFun τ‖) * (C4 * ‖qParamFun τ‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq2 hC4.le) (by positivity)
        _ ≤ (1 + 24) * C4 * ‖qParamFun τ‖ := by
            have h24 : 1 + 24 * ‖qParamFun τ‖ ≤ 1 + 24 := by linarith
            calc (1 + 24 * ‖qParamFun τ‖) * (C4 * ‖qParamFun τ‖)
                = (1 + 24 * ‖qParamFun τ‖) * C4 * ‖qParamFun τ‖ := by ring
              _ ≤ (1 + 24) * C4 * ‖qParamFun τ‖ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h24 hC4.le) hq0
    have hC6b : ‖E6Fun τ - 1 + 504 * qParamFun τ‖ ≤ C6 * ‖qParamFun τ‖ :=
      le_trans hh6 (mul_le_mul_of_nonneg_left hq2 hC6.le)
    have hD : ‖(720 : ℂ) * qParamFun τ - 5760 * qParamFun τ ^ 2‖
        ≤ (720 + 5760) * ‖qParamFun τ‖ := by
      calc ‖(720 : ℂ) * qParamFun τ - 5760 * qParamFun τ ^ 2‖
          ≤ ‖(720 : ℂ) * qParamFun τ‖ + ‖(5760 : ℂ) * qParamFun τ ^ 2‖ := norm_sub_le _ _
        _ = 720 * ‖qParamFun τ‖ + 5760 * ‖qParamFun τ‖ ^ 2 := by
            rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat, norm_pow]
          _ ≤ 720 * ‖qParamFun τ‖ + 5760 * ‖qParamFun τ‖ := by
            have := mul_le_mul_of_nonneg_left hq2 (by norm_num : (0:ℝ) ≤ 5760)
            linarith
          _ = (720 + 5760) * ‖qParamFun τ‖ := by ring
    have hsplit : E2Fun τ * E4Fun τ - E6Fun τ
        = ((E2Fun τ - 1 + 24 * qParamFun τ) * E4Fun τ
            + (1 - 24 * qParamFun τ) * (E4Fun τ - 1 - 240 * qParamFun τ)
            - (E6Fun τ - 1 + 504 * qParamFun τ))
          + ((720 : ℂ) * qParamFun τ - 5760 * qParamFun τ ^ 2) := by ring
    rw [hsplit]
    calc ‖((E2Fun τ - 1 + 24 * qParamFun τ) * E4Fun τ
              + (1 - 24 * qParamFun τ) * (E4Fun τ - 1 - 240 * qParamFun τ)
              - (E6Fun τ - 1 + 504 * qParamFun τ))
            + ((720 : ℂ) * qParamFun τ - 5760 * qParamFun τ ^ 2)‖
        ≤ ‖(E2Fun τ - 1 + 24 * qParamFun τ) * E4Fun τ
              + (1 - 24 * qParamFun τ) * (E4Fun τ - 1 - 240 * qParamFun τ)
              - (E6Fun τ - 1 + 504 * qParamFun τ)‖
            + ‖(720 : ℂ) * qParamFun τ - 5760 * qParamFun τ ^ 2‖ := norm_add_le _ _
      _ ≤ (‖(E2Fun τ - 1 + 24 * qParamFun τ) * E4Fun τ‖
              + ‖(1 - 24 * qParamFun τ) * (E4Fun τ - 1 - 240 * qParamFun τ)‖
              + ‖E6Fun τ - 1 + 504 * qParamFun τ‖)
            + ‖(720 : ℂ) * qParamFun τ - 5760 * qParamFun τ ^ 2‖ := by
            have h1 := norm_sub_le ((E2Fun τ - 1 + 24 * qParamFun τ) * E4Fun τ
              + (1 - 24 * qParamFun τ) * (E4Fun τ - 1 - 240 * qParamFun τ))
              (E6Fun τ - 1 + 504 * qParamFun τ)
            have h2' := norm_add_le ((E2Fun τ - 1 + 24 * qParamFun τ) * E4Fun τ)
              ((1 - 24 * qParamFun τ) * (E4Fun τ - 1 - 240 * qParamFun τ))
            linarith
      _ ≤ ((C2 * C4b * ‖qParamFun τ‖ + (1 + 24) * C4 * ‖qParamFun τ‖
              + C6 * ‖qParamFun τ‖) + (720 + 5760) * ‖qParamFun τ‖) := by
            linarith [hA, hB2, hC6b, hD]
      _ = K * ‖qParamFun τ‖ := by rw [hK]; ring
      _ ≤ (max C0 (K + 1) + 1) * ‖qParamFun τ‖ := hKq

/-- `Δ = O(q)` on the funnel. -/
theorem deltaFunnel_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖DeltaFun τ‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C, hC, h⟩ := DeltaFun_two_term
  refine ⟨1 + C, by positivity, fun τ hτ => ?_⟩
  have h1 : 1 ≤ τ.im := Funnel.im_one hτ
  have h2 := h τ h1
  have hq1 : ‖qParamFun τ‖ ≤ 1 := norm_qParamFun_le_one' h1
  have hq2 : ‖qParamFun τ‖ ^ 2 ≤ ‖qParamFun τ‖ := by nlinarith [norm_nonneg (qParamFun τ)]
  have hsplit : DeltaFun τ = (DeltaFun τ - qParamFun τ) + qParamFun τ := by ring
  rw [hsplit]
  calc ‖(DeltaFun τ - qParamFun τ) + qParamFun τ‖
      ≤ ‖DeltaFun τ - qParamFun τ‖ + ‖qParamFun τ‖ := norm_add_le _ _
    _ ≤ C * ‖qParamFun τ‖ ^ 2 + ‖qParamFun τ‖ := by linarith
    _ ≤ (1 + C) * ‖qParamFun τ‖ := by
        have h3 := mul_le_mul_of_nonneg_left hq2 hC.le
        nlinarith [norm_nonneg (qParamFun τ)]

/-- `‖j(τ)‖ ≤ C / ‖qParamFun τ‖` on the funnel. -/
theorem jFunnel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖jInvariantFun τ‖ ≤ C / ‖qParamFun τ‖ := by
  obtain ⟨C, hC, h⟩ := exists_jInvariantFun_Funnel_bound
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  rw [div_eq_mul_inv]
  refine le_trans h1 ?_
  have hq : ‖qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := norm_qParamFun τ
  have heq : Real.exp (2 * Real.pi * τ.im) = (‖qParamFun τ‖)⁻¹ := by
    rw [hq, ← Real.exp_neg]
    congr 1
    ring
  rw [heq]

/-- `Φ₈ = O((1+‖τ‖) q)` on the funnel. -/
theorem phi8_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
      ‖phi8 τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by
  obtain ⟨CB, hCB, hB⟩ := tau_cusp_forms
  obtain ⟨C2, hC2, hE2⟩ := exists_E2_Funnel_bound
  obtain ⟨C4, hC4, hE4⟩ := exists_E4_Funnel_bound
  refine ⟨(C2 + 3) * CB + C4 * CB + 1, by positivity, fun τ hτ => ?_⟩
  have h1 : 1 ≤ τ.im := Funnel.im_one hτ
  have hq0 : (0 : ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have ht0 : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have hB1 : ‖E2Fun τ * E6Fun τ - E4Fun τ ^ 2‖ ≤ CB * ‖qParamFun τ‖ := (hB τ h1).1
  have hB2 : ‖E2Fun τ * E4Fun τ - E6Fun τ‖ ≤ CB * ‖qParamFun τ‖ := (hB τ h1).2
  have h6 : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
    congr 1
    simp
    all_goals positivity
  have hph0 : phi0 τ - 3 * Complex.I / (Real.pi : ℂ)
      = (τ : ℂ) * E2Fun τ - 6 * Complex.I / (Real.pi : ℂ) := by
    simp only [phi0]
    ring
  have hph : ‖phi0 τ - 3 * Complex.I / (Real.pi : ℂ)‖ ≤ (1 + ‖(τ : ℂ)‖) * (C2 + 3) := by
    rw [hph0]
    have hpi : (6 : ℝ) / Real.pi ≤ 3 := by
      rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
    calc ‖(τ : ℂ) * E2Fun τ - 6 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖(τ : ℂ) * E2Fun τ‖ + ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖(τ : ℂ)‖ * C2 + 3 := by
          rw [h6, norm_mul]
          have hle := mul_le_mul_of_nonneg_left (hE2 τ hτ) ht0
          linarith
      _ ≤ (1 + ‖(τ : ℂ)‖) * (C2 + 3) := by nlinarith [ht0, hC2.le]
  have hterm1 : ‖(phi0 τ - 3 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ * E6Fun τ - E4Fun τ ^ 2)‖
      ≤ (1 + ‖(τ : ℂ)‖) * ((C2 + 3) * CB) * ‖qParamFun τ‖ := by
    rw [norm_mul]
    calc ‖phi0 τ - 3 * Complex.I / (Real.pi : ℂ)‖
            * ‖E2Fun τ * E6Fun τ - E4Fun τ ^ 2‖
        ≤ ((1 + ‖(τ : ℂ)‖) * (C2 + 3)) * (CB * ‖qParamFun τ‖) :=
          mul_le_mul hph hB1 (norm_nonneg _) (by positivity)
      _ = (1 + ‖(τ : ℂ)‖) * ((C2 + 3) * CB) * ‖qParamFun τ‖ := by ring
  have hterm2 : ‖(τ : ℂ) * E4Fun τ * (E2Fun τ * E4Fun τ - E6Fun τ)‖
      ≤ (1 + ‖(τ : ℂ)‖) * (C4 * CB) * ‖qParamFun τ‖ := by
    rw [show (τ : ℂ) * E4Fun τ * (E2Fun τ * E4Fun τ - E6Fun τ)
        = (τ : ℂ) * (E4Fun τ * (E2Fun τ * E4Fun τ - E6Fun τ)) by ring, norm_mul]
    calc ‖(τ : ℂ)‖ * ‖E4Fun τ * (E2Fun τ * E4Fun τ - E6Fun τ)‖
        ≤ ‖(τ : ℂ)‖ * (C4 * (CB * ‖qParamFun τ‖)) := by
          apply mul_le_mul_of_nonneg_left _ ht0
          rw [norm_mul]
          exact mul_le_mul (hE4 τ hτ) hB2 (norm_nonneg _) hC4.le
      _ ≤ (1 + ‖(τ : ℂ)‖) * (C4 * (CB * ‖qParamFun τ‖)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [ht0]
      _ = (1 + ‖(τ : ℂ)‖) * (C4 * CB) * ‖qParamFun τ‖ := by ring
  rw [phi8_eq τ]
  calc ‖(phi0 τ - 3 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ * E6Fun τ - E4Fun τ ^ 2)
          - (τ : ℂ) * E4Fun τ * (E2Fun τ * E4Fun τ - E6Fun τ)‖
      ≤ ‖(phi0 τ - 3 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ * E6Fun τ - E4Fun τ ^ 2)‖
          + ‖(τ : ℂ) * E4Fun τ * (E2Fun τ * E4Fun τ - E6Fun τ)‖ := norm_sub_le _ _
    _ ≤ (1 + ‖(τ : ℂ)‖) * ((C2 + 3) * CB) * ‖qParamFun τ‖
          + (1 + ‖(τ : ℂ)‖) * (C4 * CB) * ‖qParamFun τ‖ := add_le_add hterm1 hterm2
    _ = (1 + ‖(τ : ℂ)‖) * ((C2 + 3) * CB + C4 * CB) * ‖qParamFun τ‖ := by ring
    _ ≤ ((C2 + 3) * CB + C4 * CB + 1) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by
        have h8 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by positivity
        nlinarith [h8]

end

end Work.Asymptotics
