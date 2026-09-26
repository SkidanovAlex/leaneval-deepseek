/-
# `Sh · Sinvref - 1 = O((‖Ept z‖² e^{2π Im τ})²)` on the funnel contour

This file proves `Work.Asymptotics.Funnel24Tail.ShSinvrefFunnelBound`, the estimate which makes
the `dSinv`-terms of the cusp expansion effective on the *unbounded* funnel.

With `q = Ept z² = q_z` (`‖q‖ = a²` for `a = ‖Ept z‖ ≤ 1`), `J = j(τ)` (`‖J‖ ≤ (27/4) e^{2π Im τ}`)
one has, from `Δ(z)⁻¹ = q⁻¹ + O(1)`, `E₄(z)³ = 1 + 720q + O(q²)` and `Sinvref = 1 + (J-720)q`,

  `Sh·Sinvref - 1 = (E₄(z)³ - 1 - 720q) - (Δ(z)-q)J - (J-720)²q²
                      + (J-720)q(E₄(z)³ - 1 - 720q) - (Δ(z)-q)J(J-720)q`,

and every term is `O((a² e^{2π Im τ})²)`.  Since `e^{2π Im τ} = (‖Ept τ‖²)⁻¹`, this is the same as
`O((‖Ept z‖²/‖Ept τ‖²)²)`: the exact size of `Sh · dSinv` on the funnel (the compact version
`cusp_inv_divisor_second` sees only the case where `‖j τ‖` is bounded).
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KMinusFunnelAtoms
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.E4cube_cusp_second
import Submission.Work.Residues.DeltaExpansion

set_option maxHeartbeats 1000000

namespace Work.Asymptotics.Funnel24Tail

open UpperHalfPlane
open Work.Kernels
open Work.Residues (Ept)
open Work.Asymptotics.Funnel24

noncomputable section

/-- `(‖Ept τ‖²)⁻¹ = e^{2π Im τ}`. -/
theorem inv_Ept_tau_sq {τ : ℍ} : (‖Ept τ‖ ^ 2)⁻¹ = Real.exp (2 * Real.pi * τ.im) := by
  have h2 : ‖Ept τ‖ ^ 2 = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [Work.Residues.norm_Ept, sq, ← Real.exp_add]
    congr 1; ring
  rw [h2, ← Real.exp_neg]
  congr 1
  ring

/-- `‖Ept z‖² ≤ ‖Ept τ‖² e^{-2π}` on the funnel contour (`t ≥ Im τ + 1`). -/
theorem Ept_sq_div_le {τ z : ℍ} {t : ℝ} (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹ ≤ Real.exp (-(2 * Real.pi)) := by
  have hzim : z.im = t := ft_im_of_coe hz
  have h1 : ‖Ept z‖ ^ 2 = Real.exp (-(2 * Real.pi * t)) := by
    rw [Work.Residues.norm_Ept, hzim, sq, ← Real.exp_add]
    congr 1; ring
  have h2 : ‖Ept τ‖ ^ 2 = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [Work.Residues.norm_Ept, sq, ← Real.exp_add]
    congr 1; ring
  have h3 : (‖Ept τ‖ ^ 2)⁻¹ = Real.exp (2 * Real.pi * τ.im) := by
    rw [h2, ← Real.exp_neg]
    congr 1
    ring
  rw [h1, h3, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [ht, Real.pi_pos])

/-- **`Sh · Sinvref - 1 = O((‖Ept z‖² e^{2π Im τ})²)`.** -/
theorem ShSinvrefBound_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * Compact.Sinvref τ z - 1‖
        ≤ C * (‖Ept z‖ ^ 2 * Real.exp (2 * Real.pi * τ.im)) ^ 2 := by
  obtain ⟨cA, hcA, hA0⟩ := Work.Asymptotics.E4cube_cusp_second
  obtain ⟨cΔ, hcΔ, hD0⟩ := Work.Residues.DeltaExpansion
  refine ⟨cA + cΔ * (27 / 4) + ((27 / 4) + 720) ^ 2 + cA * ((27 / 4) + 720)
      + cΔ * (27 / 4) * ((27 / 4) + 720) + 1, by positivity, fun τ z t hτ ht hz => ?_⟩
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : (1:ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have ha0 : (0:ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have ha1 : ‖Ept z‖ ≤ 1 := norm_Ept_le_one' hz1
  have ha2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ ha0 ha1
  have ha4' : (0:ℝ) ≤ ‖Ept z‖ ^ 4 := pow_nonneg ha0 4
  have ha2' : (0:ℝ) ≤ ‖Ept z‖ ^ 2 := pow_nonneg ha0 2
  set E : ℝ := Real.exp (2 * Real.pi * τ.im) with hEdef
  have hE1 : (1:ℝ) ≤ E := by rw [hEdef, Real.one_le_exp_iff]; positivity
  have hE0 : (0:ℝ) ≤ E := by linarith
  set X : ℝ := (‖Ept z‖ ^ 2 * E) ^ 2 with hXdef
  have hX0 : (0:ℝ) ≤ X := by rw [hXdef]; positivity
  have hXeq : X = ‖Ept z‖ ^ 4 * E ^ 2 := by rw [hXdef]; ring
  have haE : ‖Ept z‖ ^ 2 ≤ E := by linarith [ha2, hE1]
  -- atom bounds
  have hJ : ‖jInvariantFun τ‖ ≤ (27 / 4) * E := by
    rw [hEdef]; exact Funnel24.norm_j_funnel τ hτ
  have hJ720 : ‖jInvariantFun τ - 720‖ ≤ (27 / 4) * E + 720 := by
    calc ‖jInvariantFun τ - 720‖ ≤ ‖jInvariantFun τ‖ + ‖(720 : ℂ)‖ := norm_sub_le _ _
      _ ≤ (27 / 4) * E + 720 := by
          rw [show ‖(720 : ℂ)‖ = 720 by norm_num]; linarith
  have hA : ‖E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2‖ ≤ cA * ‖Ept z‖ ^ 4 := by
    have h := hA0 z hz1
    rw [show qParamFun z = (Ept z) ^ 2 from Compact.qParamFun_eq_Ept_sq z,
      show ‖(Ept z) ^ 2‖ = ‖Ept z‖ ^ 2 from norm_pow _ _] at h
    calc ‖E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2‖ ≤ cA * (‖Ept z‖ ^ 2) ^ 2 := h
      _ = cA * ‖Ept z‖ ^ 4 := by ring
  have hD : ‖DeltaFun z - (Ept z) ^ 2‖ ≤ cΔ * ‖Ept z‖ ^ 4 := hD0 z hz1
  have hid : Compact.Sh τ z * Compact.Sinvref τ z - 1
      = (E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2) - (DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ
        - (jInvariantFun τ - 720) ^ 2 * (Ept z) ^ 4
        + (jInvariantFun τ - 720) * (Ept z) ^ 2 * (E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)
        - (DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ * (jInvariantFun τ - 720) * (Ept z) ^ 2 := by
    simp only [Compact.Sh, Compact.Sinvref]
    ring
  rw [hid]
  -- `a⁴ ≤ X`
  have ha4X : ‖Ept z‖ ^ 4 ≤ X := by
    have hE2 : (1:ℝ) ≤ E ^ 2 := by nlinarith [hE1]
    rw [hXeq]
    calc ‖Ept z‖ ^ 4 = ‖Ept z‖ ^ 4 * 1 := by ring
      _ ≤ ‖Ept z‖ ^ 4 * E ^ 2 := mul_le_mul_of_nonneg_left hE2 ha4'
  -- term bounds
  have hT1 : ‖E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2‖ ≤ cA * X :=
    le_trans hA (mul_le_mul_of_nonneg_left ha4X hcA.le)
  have hT2 : ‖(DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ‖ ≤ cΔ * (27 / 4) * X := by
    have h1 : ‖Ept z‖ ^ 4 * E ≤ X := by
      rw [hXeq]
      calc ‖Ept z‖ ^ 4 * E = ‖Ept z‖ ^ 4 * E * 1 := by ring
        _ ≤ ‖Ept z‖ ^ 4 * E * E := by
            refine mul_le_mul_of_nonneg_left hE1 (by positivity)
        _ = ‖Ept z‖ ^ 4 * E ^ 2 := by ring
    rw [norm_mul]
    have h2 : ‖DeltaFun z - (Ept z) ^ 2‖ * ‖jInvariantFun τ‖
        ≤ (cΔ * ‖Ept z‖ ^ 4) * ((27 / 4) * E) :=
      mul_le_mul hD hJ (norm_nonneg _) (by positivity)
    refine le_trans h2 ?_
    calc (cΔ * ‖Ept z‖ ^ 4) * ((27 / 4) * E)
        = cΔ * (27 / 4) * (‖Ept z‖ ^ 4 * E) := by ring
      _ ≤ cΔ * (27 / 4) * X := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hT3 : ‖(jInvariantFun τ - 720) ^ 2 * (Ept z) ^ 4‖ ≤ ((27 / 4) + 720) ^ 2 * X := by
    rw [norm_mul, norm_pow, show ‖(Ept z) ^ 4‖ = ‖Ept z‖ ^ 4 from norm_pow _ _]
    have h1 : ‖jInvariantFun τ - 720‖ ^ 2 ≤ (((27 / 4) + 720) * E) ^ 2 := by
      have h2 : ‖jInvariantFun τ - 720‖ ≤ ((27 / 4) + 720) * E := by nlinarith [hE1]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc ‖jInvariantFun τ - 720‖ ^ 2 * ‖Ept z‖ ^ 4
        ≤ (((27 / 4) + 720) * E) ^ 2 * ‖Ept z‖ ^ 4 :=
          mul_le_mul_of_nonneg_right h1 ha4'
      _ = ((27 / 4) + 720) ^ 2 * X := by rw [hXeq]; ring
  have hT4 : ‖(jInvariantFun τ - 720) * (Ept z) ^ 2 * (E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)‖
      ≤ cA * ((27 / 4) + 720) * X := by
    rw [show (jInvariantFun τ - 720) * (Ept z) ^ 2 * (E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)
        = (jInvariantFun τ - 720) * (E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)
          * (Ept z) ^ 2 by ring, norm_mul, norm_mul,
      show ‖(Ept z) ^ 2‖ = ‖Ept z‖ ^ 2 from norm_pow _ _]
    have h1 : ‖jInvariantFun τ - 720‖ * ‖E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2‖
        ≤ (((27 / 4) + 720) * E) * (cA * ‖Ept z‖ ^ 4) := by
      refine mul_le_mul ?_ hA (norm_nonneg _) (by positivity)
      nlinarith [hE1]
    refine le_trans (mul_le_mul_of_nonneg_right h1 ha2') ?_
    have ha6E : ‖Ept z‖ ^ 6 * E ≤ X := by
      rw [hXeq]
      calc ‖Ept z‖ ^ 6 * E = ‖Ept z‖ ^ 4 * (‖Ept z‖ ^ 2 * E) := by ring
        _ ≤ ‖Ept z‖ ^ 4 * E := by
            refine mul_le_mul_of_nonneg_left ?_ ha4'
            calc ‖Ept z‖ ^ 2 * E ≤ 1 * E := mul_le_mul_of_nonneg_right ha2 hE0
              _ = E := by ring
        _ ≤ ‖Ept z‖ ^ 4 * E ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ ha4'
            nlinarith [hE1]
    calc (((27 / 4) + 720) * E) * (cA * ‖Ept z‖ ^ 4) * ‖Ept z‖ ^ 2
        = cA * ((27 / 4) + 720) * (‖Ept z‖ ^ 6 * E) := by ring
      _ ≤ cA * ((27 / 4) + 720) * X := mul_le_mul_of_nonneg_left ha6E (by positivity)
  have hT5 : ‖(DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ * (jInvariantFun τ - 720)
        * (Ept z) ^ 2‖ ≤ cΔ * (27 / 4) * ((27 / 4) + 720) * X := by
    rw [show (DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ * (jInvariantFun τ - 720) * (Ept z) ^ 2
        = (DeltaFun z - (Ept z) ^ 2) * (jInvariantFun τ * (jInvariantFun τ - 720))
          * (Ept z) ^ 2 by ring, norm_mul, norm_mul, norm_mul,
      show ‖(Ept z) ^ 2‖ = ‖Ept z‖ ^ 2 from norm_pow _ _]
    have h1 : ‖DeltaFun z - (Ept z) ^ 2‖ * (‖jInvariantFun τ‖ * ‖jInvariantFun τ - 720‖)
        ≤ (cΔ * ‖Ept z‖ ^ 4) * (((27 / 4) * E) * (((27 / 4) + 720) * E)) := by
      refine mul_le_mul hD ?_ (by positivity) (by positivity)
      refine mul_le_mul hJ ?_ (norm_nonneg _) (by positivity)
      nlinarith [hE1]
    refine le_trans (mul_le_mul_of_nonneg_right h1 ha2') ?_
    have ha6E2 : ‖Ept z‖ ^ 6 * E ^ 2 ≤ X := by
      rw [hXeq]
      calc ‖Ept z‖ ^ 6 * E ^ 2 ≤ ‖Ept z‖ ^ 4 * E ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have h2 : ‖Ept z‖ ^ 6 ≤ ‖Ept z‖ ^ 4 := by
              calc ‖Ept z‖ ^ 6 ≤ ‖Ept z‖ ^ 4 * ‖Ept z‖ ^ 2 := by
                    rw [show ‖Ept z‖ ^ 6 = ‖Ept z‖ ^ 4 * ‖Ept z‖ ^ 2 by ring]
                _ ≤ ‖Ept z‖ ^ 4 * 1 := mul_le_mul_of_nonneg_left ha2 ha4'
                _ = ‖Ept z‖ ^ 4 := by ring
            exact h2
        _ = ‖Ept z‖ ^ 4 * E ^ 2 := rfl
    calc (cΔ * ‖Ept z‖ ^ 4) * (((27 / 4) * E) * (((27 / 4) + 720) * E)) * ‖Ept z‖ ^ 2
        = cΔ * (27 / 4) * ((27 / 4) + 720) * (‖Ept z‖ ^ 6 * E ^ 2) := by ring
      _ ≤ cΔ * (27 / 4) * ((27 / 4) + 720) * X :=
          mul_le_mul_of_nonneg_left ha6E2 (by positivity)
  -- combine
  have h1 : ‖(E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)
        - (DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ
        - (jInvariantFun τ - 720) ^ 2 * (Ept z) ^ 4
        + (jInvariantFun τ - 720) * (Ept z) ^ 2 * (E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)
        - (DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ * (jInvariantFun τ - 720)
          * (Ept z) ^ 2‖
      ≤ ‖(E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)
          - (DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ
          - (jInvariantFun τ - 720) ^ 2 * (Ept z) ^ 4
          + (jInvariantFun τ - 720) * (Ept z) ^ 2 * (E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)‖
        + ‖(DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ * (jInvariantFun τ - 720)
          * (Ept z) ^ 2‖ := norm_sub_le _ _
  have h2 : ‖(E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)
        - (DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ
        - (jInvariantFun τ - 720) ^ 2 * (Ept z) ^ 4
        + (jInvariantFun τ - 720) * (Ept z) ^ 2 * (E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)‖
      ≤ ‖(E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)
          - (DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ
          - (jInvariantFun τ - 720) ^ 2 * (Ept z) ^ 4‖
        + ‖(jInvariantFun τ - 720) * (Ept z) ^ 2 * (E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)‖ :=
      norm_add_le _ _
  have h3 : ‖(E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)
        - (DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ
        - (jInvariantFun τ - 720) ^ 2 * (Ept z) ^ 4‖
      ≤ ‖(E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)
          - (DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ‖
        + ‖(jInvariantFun τ - 720) ^ 2 * (Ept z) ^ 4‖ := norm_sub_le _ _
  have h4 : ‖(E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)
        - (DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ‖
      ≤ ‖E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2‖
        + ‖(DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ‖ := norm_sub_le _ _
  -- the sum of the five term bounds
  have hsum : ‖E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2‖
        + ‖(DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ‖
        + ‖(jInvariantFun τ - 720) ^ 2 * (Ept z) ^ 4‖
        + ‖(jInvariantFun τ - 720) * (Ept z) ^ 2 * (E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)‖
        + ‖(DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ * (jInvariantFun τ - 720)
            * (Ept z) ^ 2‖
        ≤ (cA + cΔ * (27 / 4) + ((27 / 4) + 720) ^ 2 + cA * ((27 / 4) + 720)
            + cΔ * (27 / 4) * ((27 / 4) + 720)) * X := by
    linarith [hT1, hT2, hT3, hT4, hT5]
  calc _ ≤ ‖E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2‖
        + ‖(DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ‖
        + ‖(jInvariantFun τ - 720) ^ 2 * (Ept z) ^ 4‖
        + ‖(jInvariantFun τ - 720) * (Ept z) ^ 2 * (E4Fun z ^ 3 - 1 - 720 * (Ept z) ^ 2)‖
        + ‖(DeltaFun z - (Ept z) ^ 2) * jInvariantFun τ * (jInvariantFun τ - 720)
            * (Ept z) ^ 2‖ := by linarith [h1, h2, h3, h4]
    _ ≤ _ := hsum
    _ ≤ (cA + cΔ * (27 / 4) + ((27 / 4) + 720) ^ 2 + cA * ((27 / 4) + 720)
            + cΔ * (27 / 4) * ((27 / 4) + 720) + 1) * X := by
        have hpos : (0:ℝ) ≤ X := hX0
        nlinarith [hpos]

/-- **`Sh · Sinvref - 1 = O((‖Ept z‖²/‖Ept τ‖²)²)`** (the form used downstream). -/
theorem ShSinvrefFunnelBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z * Compact.Sinvref τ z - 1‖
        ≤ C * (‖Ept z‖ ^ 2 * (‖Ept τ‖ ^ 2)⁻¹) ^ 2 := by
  obtain ⟨C, hC, h⟩ := ShSinvrefBound_exp
  refine ⟨C, hC, fun τ z t hτ ht hz => ?_⟩
  have h' := h τ z t hτ ht hz
  have h2 : (‖Ept τ‖ ^ 2)⁻¹ = Real.exp (2 * Real.pi * τ.im) := by
    have h1 : ‖Ept τ‖ ^ 2 = Real.exp (-(2 * Real.pi * τ.im)) := by
      rw [Work.Residues.norm_Ept, sq, ← Real.exp_add]
      congr 1; ring
    rw [h1, ← Real.exp_neg]
    congr 1; ring
  rw [h2]
  exact h'

end

end Work.Asymptotics.Funnel24Tail
