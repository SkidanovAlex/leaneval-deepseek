import Mathlib
import Submission.Work.BoseKinLoc.Residuals
import Submission.Work.BoseKinLoc.Tprime.kincoeff_weight_decay
import Submission.Work.BoseKinLoc.Tprime.near_coefficient
import Submission.Work.BoseKinLoc.Tprime.profHat_decay_twelve
import Submission.Work.BoseKinLoc.Tprime.profHat_sq_tail_decay
import Submission.Work.BoseKinLoc.Tprime.symA_far_sharp
import Submission.Work.BoseKinLoc.Tprime.symA_second_order_tail
import Submission.Work.BoseKinLoc.Tprime.symA_zero_decay
import Submission.Work.BoseKinLoc.Tprime.symD_value_bound
import Submission.Work.OneBodyKin.Phi
import Submission.Work.OneBodyKin.SecondOrder.boxHat_one_sub_sq_le
import Submission.Work.OneBodyKin.SecondOrder.symD_diff_bound_uniform
import Submission.Work.OneBodyKin.SymBound_iff_SymBoundOne
import Submission.Work.OneBodyKin.SymbolIntegral_fsKinCoeff
import Submission.Work.OneBodyKin.dSpace_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Tprime.tprime_two_regime`

The two-regime symbol bound of Brietzke--Solovej `lm:kinloc` (BS arXiv:1901.00537) at the
FS parameters: the residual `Work.BoseKinLoc.TprimeBound C` is inhabited.

`TprimeBound C` (`Submission/Work/BoseKinLoc/Residuals.lean`) says: for all small `σ > 0`,
all `ℓ > 0` and all smooth compactly supported `ψ`,

    `∫_u bsOneBody ℓ (fsKinCoeff ((σℓ)⁻¹)) u ψ
        ≤ (2π)⁻³ ∫_p tprSym ℓ σ C p · ‖fhat ψ p‖²`,

with the **two-regime** symbol

    `tprSym ℓ σ C p = (‖p‖ − (2σℓ)⁻¹)₊²`   if `‖p‖ ≥ (5/6)(σℓ)⁻¹`,
    `              = C σ³ ‖p‖²`             if `‖p‖ < (5/6)(σℓ)⁻¹`.

This is exactly BS `eq:Fs` (with their smoothness index `M = 5`; the corpus bump `χ` is
`C^∞`, so any `M` is available).  The *bounded* rendering `Cσ‖p‖²/(‖p‖²+β)` of the same
residual is machine-refuted (`Tprime/REFUTATION.md`); the near-region branch `Cσ³‖p‖²` is
load-bearing.

## Route

1. `SymBoundTwo σ C` — the pointwise symbol bound at box size `ℓ = 1` and cut-off `σ⁻¹`
   against the *scale-free* two-regime symbol `tprSymOne`.  This is proved by the case split
   of BS `lm:kinloc`:
   * far region `‖q‖ ≥ (5/6)σ⁻¹`: the sharp far bound `symA_far_sharp` (with the
     reverse-triangle trick `[a−C]₊² ≤ a² − 2C(‖ρ‖−‖p‖) + C²`) leaves the gap
     `−C₀²/12` against `(‖q‖ − C₀/2)²`, which pays the three error terms;
   * near region `‖q‖ < (5/6)σ⁻¹`: the *exact* decomposition
     `F(q) = symA(0)(1 − boxHat q)² + (symA(q) − symA(0)) − 2(2π)⁻³boxHat q (symD(q) − symD(0))`
     together with `symA_second_order_tail`, `symD_diff_bound_uniform` and the polynomial
     decay `symA_zero_decay`.
2. `tprSym_scale` — the homogeneity of `tprSym` in the box momentum, which transfers the
   box-size-`1` statement to every `ℓ > 0`.
3. `FamilyBound`-style assembly (`SymbolIntegral_fsKinCoeff` + the pointwise bound).

## Status

Complete: every declaration in this file has a full proof.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Tprime

open Submission.BoseGases

open Work.OneBodyKin

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The scale-free two-regime symbol -/

/-- The two-regime symbol of BS `lm:kinloc` at box size `1`, as a function of the box momentum
`q ≥ 0`: the far branch `[q − (2σ)⁻¹]₊²` for `q ≥ (5/6)σ⁻¹` and the near branch `Cσ³q²`. -/
def tprSymOne (σ C q : ℝ) : ℝ :=
  if (5 / 6) * σ⁻¹ ≤ q then fsKinCoeff ((2 * σ)⁻¹) q else C * σ ^ 3 * q ^ 2

/-- `tprSymOne` is nonnegative for nonnegative data. -/
lemma tprSymOne_nonneg {σ C : ℝ} (hσ : 0 ≤ σ) (hC : 0 ≤ C) (q : ℝ) : 0 ≤ tprSymOne σ C q := by
  unfold tprSymOne
  split
  · exact fsKinCoeff_nonneg _ _
  · exact mul_nonneg (mul_nonneg hC (pow_nonneg hσ 3)) (sq_nonneg q)

/-- `tprSymOne` is dominated by the square of the box momentum when the near-region
coefficient is `≤ 1`. -/
lemma tprSymOne_le_sq {σ C : ℝ} (hσ : 0 ≤ σ) (hC : 0 ≤ C) (hcoef : C * σ ^ 3 ≤ 1) {q : ℝ}
    (hq : 0 ≤ q) : tprSymOne σ C q ≤ q ^ 2 := by
  unfold tprSymOne
  split
  · rename_i h
    unfold fsKinCoeff
    have hinv : 0 ≤ (2 * σ)⁻¹ := inv_nonneg.mpr (by linarith)
    have hmax : max (q - (2 * σ)⁻¹) 0 ≤ q := max_le (by linarith) hq
    have h0 : 0 ≤ max (q - (2 * σ)⁻¹) 0 := le_max_right _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hmax) (add_nonneg hq h0)]
  · nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg q)]

/-! ## 2. The pointwise symbol bound at box size `1` -/

/-- **The pointwise two-regime symbol bound** at box size `ℓ = 1` and cut-off `σ⁻¹`, against
the scale-free symbol `tprSymOne`. -/
def SymBoundTwo (σ C : ℝ) : Prop :=
  ∀ q : ℝ³, famSym 1 (fsKinCoeff σ⁻¹) q ≤ tprSymOne σ C ‖q‖

/-- The homogeneity of `tprSym` in the box momentum: for `ℓ > 0`,

    `tprSym ℓ σ C p = (ℓ²)⁻¹ · tprSymOne σ C (ℓ‖p‖)`. -/
theorem tprSym_scale (ℓ σ C : ℝ) (hℓ : 0 < ℓ) (p : ℝ³) :
    tprSym ℓ σ C p = (ℓ ^ 2)⁻¹ * tprSymOne σ C (ℓ * ‖p‖) := by
  have hkey : (5 / 6) * (σ * ℓ)⁻¹ * ℓ = (5 / 6) * σ⁻¹ := by
    rw [mul_inv]; field_simp
  have hcond : ((5 / 6) * (σ * ℓ)⁻¹ ≤ ‖p‖) ↔ ((5 / 6) * σ⁻¹ ≤ ℓ * ‖p‖) := by
    constructor
    · intro h
      rw [← hkey]
      calc (5 / 6) * (σ * ℓ)⁻¹ * ℓ ≤ ‖p‖ * ℓ := mul_le_mul_of_nonneg_right h hℓ.le
        _ = ℓ * ‖p‖ := by ring
    · intro h
      have h1 : ℓ * ((5 / 6) * (σ * ℓ)⁻¹) ≤ ℓ * ‖p‖ := by
        rw [mul_comm ℓ ((5 / 6) * (σ * ℓ)⁻¹), hkey]
        exact h
      exact le_of_mul_le_mul_left h1 hℓ
  unfold tprSym tprSymOne
  by_cases h : (5 / 6) * (σ * ℓ)⁻¹ ≤ ‖p‖
  · rw [if_pos h, if_pos (hcond.mp h)]
    have hc : (2 * (σ * ℓ))⁻¹ * ℓ = (2 * σ)⁻¹ := by rw [mul_inv]; field_simp
    rw [Work.OneBodyKin.fsKinCoeff_scale hℓ ((2 * (σ * ℓ))⁻¹) ‖p‖, hc]
  · rw [if_neg h, if_neg (fun hh => h (hcond.mpr hh))]
    field_simp

/-- `tprSym` is nonnegative. -/
lemma tprSym_nonneg {ℓ σ C : ℝ} (hℓ : 0 < ℓ) (hσ : 0 < σ) (hC : 0 < C) (p : ℝ³) :
    0 ≤ tprSym ℓ σ C p := by
  rw [tprSym_scale ℓ σ C hℓ p]
  exact mul_nonneg (by positivity) (tprSymOne_nonneg hσ.le hC.le _)

/-- `tprSym` is dominated by the square of the momentum when the near-region coefficient is
`≤ 1`. -/
lemma tprSym_le_sq {ℓ σ C : ℝ} (hℓ : 0 < ℓ) (hσ : 0 < σ) (hC : 0 ≤ C)
    (hcoef : C * σ ^ 3 ≤ 1) (p : ℝ³) : tprSym ℓ σ C p ≤ ‖p‖ ^ 2 := by
  rw [tprSym_scale ℓ σ C hℓ p]
  have h1 : tprSymOne σ C (ℓ * ‖p‖) ≤ (ℓ * ‖p‖) ^ 2 :=
    tprSymOne_le_sq hσ.le hC hcoef (mul_nonneg hℓ.le (norm_nonneg p))
  have h2 : (ℓ ^ 2)⁻¹ * tprSymOne σ C (ℓ * ‖p‖) ≤ (ℓ ^ 2)⁻¹ * (ℓ * ‖p‖) ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : (ℓ ^ 2)⁻¹ * (ℓ * ‖p‖) ^ 2 = ‖p‖ ^ 2 := by
    field_simp
  linarith [h3 ▸ h2]

/-- The expansion of the projected family symbol in the three `OneBodyKin` pieces. -/
lemma famSym_expand (C : ℝ) (q : ℝ³) :
    famSym 1 (fsKinCoeff C) q
      = symA 1 (fsKinCoeff C) q
        - 2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat 1 q * symD 1 (fsKinCoeff C) q
        + symA 1 (fsKinCoeff C) 0 * (boxHat 1 q) ^ 2 := by
  have h := Phi_eq_expand C q
  unfold Phi at h
  linarith

/-- The projected family symbol, decomposed around the origin so that the `ℓ⁻²`-scale window
excess `symA 1 (fsKinCoeff C₀) q - symA 1 (fsKinCoeff C₀) 0` and the flat cross symbol
`symD 1 (fsKinCoeff C₀) q - symD 1 (fsKinCoeff C₀) 0` appear separately. -/
lemma famSym_near_decomp (C : ℝ) (q : ℝ³) :
    famSym 1 (fsKinCoeff C) q
      = symA 1 (fsKinCoeff C) 0 * (1 - boxHat 1 q) ^ 2
        + (symA 1 (fsKinCoeff C) q - symA 1 (fsKinCoeff C) 0)
        - 2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat 1 q
            * (symD 1 (fsKinCoeff C) q - symD 1 (fsKinCoeff C) 0) := by
  rw [famSym_expand C q, symD_zero_eq_symA_zero (fsKinCoeff C)]
  have hpi : ((2 * Real.pi) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 = 1 :=
    inv_mul_cancel₀ (by positivity)
  linear_combination (-2 * boxHat 1 q * symA 1 (fsKinCoeff C) 0) * hpi

/-- The elementary far-region gap: `(x−C)² + C²/12 ≤ (x−C/2)²` for `x ≥ (5/6)C`. -/
lemma far_gap {C x : ℝ} (hC : 0 < C) (hx : 5 / 6 * C ≤ x) :
    (x - C) ^ 2 + C ^ 2 / 12 ≤ (x - C / 2) ^ 2 := by
  nlinarith [hC, hx]

/-- The far-region arithmetic: the three error terms of the far-region symbol bound are absorbed
by the gap `C₀²/12` once the cut-off is large enough. -/
lemma far_numeric {K₁ K₂ K₃ K₄ mass C₀ : ℝ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hmass : 0 ≤ mass)
    (hC₀ : 6 + 48 * K₂ + 96 * K₁ + 96 * (((2 * Real.pi) ^ 3)⁻¹ * mass * K₃) + 48 * K₄ ≤ C₀) :
    K₂ + 2 * C₀ * K₁ + 2 * (((2 * Real.pi) ^ 3)⁻¹ * mass * K₃) / C₀ ^ 3 + K₄ / C₀ ^ 5
      ≤ C₀ ^ 2 / 12 := by
  have hc : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  set X : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * mass * K₃ with hX
  have hXnn : 0 ≤ X := by rw [hX]; exact mul_nonneg (mul_nonneg hc.le hmass) hK₃
  have hC₀' : 0 < C₀ := by linarith
  have hC₁ : 6 ≤ C₀ := by linarith
  have hC1' : 1 ≤ C₀ := by linarith
  have e1 : 48 * K₂ ≤ C₀ := by linarith
  have e2 : 96 * K₁ ≤ C₀ := by linarith
  have e3 : 96 * X ≤ C₀ := by linarith
  have e4 : 48 * K₄ ≤ C₀ := by linarith
  have h2' : C₀ ≤ C₀ ^ 2 := by nlinarith [hC1']
  have hCp5 : C₀ ≤ C₀ ^ 5 := by
    have h3 : C₀ ^ 2 ≤ C₀ ^ 5 := by
      have h4 : C₀ ^ 2 ≤ C₀ ^ 2 * C₀ ^ 3 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hC1')
      calc C₀ ^ 2 ≤ C₀ ^ 2 * C₀ ^ 3 := h4
        _ = C₀ ^ 5 := by ring
    linarith
  have hCp7 : C₀ ≤ C₀ ^ 7 := by
    have h3 : C₀ ^ 2 ≤ C₀ ^ 7 := by
      have h4 : C₀ ^ 2 ≤ C₀ ^ 2 * C₀ ^ 5 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hC1')
      calc C₀ ^ 2 ≤ C₀ ^ 2 * C₀ ^ 5 := h4
        _ = C₀ ^ 7 := by ring
    linarith
  have h1 : K₂ ≤ C₀ ^ 2 / 48 := by nlinarith [e1, h2']
  have h2 : 2 * C₀ * K₁ ≤ C₀ ^ 2 / 48 := by nlinarith [e2, hC₀']
  have h3 : 2 * X / C₀ ^ 3 ≤ C₀ ^ 2 / 48 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < C₀ ^ 3)]
    have h : 2 * X ≤ C₀ ^ 5 / 48 := by nlinarith [e3, hCp5]
    calc 2 * X ≤ C₀ ^ 5 / 48 := h
      _ = C₀ ^ 2 / 48 * C₀ ^ 3 := by ring
  have h4 : K₄ / C₀ ^ 5 ≤ C₀ ^ 2 / 48 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < C₀ ^ 5)]
    have h : K₄ ≤ C₀ ^ 7 / 48 := by nlinarith [e4, hCp7]
    calc K₄ ≤ C₀ ^ 7 / 48 := h
      _ = C₀ ^ 2 / 48 * C₀ ^ 5 := by ring
  linarith

set_option maxHeartbeats 1600000 in
/-- **The pointwise two-regime bound** (all small `σ`, box size `1`): there is a universal
constant `C` (depending only on the bump `χ`) such that for every small `σ > 0` the symbol of
the projected moving-box family form at the cut-off `σ⁻¹` is dominated by the scale-free
two-regime symbol `tprSymOne σ C`. -/
theorem two_regime_pointwise :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ s₀ →
      SymBoundTwo σ C ∧ C * σ ^ 3 ≤ 1 := by
  obtain ⟨K₃, hK₃nn, hK₃⟩ := kincoeff_weight_decay
  obtain ⟨K₄, hK₄nn, hK₄⟩ := symA_zero_decay
  obtain ⟨K₅, hK₅nn, hK₅⟩ := profHat_sq_tail_decay
  set K₁ : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ with hK₁def
  set K₂ : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2 with hK₂def
  set mass : ℝ := ∫ z : ℝ³, |chi z| with hmassdef
  set M : ℝ := ∫ z : ℝ³, |chi z| * ‖z‖ ^ 2 with hMdef
  have hK₁nn : 0 ≤ K₁ := by
    rw [hK₁def]
    exact mul_nonneg (by positivity)
      (integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (norm_nonneg p)))
  have hK₂nn : 0 ≤ K₂ := by
    rw [hK₂def]
    exact mul_nonneg (by positivity)
      (integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hmassnn : 0 ≤ mass := by rw [hmassdef]; exact integral_nonneg (fun z => abs_nonneg _)
  have hMnn : 0 ≤ M := by
    rw [hMdef]; exact integral_nonneg (fun z => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  obtain ⟨C, hC1, hnear⟩ := near_coefficient K₃ K₄ K₅ M
  have hCpos : 0 < C := by linarith
  set D : ℝ := 6 + 48 * K₂ + 96 * K₁ + 96 * (((2 * Real.pi) ^ 3)⁻¹ * mass * K₃) + 48 * K₄
    with hDdef
  have hD6 : 6 ≤ D := by
    rw [hDdef]
    have hX : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ * mass * K₃ :=
      mul_nonneg (mul_nonneg (by positivity) hmassnn) hK₃nn
    linarith
  have hDpos : 0 < D := by linarith
  have h2C1 : 0 < 2 * C + 1 := by linarith
  refine ⟨C, hCpos, min (1 / D) (1 / (2 * C + 1)), lt_min (by positivity) (by positivity), ?_⟩
  intro σ hσ hσs
  have hmin1 : σ ≤ 1 / D := le_trans hσs (min_le_left _ _)
  have hmin2 : σ ≤ 1 / (2 * C + 1) := le_trans hσs (min_le_right _ _)
  have hσD : D ≤ σ⁻¹ := by
    have h' : σ ≤ D⁻¹ := by simpa [div_eq_mul_inv] using hmin1
    exact (le_inv_comm₀ hDpos hσ).mpr h'
  have hσD' : 6 + 48 * K₂ + 96 * K₁ + 96 * (((2 * Real.pi) ^ 3)⁻¹ * mass * K₃) + 48 * K₄
      ≤ σ⁻¹ := by
    rw [hDdef] at hσD
    exact hσD
  have hcoef : C * σ ^ 3 ≤ 1 := by
    have hσsq : σ ^ 3 ≤ (1 / (2 * C + 1)) ^ 3 := pow_le_pow_left₀ hσ.le hmin2 3
    have h5 : C ≤ (2 * C + 1) ^ 3 := by
      have h6 : 1 ≤ 2 * C + 1 := by linarith
      have h7 : 2 * C + 1 ≤ (2 * C + 1) ^ 3 := by
        have h8 : (2 * C + 1) ^ 1 ≤ (2 * C + 1) ^ 3 := pow_le_pow_right₀ h6 (by norm_num)
        simpa using h8
      linarith
    calc C * σ ^ 3 ≤ C * (1 / (2 * C + 1)) ^ 3 := mul_le_mul_of_nonneg_left hσsq hCpos.le
      _ = C / (2 * C + 1) ^ 3 := by rw [div_eq_mul_inv, mul_pow, one_pow, inv_pow]; ring
      _ ≤ 1 := by
        rw [div_le_one (pow_pos (by linarith : (0 : ℝ) < 2 * C + 1) 3)]
        exact h5
  refine ⟨?_, hcoef⟩
  have hCb1 : 1 ≤ σ⁻¹ := le_trans (by linarith : (1 : ℝ) ≤ D) hσD
  have hCb6 : 6 ≤ σ⁻¹ := le_trans hD6 hσD
  have hσinvpos : 0 < σ⁻¹ := by positivity
  intro q
  by_cases hq : (5 / 6) * σ⁻¹ ≤ ‖q‖
  · -- far region
    rw [tprSymOne, if_pos hq, famSym_expand (σ⁻¹) q]
    have hsymA := symA_far_sharp (σ⁻¹) hσinvpos.le q
    rw [← hK₂def, ← hK₁def] at hsymA
    have hsymD := symD_value_bound (σ⁻¹) q
    have hW := hK₃ (σ⁻¹) hCb1
    have hZ := hK₄ (σ⁻¹) hCb1
    have hbox : |boxHat 1 q| ≤ 1 := by
      simpa using abs_boxHat_le (ℓ := 1) (by norm_num) q
    have hcross : -2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat 1 q * symD 1 (fsKinCoeff (σ⁻¹)) q
        ≤ 2 * (((2 * Real.pi) ^ 3)⁻¹ * mass * K₃) / (σ⁻¹) ^ 3 := by
      have hcnn : 0 ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ := by positivity
      have habs : |boxHat 1 q * symD 1 (fsKinCoeff (σ⁻¹)) q| ≤ mass * K₃ / (σ⁻¹) ^ 3 := by
        rw [abs_mul]
        have h1 : |symD 1 (fsKinCoeff (σ⁻¹)) q| ≤ mass * K₃ / (σ⁻¹) ^ 3 := by
          have h2 : mass * (∫ p, fsKinCoeff (σ⁻¹) ‖p‖ * |profHat p|) ≤ mass * (K₃ / (σ⁻¹) ^ 3) :=
            mul_le_mul_of_nonneg_left hW hmassnn
          have h3 : mass * (K₃ / (σ⁻¹) ^ 3) = mass * K₃ / (σ⁻¹) ^ 3 := by ring
          linarith [hsymD, h2, h3.le]
        calc |boxHat 1 q| * |symD 1 (fsKinCoeff (σ⁻¹)) q| ≤ 1 * (mass * K₃ / (σ⁻¹) ^ 3) :=
              mul_le_mul hbox h1 (abs_nonneg _) (by norm_num)
          _ = mass * K₃ / (σ⁻¹) ^ 3 := by ring
      have hneg := neg_le_abs (boxHat 1 q * symD 1 (fsKinCoeff (σ⁻¹)) q)
      calc -2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat 1 q * symD 1 (fsKinCoeff (σ⁻¹)) q
          = (2 * ((2 * Real.pi) ^ 3)⁻¹) * (-(boxHat 1 q * symD 1 (fsKinCoeff (σ⁻¹)) q)) := by
            ring
        _ ≤ (2 * ((2 * Real.pi) ^ 3)⁻¹) * |boxHat 1 q * symD 1 (fsKinCoeff (σ⁻¹)) q| :=
              mul_le_mul_of_nonneg_left hneg hcnn
        _ ≤ (2 * ((2 * Real.pi) ^ 3)⁻¹) * (mass * K₃ / (σ⁻¹) ^ 3) :=
              mul_le_mul_of_nonneg_left habs hcnn
        _ = 2 * (((2 * Real.pi) ^ 3)⁻¹ * mass * K₃) / (σ⁻¹) ^ 3 := by ring
    have hmass_term : symA 1 (fsKinCoeff (σ⁻¹)) 0 * (boxHat 1 q) ^ 2 ≤ K₄ / (σ⁻¹) ^ 5 := by
      have hb2 : (boxHat 1 q) ^ 2 ≤ 1 := by
        have h := abs_nonneg (boxHat 1 q)
        nlinarith [hbox, sq_abs (boxHat 1 q)]
      calc symA 1 (fsKinCoeff (σ⁻¹)) 0 * (boxHat 1 q) ^ 2 ≤ (K₄ / (σ⁻¹) ^ 5) * 1 :=
            mul_le_mul hZ hb2 (sq_nonneg _) (by positivity)
        _ = K₄ / (σ⁻¹) ^ 5 := by ring
    have htot : famSym 1 (fsKinCoeff (σ⁻¹)) q
        ≤ (‖q‖ - σ⁻¹) ^ 2 + (K₂ + 2 * (σ⁻¹) * K₁
            + 2 * (((2 * Real.pi) ^ 3)⁻¹ * mass * K₃) / (σ⁻¹) ^ 3 + K₄ / (σ⁻¹) ^ 5) := by
      rw [famSym_expand (σ⁻¹) q]
      linarith [hsymA, hcross, hmass_term]
    have hnum := far_numeric hK₁nn hK₂nn hK₃nn hK₄nn hmassnn hσD'
    have hgap := far_gap (C := σ⁻¹) hσinvpos hq
    have hrhs : fsKinCoeff ((2 * σ)⁻¹) ‖q‖ = (‖q‖ - σ⁻¹ / 2) ^ 2 := by
      have h2inv : (2 * σ)⁻¹ = σ⁻¹ / 2 := by
        rw [mul_inv]
        ring
      rw [h2inv, fsKinCoeff,
        max_eq_left (by linarith [hq] : (0 : ℝ) ≤ ‖q‖ - σ⁻¹ / 2)]
    rw [hrhs]
    nlinarith [htot, hnum, hgap]
  · -- near region
    rw [tprSymOne, if_neg hq, famSym_near_decomp (σ⁻¹) q]
    have hq' : ‖q‖ ≤ 5 / 6 * σ⁻¹ := le_of_lt (not_le.mp hq)
    have hxnn : 0 ≤ ‖q‖ := norm_nonneg q
    have hA0 := hK₄ (σ⁻¹) hCb1
    have hboxsq := SecondOrder.boxHat_one_sub_sq_le q
    have hA2 := symA_second_order_tail (σ⁻¹) hσinvpos q hq'
    have htail := hK₅ ((σ⁻¹) / 6) (by linarith)
    have hDd := SecondOrder.symD_diff_bound_uniform (σ⁻¹) q
    rw [← hMdef] at hDd
    have hW := hK₃ (σ⁻¹) hCb1
    have hbox : |boxHat 1 q| ≤ 1 := by
      simpa using abs_boxHat_le (ℓ := 1) (by norm_num) q
    have ht1 : symA 1 (fsKinCoeff (σ⁻¹)) 0 * (1 - boxHat 1 q) ^ 2
        ≤ K₄ / (σ⁻¹) ^ 5 * ((9 / 64) * ‖q‖ ^ 4) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hA0 hboxsq (sq_nonneg _) (by positivity)
    have ht2 : symA 1 (fsKinCoeff (σ⁻¹)) q - symA 1 (fsKinCoeff (σ⁻¹)) 0
        ≤ 4 * ((2 * Real.pi) ^ 3)⁻¹ * (K₅ / (((σ⁻¹) / 6) ^ 6)) * ‖q‖ ^ 2 := by
      calc symA 1 (fsKinCoeff (σ⁻¹)) q - symA 1 (fsKinCoeff (σ⁻¹)) 0
          ≤ (4 * ((2 * Real.pi) ^ 3)⁻¹
              * (∫ p in {p : ℝ³ | (σ⁻¹) / 6 < ‖p‖}, (profHat p) ^ 2)) * ‖q‖ ^ 2 := hA2
        _ ≤ (4 * ((2 * Real.pi) ^ 3)⁻¹ * (K₅ / (((σ⁻¹) / 6) ^ 6))) * ‖q‖ ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left htail (by positivity)
        _ = 4 * ((2 * Real.pi) ^ 3)⁻¹ * (K₅ / (((σ⁻¹) / 6) ^ 6)) * ‖q‖ ^ 2 := by ring
    have ht3 : -2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat 1 q
          * (symD 1 (fsKinCoeff (σ⁻¹)) q - symD 1 (fsKinCoeff (σ⁻¹)) 0)
        ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ * (M * ‖q‖ ^ 2 * (K₃ / (σ⁻¹) ^ 3)) := by
      have hcnn : 0 ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ := by positivity
      have habs : |boxHat 1 q
          * (symD 1 (fsKinCoeff (σ⁻¹)) q - symD 1 (fsKinCoeff (σ⁻¹)) 0)|
          ≤ M * ‖q‖ ^ 2 * (K₃ / (σ⁻¹) ^ 3) := by
        rw [abs_mul]
        have h1 : |symD 1 (fsKinCoeff (σ⁻¹)) q - symD 1 (fsKinCoeff (σ⁻¹)) 0|
            ≤ M * ‖q‖ ^ 2 * (K₃ / (σ⁻¹) ^ 3) := by
          have h2 : M * ‖q‖ ^ 2 * (∫ p, fsKinCoeff (σ⁻¹) ‖p‖ * |profHat p|)
              ≤ M * ‖q‖ ^ 2 * (K₃ / (σ⁻¹) ^ 3) :=
            mul_le_mul_of_nonneg_left hW (mul_nonneg hMnn (sq_nonneg _))
          linarith [hDd, h2]
        calc |boxHat 1 q| * |symD 1 (fsKinCoeff (σ⁻¹)) q - symD 1 (fsKinCoeff (σ⁻¹)) 0|
            ≤ 1 * (M * ‖q‖ ^ 2 * (K₃ / (σ⁻¹) ^ 3)) :=
              mul_le_mul hbox h1 (abs_nonneg _) (by norm_num)
          _ = M * ‖q‖ ^ 2 * (K₃ / (σ⁻¹) ^ 3) := by ring
      have hneg := neg_le_abs (boxHat 1 q
        * (symD 1 (fsKinCoeff (σ⁻¹)) q - symD 1 (fsKinCoeff (σ⁻¹)) 0))
      calc -2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat 1 q
            * (symD 1 (fsKinCoeff (σ⁻¹)) q - symD 1 (fsKinCoeff (σ⁻¹)) 0)
          = (2 * ((2 * Real.pi) ^ 3)⁻¹) * (-(boxHat 1 q
              * (symD 1 (fsKinCoeff (σ⁻¹)) q - symD 1 (fsKinCoeff (σ⁻¹)) 0))) := by ring
        _ ≤ (2 * ((2 * Real.pi) ^ 3)⁻¹) * |boxHat 1 q
              * (symD 1 (fsKinCoeff (σ⁻¹)) q - symD 1 (fsKinCoeff (σ⁻¹)) 0)| :=
              mul_le_mul_of_nonneg_left hneg hcnn
        _ ≤ (2 * ((2 * Real.pi) ^ 3)⁻¹) * (M * ‖q‖ ^ 2 * (K₃ / (σ⁻¹) ^ 3)) :=
              mul_le_mul_of_nonneg_left habs hcnn
        _ = 2 * ((2 * Real.pi) ^ 3)⁻¹ * (M * ‖q‖ ^ 2 * (K₃ / (σ⁻¹) ^ 3)) := by ring
    have htot : famSym 1 (fsKinCoeff (σ⁻¹)) q
        ≤ K₄ / (σ⁻¹) ^ 5 * ((9 / 64) * ‖q‖ ^ 4)
          + 4 * ((2 * Real.pi) ^ 3)⁻¹ * (K₅ / (((σ⁻¹) / 6) ^ 6)) * ‖q‖ ^ 2
          + 2 * ((2 * Real.pi) ^ 3)⁻¹ * (M * ‖q‖ ^ 2 * (K₃ / (σ⁻¹) ^ 3)) := by
      rw [famSym_near_decomp (σ⁻¹) q]
      linarith [ht1, ht2, ht3]
    have hnum := hnear (σ⁻¹) ‖q‖ hCb6 hxnn hq'
    have hs3 : ((σ⁻¹) ^ 3)⁻¹ = σ ^ 3 := by rw [inv_pow, inv_inv]
    rw [hs3] at hnum
    linarith [htot, hnum]

/-- **From the pointwise two-regime bound to the residual** `TprimeBound`. -/
theorem tprimeBound_of_two_regime {C s₀ : ℝ} (hs₀ : 0 < s₀) (hC : 0 < C)
    (h : ∀ σ : ℝ, 0 < σ → σ ≤ s₀ → SymBoundTwo σ C ∧ C * σ ^ 3 ≤ 1) :
    Work.BoseKinLoc.TprimeBound C := by
  refine ⟨s₀, hs₀, ?_⟩
  intro σ hσ hσs ψ hψ hcs ℓ hℓ hint
  obtain ⟨hSym, hcoef⟩ := h σ hσ hσs
  have hff : (∫ u : ℝ³, Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) u ψ)
      = Work.BSKinetic.bsFamilyForm ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) ψ := rfl
  rw [hff, Work.OneBodyKin.SymbolIntegral_fsKinCoeff hℓ ψ hψ hcs]
  have hpt : ∀ q : ℝ³, famSym ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) q
      ≤ tprSym ℓ σ C q := by
    intro q
    have h2 : (σ * ℓ)⁻¹ * ℓ = σ⁻¹ := by rw [mul_inv]; field_simp
    have h1 : famSym 1 (Submission.BoseGases.fsKinCoeff (σ⁻¹)) (ℓ • q)
        ≤ tprSymOne σ C ‖ℓ • q‖ := hSym (ℓ • q)
    have h3 := Work.OneBodyKin.famSym_kinCoeff_scale (c := (σ * ℓ)⁻¹) hℓ q
    rw [h2] at h3
    rw [h3] at h1
    have h4 : ℓ ^ 2 * famSym ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) q
        ≤ tprSymOne σ C (ℓ * ‖q‖) := by
      simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] using h1
    have h5 : famSym ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) q
        ≤ (ℓ ^ 2)⁻¹ * tprSymOne σ C (ℓ * ‖q‖) := by
      have h4a : famSym ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) q * ℓ ^ 2
          ≤ tprSymOne σ C (ℓ * ‖q‖) := by
        rw [mul_comm (famSym ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) q) (ℓ ^ 2)]
        exact h4
      rw [show (ℓ ^ 2)⁻¹ * tprSymOne σ C (ℓ * ‖q‖)
          = tprSymOne σ C (ℓ * ‖q‖) / ℓ ^ 2 by rw [div_eq_mul_inv, mul_comm]]
      exact (le_div_iff₀ (pow_pos hℓ 2)).mpr h4a
    rw [tprSym_scale ℓ σ C hℓ q]
    exact h5
  have hψint : Integrable (fun z : ℝ³ => (ψ z : ℂ)) := by
    refine (Complex.continuous_ofReal.comp hψ.continuous).integrable_of_hasCompactSupport ?_
    exact hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  have hcontk : Continuous
      (fun q : ℝ³ => Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q) :=
    Work.OneBodyKin.continuous_kinFT hψint
  have hmeas : AEStronglyMeasurable (fun q : ℝ³ =>
      tprSym ℓ σ C q * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2) volume := by
    have hT : Measurable (fun q : ℝ³ => tprSym ℓ σ C q) := by
      have hc : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff ((2 * (σ * ℓ))⁻¹) r) := by
        unfold Submission.BoseGases.fsKinCoeff
        exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
      have hfs : Measurable fun q : ℝ³ =>
          Submission.BoseGases.fsKinCoeff ((2 * (σ * ℓ))⁻¹) ‖q‖ :=
        hc.measurable.comp measurable_norm
      have hnear : Measurable fun q : ℝ³ => C * σ ^ 3 * ‖q‖ ^ 2 :=
        measurable_const.mul (measurable_norm.pow_const 2)
      unfold tprSym
      exact Measurable.ite (measurableSet_le measurable_const measurable_norm) hfs hnear
    exact (AEMeasurable.mul (μ := volume) hT.aemeasurable
      (hcontk.norm.pow 2).aemeasurable).aestronglyMeasurable
  have hg : Integrable (fun q : ℝ³ => tprSym ℓ σ C q
      * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2) := by
    refine (Work.SmallBoxTBWord.integrable_kinFT_energy_cspt ψ hψ hcs).mono' hmeas ?_
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (tprSym_nonneg hℓ hσ hC q) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (tprSym_le_sq hℓ hσ hC.le hcoef q) (sq_nonneg _)
  have hle : (∫ q : ℝ³, famSym ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) q
        * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
      ≤ ∫ q : ℝ³, tprSym ℓ σ C q
        * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2 := by
    by_cases hf : Integrable (fun q : ℝ³ =>
        famSym ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) q
        * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
    · exact integral_mono_ae hf hg (Filter.Eventually.of_forall
        (fun q => mul_le_mul_of_nonneg_right (hpt q) (sq_nonneg _)))
    · rw [integral_undef hf]
      exact integral_nonneg (fun q => mul_nonneg (tprSym_nonneg hℓ hσ hC q) (sq_nonneg _))
  exact mul_le_mul_of_nonneg_left hle (by positivity)

theorem tprime_two_regime : ∃ C : ℝ, 0 < C ∧ Work.BoseKinLoc.TprimeBound C := by
  obtain ⟨C, hC, s₀, hs₀, h⟩ := two_regime_pointwise
  exact ⟨C, hC, tprimeBound_of_two_regime hs₀ hC h⟩

end Work.BoseKinLoc.Tprime
