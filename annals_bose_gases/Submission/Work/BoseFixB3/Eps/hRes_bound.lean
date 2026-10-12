import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseFixB3.Eps.kinFT_bumpSq_decay
import Submission.Work.BoseFixB3.Eps.kinFT_chiU_sq_scaling
import Submission.Work.BoseFixB3.Eps.tail_zpow_integral
import Submission.Work.BoseFixB3.Scaling.chiU_sq_indicator
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Eps/hRes_bound` — the smallness of `(1 − f_L)(χ_ℓ²)`

The analytic heart of FS's `ε₂`-Cauchy–Schwarz (`lem:Q3-splitting1`, ll. 1531–1545 of
`Papers/fournais_solovej/final_v2.tex`): the low-momentum multiplier `f_L = lowMult fc κ ℓ`
(the symbol `f(‖p‖/κ)`, a smooth cut-off at `κ`) leaves the window profile `χ_ℓ²` almost
invariant, so

  `|(1 − f_L)(χ_ℓ²)(z)| ≤ CH·(κℓ)^{-49}`

uniformly in `z`, provided `κ ℓ ≥ 1` (FS's dilute regime, where `κℓ = d^{-2}`, and the
prescription `M = 48` makes `d^{2(M-1)} = d^{94}` the error coefficient).

## Proof

Fourier inversion (`Scaling.chiU_sq_indicator` + `kinFT_inversion_indChiSq`) writes
`(1 − f_L)(χ_ℓ²)` as the inverse transform of `(1 − f(‖p‖/κ))·kinFT(χ_ℓ²)`.  The symbol
`1 − f(‖p‖/κ)` vanishes for `‖p‖ ≤ κ` and is bounded by `1`, while

  `kinFT(χ_ℓ²)(p) = ℓ³·kinFT(χ²)(ℓ•p)`,  `‖kinFT(χ²)(q)‖ ≤ Cb(1+‖q‖)^{-52}`

(Schwartz decay of the Fourier transform of the fixed bump `χ²`, `kinFT_bumpSq_decay`).
Hence the inverse transform is bounded by

  `(2π)^{-3}∫_{‖p‖ ≥ κ} Cb ℓ³ (1+ℓ‖p‖)^{-52} dp ≤ (2π)^{-3}Cb ℓ^{3-52}∫_{‖p‖ ≥ κ}‖p‖^{-52}dp
     ≤ (2π)^{-3}Cb Ct (κℓ)^{-49}`

(`tail_zpow_integral`).  The exponent `49 > M - 1 = 47` leaves room for the final
comparison with `d^{2(M-1)}`.
-/

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators FourierTransform

namespace Work.BoseFixB3.Eps

local notation "ℝ3" => EuclideanSpace ℝ (Fin 3)

/-- The ℂ-valued indicator-restricted window profile `1_{acube ℓ}·χ_ℓ²` — the function
whose `kinFT` appears in `lowMult`. -/
def indChiSq (ℓ : ℝ) : ℝ3 → ℂ :=
  fun y => (((Submission.BoseGases.acube ℓ).indicator
      (fun w => Submission.BoseGases.chiU ℓ 0 w ^ 2) y : ℝ) : ℂ)

/-- `1_{acube ℓ}·χ_ℓ² = φ(ℓ⁻¹·)` (the corpus's `Scaling.chiU_sq_indicator`). -/
lemma indChiSq_eq (ℓ : ℝ) (hℓ : 0 < ℓ) :
    indChiSq ℓ = fun y : ℝ3 =>
      ((Work.BoseFixB3.Scaling.phi ((ℓ⁻¹) • y) : ℝ) : ℂ) := by
  funext y
  simp only [indChiSq]
  rw [Work.BoseFixB3.Scaling.chiU_sq_indicator ℓ hℓ y]

lemma continuous_indChiSq (ℓ : ℝ) (hℓ : 0 < ℓ) : Continuous (indChiSq ℓ) := by
  rw [indChiSq_eq ℓ hℓ]
  have hlin : Continuous (fun y : ℝ3 => (ℓ⁻¹) • y) := by fun_prop
  exact Complex.continuous_ofReal.comp (Work.BoseFixB3.Scaling.phi_continuous.comp hlin)

lemma hasCompactSupport_indChiSq (ℓ : ℝ) (hℓ : 0 < ℓ) : HasCompactSupport (indChiSq ℓ) := by
  rw [indChiSq_eq ℓ hℓ]
  have hφ : HasCompactSupport (fun y : ℝ3 => ((Work.BoseFixB3.Scaling.phi y : ℝ) : ℂ)) :=
    Work.BoseFixB3.Scaling.phi_hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  exact hφ.comp_homeomorph (Homeomorph.smulOfNeZero (ℓ⁻¹) (inv_ne_zero (ne_of_gt hℓ)))

lemma integrable_indChiSq (ℓ : ℝ) (hℓ : 0 < ℓ) : Integrable (indChiSq ℓ) :=
  (continuous_indChiSq ℓ hℓ).integrable_of_hasCompactSupport (hasCompactSupport_indChiSq ℓ hℓ)

/-- `bumpSqC = Scaling.phiC` (definitional). -/
lemma bumpSqC_eq_phiC : bumpSqC = Work.BoseFixB3.Scaling.phiC := rfl

/-- `indChiSq ℓ = (χ_ℓ² : ℂ)` (the indicator is redundant: the profile vanishes off the box). -/
lemma indChiSq_eq_plain (ℓ : ℝ) (hℓ : 0 < ℓ) :
    indChiSq ℓ = fun y : ℝ3 => (((Submission.BoseGases.chiU ℓ 0 y) ^ 2 : ℝ) : ℂ) := by
  funext y
  simp only [indChiSq]
  rw [Work.BoseFixB3.Scaling.chiU_sq_indicator ℓ hℓ y]
  simp [Work.BoseFixB3.Scaling.phi, Submission.BoseGases.chiU]


/-- `kinFT (indChiSq ℓ)` is integrable (it is the Fourier transform of a Schwartz function,
up to the scaling `ℓ`). -/
lemma integrable_kinFT_indChiSq (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Integrable (fun p : ℝ3 => Submission.BoseGases.kinFT (indChiSq ℓ) p) := by
  have hFint : Integrable (fun q : ℝ3 => (𝓕 Work.BoseFixB3.Scaling.phiSch) q) :=
    SchwartzMap.integrable _
  have hcomp1 : Integrable (fun q : ℝ3 =>
      (𝓕 Work.BoseFixB3.Scaling.phiSch) ((2 * π)⁻¹ • q)) :=
    hFint.comp_smul (by positivity)
  have hkin : Integrable (fun q : ℝ3 =>
      Submission.BoseGases.kinFT Work.BoseFixB3.Scaling.phiC q) := by
    refine hcomp1.congr ?_
    filter_upwards with q
    rw [Work.BoseFixB3.Scaling.kinFT_phiC_fourier]
  have hkin2 : Integrable (fun p : ℝ3 =>
      Submission.BoseGases.kinFT Work.BoseFixB3.Scaling.phiC (ℓ • p)) :=
    hkin.comp_smul (ne_of_gt hℓ)
  have h3 : Integrable (fun p : ℝ3 =>
      (ℓ : ℂ) ^ 3 * Submission.BoseGases.kinFT bumpSqC (ℓ • p)) := hkin2.const_mul _
  refine h3.congr (Filter.Eventually.of_forall fun p => ?_)
  beta_reduce
  symm
  rw [indChiSq_eq_plain ℓ hℓ]
  rw [show (fun y : ℝ3 => (((Submission.BoseGases.chiU ℓ 0 y) ^ 2 : ℝ) : ℂ))
      = fun y : ℝ3 => (Work.BoseFixB3.Scaling.phi ((ℓ⁻¹) • y) : ℂ) from by
    funext y
    simp [Work.BoseFixB3.Scaling.phi, Submission.BoseGases.chiU]]
  rw [Work.BoseFixB3.Scaling.kinFT_scaled_phi ℓ hℓ p, Complex.real_smul, ← bumpSqC_eq_phiC,
    show (((ℓ ^ 3 : ℝ)) : ℂ) = (ℓ : ℂ) ^ 3 by push_cast; ring]

/-- **Fourier inversion for the window profile** `χ_ℓ² = φ(ℓ⁻¹·)`, in the corpus's
`p`-convention: `(2π)^{-3}∫_p e^{i⟪p,z⟫}·kinFT(χ_ℓ²)(p) dp = χ_ℓ²(z)`. -/
lemma kinFT_inversion_indChiSq (ℓ : ℝ) (hℓ : 0 < ℓ) (z : ℝ3) :
    ((((2 * π) ^ 3 : ℝ)) : ℂ)⁻¹ * (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
        Submission.BoseGases.kinFT (indChiSq ℓ) p)
      = ((Submission.BoseGases.chiU ℓ 0 z ^ 2 : ℝ) : ℂ) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hpine : (2 * π : ℝ) ≠ 0 := ne_of_gt hpi
  have hfin : Module.finrank ℝ ℝ3 = 3 := by simp [EuclideanSpace]
  set F : ℝ3 → ℂ := fun y => (Work.BoseFixB3.Scaling.phi ((ℓ⁻¹) • y) : ℂ) with hFdef
  have hFind : ∀ y : ℝ3, indChiSq ℓ y = F y := fun y => congrFun (indChiSq_eq ℓ hℓ) y
  have hfeq : F = indChiSq ℓ := funext fun y => (hFind y).symm
  have hFint : Integrable F :=
    (integrable_indChiSq ℓ hℓ).congr (Filter.Eventually.of_forall fun y => hFind y)
  have hGint : Integrable (fun q : ℝ3 => (𝓕 F) q) := by
    have hG := integrable_kinFT_indChiSq ℓ hℓ
    have hcomp : Integrable (fun q : ℝ3 =>
        Submission.BoseGases.kinFT (indChiSq ℓ) ((2 * π) • q)) :=
      hG.comp_smul hpine
    refine hcomp.congr (Filter.Eventually.of_forall fun q => ?_)
    beta_reduce
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, ← hfeq]
    exact congrArg (𝓕 F) (inv_smul_smul₀ hpine q)
  have hfourier := MeasureTheory.Integrable.fourierInv_fourier_eq (f := F) hFint hGint
    ((Complex.continuous_ofReal.comp
      (Work.BoseFixB3.Scaling.phi_continuous.comp (by fun_prop))).continuousAt (x := z))
  -- the integral representation of the inverse transform
  have hrep : (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
        (𝓕 F) ((2 * π)⁻¹ • p))
      = ((((2 * π : ℝ)) ^ 3 : ℝ) : ℂ) *
          ((FourierTransform.fourierInv (FourierTransform.fourier F)) z) := by
    have hpt : ∀ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * (𝓕 F) ((2 * π)⁻¹ • p)
        = Complex.exp (↑(2 * π * inner ℝ ((2 * π)⁻¹ • p) z) * Complex.I) *
            (𝓕 F) ((2 * π)⁻¹ • p) := by
      intro p
      have h1 : (2 * π * inner ℝ ((2 * π)⁻¹ • p) z) = inner ℝ p z := by
        rw [real_inner_smul_left]
        field_simp
      rw [h1]
      congr 1
      rw [mul_comm Complex.I]
    set H : ℝ3 → ℂ := fun y : ℝ3 =>
      Complex.exp (↑(2 * π * inner ℝ y z) * Complex.I) * (𝓕 F) y with hHdef
    have hcomp : (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * (𝓕 F) ((2 * π)⁻¹ • p))
        = ∫ x : ℝ3, H ((2 * π)⁻¹ • x) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hHdef]
      exact hpt p
    have hsubst : (∫ x : ℝ3, H ((2 * π)⁻¹ • x)) = (2 * π : ℝ) ^ 3 • (∫ x : ℝ3, H x) := by
      have h := Measure.integral_comp_inv_smul_of_nonneg volume H hpi.le
      rw [hfin] at h
      exact h
    have hred : (∫ x : ℝ3, H x)
        = ∫ v : ℝ3, Complex.exp (↑(2 * π * inner ℝ v z) * Complex.I) * (𝓕 F) v := by
      apply integral_congr_ae
      filter_upwards with v
      rw [hHdef]
    calc (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * (𝓕 F) ((2 * π)⁻¹ • p))
        = ∫ x : ℝ3, H ((2 * π)⁻¹ • x) := hcomp
      _ = (2 * π : ℝ) ^ 3 • (∫ x : ℝ3, H x) := hsubst
      _ = ((((2 * π : ℝ)) ^ 3 : ℝ) : ℂ) * (∫ x : ℝ3, H x) := by rw [Complex.real_smul]
      _ = ((((2 * π : ℝ)) ^ 3 : ℝ) : ℂ) * (∫ v : ℝ3,
            Complex.exp (↑(2 * π * inner ℝ v z) * Complex.I) * (𝓕 F) v) := by rw [hred]
      _ = ((((2 * π : ℝ)) ^ 3 : ℝ) : ℂ) *
            ((FourierTransform.fourierInv (FourierTransform.fourier F)) z) := by
          congr 1
          rw [Real.fourierInv_eq']
          apply integral_congr_ae
          filter_upwards with v
          rw [smul_eq_mul]
  have hkin : (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
        Submission.BoseGases.kinFT (indChiSq ℓ) p)
      = (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * (𝓕 F) ((2 * π)⁻¹ • p)) := by
    apply integral_congr_ae
    filter_upwards with p
    congr 1
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, ← hfeq]
  rw [hkin, hrep, hfourier]
  have hne : ((((2 * π) ^ 3 : ℝ)) : ℂ) ≠ 0 := by
    have h : ((2 * π) ^ 3 : ℝ) ≠ 0 := by positivity
    exact_mod_cast h
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  simp [hFdef, Work.BoseFixB3.Scaling.phi, Submission.BoseGases.chiU]

/-- Arithmetic helper: for `ℓ, L > 0` with `ℓ L ≥ 1`,
`ℓ³/(1+ℓL)^52 ≤ ℓ^{-49}L^{-52}`. -/
lemma div_pow_le_zpow {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (h1 : 1 ≤ ℓ * L) :
    ℓ ^ 3 / (1 + ℓ * L) ^ 52 ≤ ℓ ^ (-(49 : ℤ)) * (L ^ 52)⁻¹ := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hpow : ℓ ^ (-(49 : ℤ)) * ℓ ^ 52 = ℓ ^ 3 := by
    rw [← zpow_natCast ℓ 52, ← zpow_add₀ hℓne]
    norm_num
  have h3 : (ℓ * L) ^ 52 ≤ (1 + ℓ * L) ^ 52 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith [mul_pos hℓ hL]
  have hkey : ℓ ^ 3 * L ^ 52 ≤ ℓ ^ (-(49 : ℤ)) * (1 + ℓ * L) ^ 52 := by
    calc ℓ ^ 3 * L ^ 52 = ℓ ^ (-(49 : ℤ)) * (ℓ * L) ^ 52 := by
          rw [mul_pow, ← hpow]
          ring
      _ ≤ ℓ ^ (-(49 : ℤ)) * (1 + ℓ * L) ^ 52 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have h4 : ℓ ^ 3 * L ^ 52 * (L ^ 52)⁻¹
      ≤ ℓ ^ (-(49 : ℤ)) * (1 + ℓ * L) ^ 52 * (L ^ 52)⁻¹ :=
    mul_le_mul_of_nonneg_right hkey (by positivity)
  rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero 52 (ne_of_gt hL)), mul_one] at h4
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + ℓ * L) ^ 52)]
  calc ℓ ^ 3 ≤ ℓ ^ (-(49 : ℤ)) * (1 + ℓ * L) ^ 52 * (L ^ 52)⁻¹ := h4
    _ = ℓ ^ (-(49 : ℤ)) * (L ^ 52)⁻¹ * (1 + ℓ * L) ^ 52 := by ring

/-- **The `ε₂`-profile bound** (given the four analytic inputs).  For the multiplier
`(1 − f_L)` with `f_L = lowMult fc κ ℓ`,

  `|(1 − f_L)(χ_ℓ²)(z)| ≤ CH·(κℓ)^{-49}`

in the dilute regime `κℓ ≥ 1`.  Fourier inversion writes `(1 − f_L)(χ_ℓ²)` as the inverse
transform of `(1 − f(‖p‖/κ))·kinFT(χ_ℓ²)`; the symbol vanishes for `‖p‖ ≤ κ`, and the
Schwartz decay of `kinFT(χ²)` (the `ℓ`-scaled bump) turns the tail `∫_{‖p‖ ≥ κ}` into
`(κℓ)^{-49}`. -/

theorem hRes_abs_le_of
    (hdec : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ3,
      ‖Submission.BoseGases.kinFT bumpSqC q‖ ≤ C / (1 + ‖q‖) ^ N)
    (htail : ∀ N : ℕ, 4 ≤ N → ∃ C : ℝ, 0 ≤ C ∧ ∀ κ : ℝ, 0 < κ →
      IntegrableOn (fun p : ℝ3 => ((‖p‖) ^ N)⁻¹) {q : ℝ3 | κ ≤ ‖q‖} volume ∧
      (∫ p in {q : ℝ3 | κ ≤ ‖q‖}, ((‖p‖) ^ N)⁻¹) ≤ C * κ ^ (3 - (N : ℤ)))
    (hscale : ∀ (ℓ : ℝ), 0 < ℓ → ∀ p : ℝ3,
      Submission.BoseGases.kinFT (fun y => (((Submission.BoseGases.chiU ℓ 0 y) ^ 2 : ℝ) : ℂ)) p
        = (ℓ : ℂ) ^ 3 * Submission.BoseGases.kinFT bumpSqC (ℓ • p)) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ),
      0 < κ → 0 < ℓ → 1 ≤ κ * ℓ →
      ∀ z : ℝ3, |hRes fc κ ℓ z| ≤ CH * (κ * ℓ) ^ (-(49 : ℤ)) := by
  classical
  obtain ⟨Cb, hCb0, hCb⟩ := hdec 52
  obtain ⟨Ct, hCt0, hCt⟩ := htail 52 (by norm_num)
  refine ⟨((2 * π) ^ 3)⁻¹ * (Cb * Ct), by positivity, ?_⟩
  intro fc κ ℓ hκ hℓ hκℓ z
  -- the cut-off is `1` below `κ` and `0` above `2κ`
  have hf_one : ∀ p : ℝ3, ‖p‖ ≤ κ → fc.f (‖p‖ / κ) = 1 := by
    intro p hp
    refine fc.one _ ?_
    rw [div_le_one hκ]
    exact hp
  have hf_le_one : ∀ p : ℝ3, fc.f (‖p‖ / κ) ≤ 1 := by
    intro p
    by_cases h : ‖p‖ / κ ≤ 1
    · rw [fc.one _ h]
    · exact le_trans (fc.anti (le_of_not_ge h)) (le_of_eq (fc.one 1 le_rfl))
  have hf_nonneg : ∀ p : ℝ3, 0 ≤ fc.f (‖p‖ / κ) := by
    intro p
    by_cases h : ‖p‖ / κ ≤ 2
    · have h2 := fc.anti h
      rwa [fc.zero 2 le_rfl] at h2
    · rw [fc.zero _ (le_of_not_ge h)]
  -- the transform `G = kinFT (χ_ℓ²)` and its properties
  set G : ℝ3 → ℂ := fun p => Submission.BoseGases.kinFT
      (fun y => (((Submission.BoseGases.acube ℓ).indicator
        (fun w => Submission.BoseGases.chiU ℓ 0 w ^ 2) y : ℝ) : ℂ)) p with hGdef
  have hG_eq : ∀ p : ℝ3, G p = (ℓ : ℂ) ^ 3 * Submission.BoseGases.kinFT bumpSqC (ℓ • p) := by
    intro p
    simp only [hGdef]
    rw [show (fun y => (((Submission.BoseGases.acube ℓ).indicator
          (fun w => Submission.BoseGases.chiU ℓ 0 w ^ 2) y : ℝ) : ℂ)) = indChiSq ℓ from rfl,
      indChiSq_eq_plain ℓ hℓ, hscale ℓ hℓ p]
  have hGint : Integrable G := by
    have hFint : Integrable (fun q : ℝ3 => (𝓕 Work.BoseFixB3.Scaling.phiSch) q) :=
      SchwartzMap.integrable _
    have hcomp1 : Integrable (fun q : ℝ3 =>
        (𝓕 Work.BoseFixB3.Scaling.phiSch) ((2 * π)⁻¹ • q)) :=
      hFint.comp_smul (by positivity)
    have hkin : Integrable (fun q : ℝ3 =>
        Submission.BoseGases.kinFT Work.BoseFixB3.Scaling.phiC q) := by
      refine hcomp1.congr ?_
      filter_upwards with q
      rw [Work.BoseFixB3.Scaling.kinFT_phiC_fourier]
    have hkin2 : Integrable (fun p : ℝ3 =>
        Submission.BoseGases.kinFT Work.BoseFixB3.Scaling.phiC (ℓ • p)) :=
      hkin.comp_smul (ne_of_gt hℓ)
    have hbump : Integrable (fun p : ℝ3 =>
        (ℓ : ℂ) ^ 3 * Submission.BoseGases.kinFT bumpSqC (ℓ • p)) := by
      have h := hkin2.const_mul ((ℓ : ℂ) ^ 3)
      simpa only [bumpSqC_eq_phiC] using h
    exact hbump.congr (Filter.Eventually.of_forall fun p => (hG_eq p).symm)
  -- the inverse-transform identity for the profile `χ_ℓ²`
  have hcubene : ((((2 * π) ^ 3 : ℝ)) : ℂ) ≠ 0 := by
    have h : ((2 * π) ^ 3 : ℝ) ≠ 0 := by positivity
    exact_mod_cast h
  have hInv : (((2 * π) ^ 3)⁻¹ : ℝ) * (∫ p : ℝ3,
      Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * G p).re
      = Submission.BoseGases.chiU ℓ 0 z ^ 2 := by
    have h := kinFT_inversion_indChiSq ℓ hℓ z
    have h2 : (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
          Submission.BoseGases.kinFT (indChiSq ℓ) p)
        = ∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * G p := by
      apply integral_congr_ae
      filter_upwards with p
      rfl
    rw [h2] at h
    have h3 : (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * G p)
        = (((2 * π) ^ 3 : ℝ) : ℂ) * ((Submission.BoseGases.chiU ℓ 0 z ^ 2 : ℝ) : ℂ) := by
      calc (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * G p)
          = (((2 * π) ^ 3 : ℝ) : ℂ) *
              (((((2 * π) ^ 3 : ℝ)) : ℂ)⁻¹ * (∫ p : ℝ3,
                Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * G p)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hcubene, one_mul]
        _ = (((2 * π) ^ 3 : ℝ) : ℂ) * ((Submission.BoseGases.chiU ℓ 0 z ^ 2 : ℝ) : ℂ) := by
            rw [h]
    have h4 := congrArg Complex.re h3
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero] at h4
    rw [h4]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : ((2 * π) ^ 3 : ℝ) ≠ 0), one_mul]
  have hInv' : (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * G p).re
      = ((2 * π) ^ 3 : ℝ) * Submission.BoseGases.chiU ℓ 0 z ^ 2 := by
    have hpos : (0 : ℝ) < (2 * π) ^ 3 := by positivity
    calc (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * G p).re
        = ((2 * π) ^ 3) * ((((2 * π) ^ 3)⁻¹ : ℝ) *
            (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * G p).re) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
      _ = ((2 * π) ^ 3) * Submission.BoseGases.chiU ℓ 0 z ^ 2 := by rw [hInv]
  -- the multiplier identity
  have hAint : Integrable (fun p : ℝ3 => Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * G p) := by
    refine hGint.bdd_mul (c := 1)
      ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable) ?_
    filter_upwards with p
    exact le_of_eq (Complex.norm_exp_I_mul_ofReal _)
  have hBint : Integrable (fun p : ℝ3 => Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
      (((fc.f (‖p‖ / κ) : ℝ)) : ℂ) * G p) := by
    have hf_meas : AEStronglyMeasurable (fun p : ℝ3 =>
        Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
          (((fc.f (‖p‖ / κ) : ℝ)) : ℂ)) :=
      (((Complex.continuous_exp.comp (by fun_prop)).mul
        (Complex.continuous_ofReal.comp
          (fc.smooth.continuous.comp (by fun_prop))))).aestronglyMeasurable
    refine hGint.bdd_mul (c := 1) hf_meas ?_
    filter_upwards with p
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
      show ‖((((fc.f (‖p‖ / κ) : ℝ)) : ℂ))‖ = |fc.f (‖p‖ / κ)| from RCLike.norm_ofReal _,
      abs_of_nonneg (hf_nonneg p)]
    exact hf_le_one p
  have hLow : Work.BoseBoxFix.lowMult fc κ ℓ
      (fun w => Submission.BoseGases.chiU ℓ 0 w ^ 2) z
      = (((2 * π) ^ 3)⁻¹ : ℝ) * (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
          (((fc.f (‖p‖ / κ) : ℝ)) : ℂ) * G p).re := by
    simp only [Work.BoseBoxFix.lowMult, hGdef, indChiSq]
    rw [Complex.re_ofReal_mul]
  have hid : hRes fc κ ℓ z = (((2 * π) ^ 3)⁻¹ : ℝ) *
      (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
        (((1 - fc.f (‖p‖ / κ) : ℝ)) : ℂ) * G p).re := by
    have hsub := integral_sub hAint hBint
    have hdiff : (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
        (((1 - fc.f (‖p‖ / κ) : ℝ)) : ℂ) * G p)
        = (∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * G p)
          - ∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
              (((fc.f (‖p‖ / κ) : ℝ)) : ℂ) * G p := by
      rw [← hsub]
      apply integral_congr_ae
      filter_upwards with p
      push_cast
      ring
    rw [hRes, hLow, hdiff, Complex.sub_re, hInv', mul_sub, ← mul_assoc,
      inv_mul_cancel₀ (by positivity : ((2 * π) ^ 3 : ℝ) ≠ 0), one_mul]
  -- the pointwise bound on the integrand
  have hpoint : ∀ p : ℝ3, ‖Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
        (((1 - fc.f (‖p‖ / κ) : ℝ)) : ℂ) * G p‖
      ≤ Cb * ℓ ^ (-(49 : ℤ)) * ({q : ℝ3 | κ ≤ ‖q‖}).indicator (fun p => (‖p‖ ^ 52)⁻¹) p := by
    intro p
    by_cases hp : κ ≤ ‖p‖
    · rw [Set.indicator_of_mem (show p ∈ {q : ℝ3 | κ ≤ ‖q‖} from hp)]
      rw [norm_mul, norm_mul, show ‖Complex.exp (Complex.I * (inner ℝ p z : ℂ))‖ = 1 from
        Complex.norm_exp_I_mul_ofReal _, one_mul,
        show ‖((((1 - fc.f (‖p‖ / κ) : ℝ)) : ℂ))‖ = |1 - fc.f (‖p‖ / κ)| from
          RCLike.norm_ofReal _]
      have h1 : |1 - fc.f (‖p‖ / κ)| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [hf_le_one p], by linarith [hf_nonneg p]⟩
      have hnormℓ : ‖(ℓ : ℂ)‖ = ℓ := by
        rw [show ‖(ℓ : ℂ)‖ = |ℓ| from RCLike.norm_ofReal ℓ, abs_of_nonneg hℓ.le]
      have h2 : ‖G p‖ ≤ Cb * ℓ ^ 3 / (1 + ℓ * ‖p‖) ^ 52 := by
        rw [hG_eq p, norm_mul, norm_pow, hnormℓ]
        have h := hCb (ℓ • p)
        rw [norm_smul, Real.norm_of_nonneg hℓ.le] at h
        calc ℓ ^ 3 * ‖Submission.BoseGases.kinFT bumpSqC (ℓ • p)‖
            ≤ ℓ ^ 3 * (Cb / (1 + ℓ * ‖p‖) ^ 52) :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = Cb * ℓ ^ 3 / (1 + ℓ * ‖p‖) ^ 52 := by ring
      have hstep : ℓ ^ 3 / (1 + ℓ * ‖p‖) ^ 52 ≤ ℓ ^ (-(49 : ℤ)) * (‖p‖ ^ 52)⁻¹ :=
        div_pow_le_zpow hℓ (lt_of_lt_of_le hκ hp) (by
          calc (1 : ℝ) ≤ κ * ℓ := hκℓ
            _ ≤ ‖p‖ * ℓ := mul_le_mul_of_nonneg_right hp hℓ.le
            _ = ℓ * ‖p‖ := by ring)
      calc |1 - fc.f (‖p‖ / κ)| * ‖G p‖
          ≤ 1 * (Cb * ℓ ^ 3 / (1 + ℓ * ‖p‖) ^ 52) :=
            mul_le_mul h1 h2 (by positivity) (by norm_num)
        _ = Cb * (ℓ ^ 3 / (1 + ℓ * ‖p‖) ^ 52) := by ring
        _ ≤ Cb * (ℓ ^ (-(49 : ℤ)) * (‖p‖ ^ 52)⁻¹) :=
            mul_le_mul_of_nonneg_left hstep hCb0
        _ = Cb * ℓ ^ (-(49 : ℤ)) * (‖p‖ ^ 52)⁻¹ := by ring
    · rw [Set.indicator_of_notMem (show p ∉ {q : ℝ3 | κ ≤ ‖q‖} from hp)]
      have h1 : fc.f (‖p‖ / κ) = 1 := hf_one p (le_of_not_ge hp)
      rw [h1, sub_self]
      simp
  -- assemble
  obtain ⟨hTailInt, hTailBd⟩ := hCt κ hκ
  have hsmeas : MeasurableSet {q : ℝ3 | κ ≤ ‖q‖} :=
    measurableSet_le measurable_const measurable_norm
  have hbase : Integrable (({q : ℝ3 | κ ≤ ‖q‖}).indicator (fun p : ℝ3 => (‖p‖ ^ 52)⁻¹)) := by
    rw [integrable_indicator_iff hsmeas]
    exact hTailInt
  have hcore : (((2 * π) ^ 3)⁻¹ : ℝ) * (∫ p : ℝ3,
        ‖Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
          (((1 - fc.f (‖p‖ / κ) : ℝ)) : ℂ) * G p‖)
      ≤ (((2 * π) ^ 3)⁻¹ : ℝ) * (Cb * ℓ ^ (-(49 : ℤ))) *
          (∫ p in {q : ℝ3 | κ ≤ ‖q‖}, (‖p‖ ^ 52)⁻¹) := by
    have hmono := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun p => norm_nonneg _) (hbase.const_mul _)
      (Filter.Eventually.of_forall fun p => hpoint p)
    have hconst : (∫ p : ℝ3, Cb * ℓ ^ (-(49 : ℤ)) *
          ({q : ℝ3 | κ ≤ ‖q‖}).indicator (fun p : ℝ3 => (‖p‖ ^ 52)⁻¹) p)
        = Cb * ℓ ^ (-(49 : ℤ)) * (∫ p : ℝ3,
            ({q : ℝ3 | κ ≤ ‖q‖}).indicator (fun p : ℝ3 => (‖p‖ ^ 52)⁻¹) p) :=
      integral_const_mul (Cb * ℓ ^ (-(49 : ℤ))) _
    rw [hconst, integral_indicator hsmeas] at hmono
    have hfin := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ ((2 * π) ^ 3)⁻¹)
    calc (((2 * π) ^ 3)⁻¹ : ℝ) * (∫ p : ℝ3,
          ‖Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
            (((1 - fc.f (‖p‖ / κ) : ℝ)) : ℂ) * G p‖)
        ≤ ((2 * π) ^ 3)⁻¹ * (Cb * ℓ ^ (-(49 : ℤ)) *
            (∫ p in {q : ℝ3 | κ ≤ ‖q‖}, (‖p‖ ^ 52)⁻¹)) := hfin
      _ = (((2 * π) ^ 3)⁻¹ : ℝ) * (Cb * ℓ ^ (-(49 : ℤ))) *
            (∫ p in {q : ℝ3 | κ ≤ ‖q‖}, (‖p‖ ^ 52)⁻¹) := by ring
  have hchain : |hRes fc κ ℓ z|
      ≤ (((2 * π) ^ 3)⁻¹ : ℝ) * (Cb * ℓ ^ (-(49 : ℤ))) *
          (∫ p in {q : ℝ3 | κ ≤ ‖q‖}, (‖p‖ ^ 52)⁻¹) := by
    rw [hid, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * π) ^ 3)⁻¹)]
    calc (((2 * π) ^ 3)⁻¹ : ℝ) * |(∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
            (((1 - fc.f (‖p‖ / κ) : ℝ)) : ℂ) * G p).re|
        ≤ (((2 * π) ^ 3)⁻¹ : ℝ) * ‖∫ p : ℝ3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
              (((1 - fc.f (‖p‖ / κ) : ℝ)) : ℂ) * G p‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
      _ ≤ (((2 * π) ^ 3)⁻¹ : ℝ) * (∫ p : ℝ3,
            ‖Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
              (((1 - fc.f (‖p‖ / κ) : ℝ)) : ℂ) * G p‖) :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
      _ ≤ (((2 * π) ^ 3)⁻¹ : ℝ) * (Cb * ℓ ^ (-(49 : ℤ))) *
            (∫ p in {q : ℝ3 | κ ≤ ‖q‖}, (‖p‖ ^ 52)⁻¹) := hcore
  have hchain2 : (((2 * π) ^ 3)⁻¹ : ℝ) * (Cb * ℓ ^ (-(49 : ℤ))) *
      (∫ p in {q : ℝ3 | κ ≤ ‖q‖}, (‖p‖ ^ 52)⁻¹)
      ≤ (((2 * π) ^ 3)⁻¹ : ℝ) * (Cb * Ct) * (κ * ℓ) ^ (-(49 : ℤ)) := by
    have h1 : (((2 * π) ^ 3)⁻¹ : ℝ) * (Cb * ℓ ^ (-(49 : ℤ))) *
        (∫ p in {q : ℝ3 | κ ≤ ‖q‖}, (‖p‖ ^ 52)⁻¹)
        ≤ (((2 * π) ^ 3)⁻¹ : ℝ) * (Cb * ℓ ^ (-(49 : ℤ))) * (Ct * κ ^ (3 - (52 : ℤ))) :=
      mul_le_mul_of_nonneg_left hTailBd
        (mul_nonneg (by positivity) (mul_nonneg hCb0 (zpow_nonneg hℓ.le _)))
    have h2 : (((2 * π) ^ 3)⁻¹ : ℝ) * (Cb * ℓ ^ (-(49 : ℤ))) * (Ct * κ ^ (3 - (52 : ℤ)))
        = (((2 * π) ^ 3)⁻¹ : ℝ) * (Cb * Ct) * (κ * ℓ) ^ (-(49 : ℤ)) := by
      rw [show (3 : ℤ) - 52 = -(49 : ℤ) by norm_num, mul_zpow]
      field_simp
    rw [h2] at h1
    exact h1
  linarith [hchain, hchain2]

/-- **FS's `ε₂`-smallness of the localisation residual.**  There is a universal constant `CH`
with: in the dilute regime `κℓ ≥ 1`, the one-body profile `(1 − f_L)(χ_ℓ²) = hRes fc κ ℓ`
is bounded by `CH·(κℓ)^{-49}` uniformly. -/
theorem hRes_abs_le :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ),
      0 < κ → 0 < ℓ → 1 ≤ κ * ℓ →
      ∀ z : EuclideanSpace ℝ (Fin 3), |hRes fc κ ℓ z| ≤ CH * (κ * ℓ) ^ (-(49 : ℤ)) :=
  hRes_abs_le_of kinFT_bumpSq_decay tail_zpow_integral kinFT_chiU_sq_scaling

end Work.BoseFixB3.Eps
