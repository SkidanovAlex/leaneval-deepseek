/-
# Uniform bounds for the angular jet of `Γ`

This module proves `Work.FTS.StrongPersist.L3Aux.GamJetBounds`: a single constant `K` bounds,
uniformly over `α ∈ (0,1]`,

* the angular jet `D_θ^i Γ` of `Γ(θ) = (sin θ cos²θ)^{α/3}` on `Iθ`, for `i ≤ 4`;
* the weighted angular mass `∫_{Iθ} (Γ/c)² sin(2θ)^{-η}`;
* the weighted angular masses `∫_{Iθ} (D_θ^i (Γ/c))² sin(2θ)^{-γ(α)}`, `1 ≤ i ≤ 4`,
  where `c = c(α) = ∫_{Iθ} ΓK` is the normalisation constant of the paper and
  `γ(α) = 1 + α/10`.

## Route

* **Jet bound.**  `Work.FTS.LocData.DthIter_Gam_abs_le` gives the pointwise bound
  `|D_θ^i Γ| ≤ 10⁵ · Γ` for `i ≤ 4`, and `Γ ≤ 1` on `Iθ` (`Work.Spaces.Gam_bounds`), so
  `|D_θ^i Γ| ≤ 10⁵` there.

* **`η`-mass.**  On `Iθ` one has `(Γ/c)² ≤ 100` (since `Γ ≤ 1` and `1/10 ≤ c ≤ 10`,
  `Work.Spaces.c_bounds`), so the integrand is dominated by `100 · sin(2θ)^{-η}`, whose
  integral over `Iθ` is at most `100/(1-η) = 10000` (`Work.Spaces.sin_two_rpow`).

* **`γ`-mass.**  Here the crude bound is not enough, because `∫ sin(2θ)^{-γ} = ∞`
  (`γ > 1`); the vanishing of `Γ` at the endpoints is essential.  We use the *quantitative*
  jet bound with the factor `α`,
  `|D_θ^i (Γ/c)| ≤ α · 10⁵ · (Γ/c)` (from `Work.Spaces.dthU_iter_Gam_abs_bound` and
  `Work.FTS.LocData.Tfun_abs_le`), and the pointwise comparison
  `Γ² sin(2θ)^{-γ} ≤ 2^{-2α/3} sin(2θ)^{17α/30-1}` (`Work.FTS.LocData.GamSq_sin_neg_gam_le`).
  Hence the integrand is dominated by `α² 10¹² sin(2θ)^{17α/30-1}`, whose integral over `Iθ`
  is at most `α² 10¹² · 3000/(17α) = 10¹²·3000α/17 ≤ 10¹²·3000/17 ≤ 10¹⁵`.

All constants are generous; only existence matters for the statement.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Gam_jet_upper_zero
import Submission.Work.Coercivity.Gam_jet_upper_pi
import Submission.Work.Coercivity.DthU_iter_Gam_all
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.integral_sin_rpow
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.LocData.angMaj_mem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false

/-! ## Elementary consequences of `Γ ≤ 1` and `1/10 ≤ c ≤ 10` -/

/-- On `Iθ`, `(Γ/c)² ≤ 100` for `0 < α ≤ 1`. -/
private lemma gamCoef_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 100 := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hdiv : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hcpos]
    nlinarith
  have hdiv0 : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α := div_nonneg hG0 hcpos.le
  nlinarith [hdiv, hdiv0]

/-- On `Iθ`, `(Γ/c)² ≤ 100 Γ²` for `0 < α ≤ 1` (used to exploit the vanishing of `Γ`). -/
private lemma gamCoef_sq_le_gamSq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 100 * Work.Spaces.Gam α θ ^ 2 := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hinv : (Work.Spaces.c α)⁻¹ ≤ 10 := by
    rw [inv_le_iff_one_le_mul₀ hcpos]
    linarith
  have h2 : ((Work.Spaces.c α)⁻¹) ^ 2 ≤ 100 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr hcpos.le) hinv 2
    nlinarith [h]
  rw [div_eq_mul_inv, mul_pow]
  have hG2 : 0 ≤ Work.Spaces.Gam α θ ^ 2 := sq_nonneg _
  calc Work.Spaces.Gam α θ ^ 2 * (Work.Spaces.c α)⁻¹ ^ 2
      ≤ Work.Spaces.Gam α θ ^ 2 * 100 := mul_le_mul_of_nonneg_left h2 hG2
    _ = 100 * Work.Spaces.Gam α θ ^ 2 := by ring

/-! ## The quantitative jet bound for `Γ/c` -/

/-- **Jet bound with the factor `α`.**  For `1 ≤ i ≤ 4` and `θ ∈ Iθ`,
`|D_θ^i (Γ/c)| ≤ α · 10⁵ · (Γ/c)`.

The factor `α` is what makes the subsequent `∫ (D_θ^i(Γ/c))² sin(2θ)^{-γ}` estimate
uniform in `α`: near `θ = 0` the jet vanishes like `Γ ∼ θ^{α/3}`, and the extra `α` exactly
compensates the `1/α` in `∫ sin(2θ)^{17α/30-1} = 3000/(17α)`. -/
private lemma gamCoef_jet_le (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ 4) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ|
      ≤ α * 100000 * (Work.Spaces.Gam α θ / Work.Spaces.c α) := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  rw [Work.FTS.LocData.DthIter_rad_eq]
  rw [show (fun t : ℝ => Work.Spaces.Gam α t / Work.Spaces.c α)
      = (fun t : ℝ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α t) from by
    funext t; rw [div_eq_inv_mul]]
  rw [Work.Spaces.dthU_iter_const_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hcpos.le)]
  have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i hi1 α hα 100000
    (fun θ' _ => Work.FTS.LocData.Tfun_abs_le (i - 1) (by omega) α hα hα1 θ')
  have hb := hkey θ hθ
  have h1 : (Work.Spaces.c α)⁻¹ * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (Work.Spaces.c α)⁻¹ * (α * 100000 * Work.Spaces.Gam α θ) :=
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hcpos.le)
  have h2 : (Work.Spaces.c α)⁻¹ * (α * 100000 * Work.Spaces.Gam α θ)
      = α * 100000 * (Work.Spaces.Gam α θ / Work.Spaces.c α) := by
    rw [div_eq_mul_inv]; ring
  exact h1.trans (le_of_eq h2)

/-! ## Measurability of the jet (needed for `IntegrableOn`) -/

/-- `dthU^[m] g` is Borel measurable for every `m ≥ 1`, with no hypothesis on `g`
(and for `m = 0` when `g` is measurable): `dthU` multiplies `deriv` by `sin(2·)`, and
`measurable_deriv` is unconditional. -/
private lemma measurable_dthU_iter (g : ℝ → ℝ) (hg : Measurable g) (m : ℕ) :
    Measurable (Work.Spaces.dthU^[m] g) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      show Measurable (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[m] g) θ)
      exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id))).mul
        (measurable_deriv _)

/-- The angular jet of `Γ/c`, as a function of `θ`, is Borel measurable. -/
private lemma measurable_gamCoef_jet (i : ℕ) (α : ℝ) :
    Measurable (fun θ => Work.Spaces.DthIter i
      (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) := by
  have hfun : (fun θ => Work.Spaces.DthIter i
        (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ)
      = fun θ => (Work.Spaces.c α)⁻¹ * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ := by
    funext θ
    rw [Work.FTS.LocData.DthIter_rad_eq]
    rw [show (fun t : ℝ => Work.Spaces.Gam α t / Work.Spaces.c α)
        = (fun t : ℝ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α t) from by
      funext t; rw [div_eq_inv_mul]]
    rw [Work.Spaces.dthU_iter_const_mul]
  rw [hfun]
  exact measurable_const.mul (measurable_dthU_iter _ (by simp only [Work.Spaces.Gam]; fun_prop) i)

/-! ## The pointwise domination of the `γ`-weighted jet -/

/-- **Pointwise domination.**  On `Iθ`, for `1 ≤ i ≤ 4`,

`(D_θ^i (Γ/c))² sin(2θ)^{-γ(α)} ≤ α² · 10¹² · sin(2θ)^{17α/30-1}`,

and the exponent `17α/30 - 1 = 2α/3 - γ(α)` satisfies `-1 < 17α/30 - 1 ≤ 0`. -/
private lemma gamCoef_gam_pt_le (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ 4) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hX0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  have hXg : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hX0 _
  have hXp : 0 ≤ (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := Real.rpow_nonneg hX0 _
  have hjet := gamCoef_jet_le i hi1 hi α hα hα1 hθ
  have hD2 : (Work.Spaces.DthIter i
        (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
      ≤ (α * 100000) ^ 2 * (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 := by
    rw [← sq_abs]
    have h := pow_le_pow_left₀ (abs_nonneg _) hjet 2
    rwa [mul_pow] at h
  have hcx := gamCoef_sq_le_gamSq α hα hα1 hθ
  have hgs := Work.FTS.LocData.GamSq_sin_neg_gam_le α hα hα1 hθ
  have hstep1 : (Work.Spaces.DthIter i
        (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_right hD2 hXg
  have hstep2 : ((α * 100000) ^ 2 * (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (100 * Work.Spaces.Gam α θ ^ 2))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    apply mul_le_mul_of_nonneg_right _ hXg
    exact mul_le_mul_of_nonneg_left hcx (by positivity)
  have hstep4 : (α * 100000) ^ 2 * 100 * (Work.Spaces.Gam α θ ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (α * 100000) ^ 2 * 100 * (2 ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) :=
    mul_le_mul_of_nonneg_left hgs (by positivity)
  have hbc : (α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3)) ≤ α ^ 2 * 10 ^ 12 := by
    have h2 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -(2 * α / 3) ≤ 0)
    calc (α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3))
        ≤ (α * 100000) ^ 2 * 100 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = α ^ 2 * 10 ^ 12 := by ring
  calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hstep1
    _ ≤ ((α * 100000) ^ 2 * (100 * Work.Spaces.Gam α θ ^ 2))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hstep2
    _ = (α * 100000) ^ 2 * 100 * (Work.Spaces.Gam α θ ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ ≤ (α * 100000) ^ 2 * 100 * (2 ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := hstep4
    _ = ((α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3)))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by ring
    _ ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) :=
        mul_le_mul_of_nonneg_right hbc hXp

/-! ## The two angular mass estimates -/

/-- **The `η`-weighted mass of `Γ/c`.**  `∫_{Iθ} (Γ/c)² sin(2θ)^{-η} ≤ 10⁶` for `0 < α ≤ 1`. -/
private lemma gamCoef_eta_integral_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 1000000 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsin2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  have hη1 : -1 < -(Work.Spaces.eta) := by simp only [Work.Spaces.eta]; norm_num
  have hη0 : -(Work.Spaces.eta) ≤ 0 := by simp only [Work.Spaces.eta]; norm_num
  obtain ⟨hInt, hBd⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hη1 hη0
  have hBd' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10000 := by
    have heq : 100 / (-(Work.Spaces.eta) + 1) = 10000 := by
      simp only [Work.Spaces.eta]; norm_num
    rwa [heq] at hBd
  have h100 : MeasureTheory.IntegrableOn
      (fun θ => 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    hInt.const_mul 100
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    have hX : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_nonneg (hsin2 θ hθ) _
    have h2 := gamCoef_sq_le α hα hα1 hθ
    nlinarith [h2, hX]
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  have hIntf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    h100.mono' hmeas (by
      filter_upwards [hpt, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2 θ h2) _))]
      exact h1)
  refine ⟨hIntf, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hIntf h100 hpt
  calc ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ ∫ θ in Work.Spaces.Iθ, 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := hmono
    _ = 100 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ 100 * 10000 := by linarith [hBd']
    _ = 1000000 := by norm_num

/-- **The `γ`-weighted mass of the jet of `Γ/c`.**  For `1 ≤ i ≤ 4` and `0 < α ≤ 1`,

`∫_{Iθ} (D_θ^i (Γ/c))² sin(2θ)^{-γ(α)} ≤ 10¹⁵`. -/
private lemma gamCoef_gam_integral_le (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ 4) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DthIter i
          (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DthIter i
          (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 10 ^ 15 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsin2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  have hp1 : -1 < 17 * α / 30 - 1 := by linarith
  have hp2 : 17 * α / 30 - 1 ≤ 0 := by linarith
  obtain ⟨hIntS, hBdS⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1) hp1 hp2
  have hBdS' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by field_simp; ring
    rwa [heq] at hBdS
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
      Work.Spaces.Iθ := hIntS.const_mul _
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact gamCoef_gam_pt_le i hi1 hi α hα hα1 hθ
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.DthIter i
          (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) := by
    have hD := measurable_gamCoef_jet i α
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.gam]
    fun_prop
  have hIntf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DthIter i
          (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    hdom.mono' hmeas (by
      filter_upwards [hpt, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2 θ h2) _))]
      exact h1)
  refine ⟨hIntf, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hIntf hdom hpt
  calc ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DthIter i
        (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ∫ θ in Work.Spaces.Iθ,
          α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := hmono
    _ = α ^ 2 * 10 ^ 12
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ α ^ 2 * 10 ^ 12 * (3000 / (17 * α)) :=
        mul_le_mul_of_nonneg_left hBdS' (by positivity)
    _ = 10 ^ 12 * 3000 * α / 17 := by field_simp
    _ ≤ 10 ^ 15 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 17)]
        nlinarith [hα1]

/-! ## The target -/

theorem GamJetBounds : ∃ K : ℝ, 0 < K ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ i ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ => Work.Spaces.Gam α θ) 0 θ| ≤ K) ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ K) ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DthIter i
            (fun _ θ => Work.Spaces.Gam α θ / Work.Spaces.c α) 0 θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DthIter i
            (fun _ θ => Work.Spaces.Gam α θ / Work.Spaces.c α) 0 θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ K) := by
  refine ⟨10 ^ 15, by norm_num, ?_, ?_, ?_⟩
  · intro α hα hα1 i hi θ hθ
    have hkey := Work.FTS.LocData.DthIter_Gam_abs_le i hi α hα hα1 hθ
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    nlinarith [hkey, hG1, hG0]
  · intro α hα hα1
    obtain ⟨h1, h2⟩ := gamCoef_eta_integral_le α hα hα1
    exact ⟨h1, h2.trans (by norm_num)⟩
  · intro α hα hα1 i hi1 hi
    exact gamCoef_gam_integral_le i hi1 hi α hα hα1

end Work.FTS.StrongPersist.L3Aux
