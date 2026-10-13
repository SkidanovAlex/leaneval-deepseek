/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary layer for the honest `w²`-weighted energy inequality

This module collects the elementary facts shared by
`Work.FTS.EllipticEst.Honest.HonEnergyExpl` and by the auxiliary lemmas its proof dispatches:

* the elementary bounds on the radial weight `w z = (1+z)²/z²` and the angular weight
  `σ θ = sin(2θ)^{-η}` (`one_le_w_sq`, `one_le_sEta`, `sEta_integrableOn`, ...);
* the pointwise form `HkIntegrand_zero_eq'` of the level-`0` `Hk`-integrand as a product
  `w(z)² · (g² σ)`;
* the *slicewise* integrability that the honesty conditions `memA`, `memB`, `memF` of the class
  `Hon` provide: for every `z > 0` the `θ`-slices of `∂_θθΨ`, `z²∂_zzΨ` and `F` are square
  integrable against `σ`, and (because `σ ≥ 1` on `(0,π/2)`) also plain square integrable;
* an a.e.-strong-measurability transfer `slice_aesm_of_contDiffOn` for slices that are smooth on
  the *open* interval, which is what turns the `σ`-weighted integrability into unweighted
  integrability.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.weight_algebra_fts
import Submission.Work.FTS.EllipticEst.RadialEnergyDefs
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## Elementary bounds on the two weights -/

/-- `1 ≤ (w z)²` for `z > 0`. -/
theorem one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have hz' : (1 : ℝ) ≤ (1 + z) / z := by
    rw [le_div_iff₀ hz]; linarith
  have hw : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by rw [Work.Spaces.w, div_pow]
  rw [hw]
  exact one_le_pow₀ (one_le_pow₀ hz')

/-- `w z ≠ 0` for `z > 0`. -/
theorem w_ne_zero {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  have h : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by rw [Work.Spaces.w, div_pow]
  rw [h]
  exact pow_ne_zero 2 (div_ne_zero (by linarith) (ne_of_gt hz))

/-- `1 ≤ σ θ` on the open interval. -/
theorem one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ :=
  Work.FTS.EllipticEst.sliceLim_one_le_sEta hθ

/-- `0 ≤ σ θ` on `Iθ`. -/
theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- `σ` is integrable on `Iθ` (the `p = -η` case of `sin_two_rpow`). -/
theorem sEta_integrableOn :
    IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
  (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
    (by norm_num [Work.Spaces.eta])).1

/-- `∫_θ σ θ ≤ 10000`. -/
theorem sEta_integral_le :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) ≤ 10000 := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
    (by norm_num [Work.Spaces.eta])).2
  have h1 : -(Work.Spaces.eta) + 1 = 1 / 100 := by norm_num [Work.Spaces.eta]
  rw [h1] at h
  have key : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
      = ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) :=
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => rfl)
  rw [key]
  linarith [h]

/-- `volume.restrict Iθ = volume.restrict (0,π/2)`: the two endpoints are a null set. -/
theorem restrict_Iθ_eq_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm

/-- A function smooth on `(0,π/2)` is a.e. strongly measurable for the measure of `Iθ`. -/
theorem slice_aesm_of_contDiffOn {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_Ioo]
  exact hu.continuousOn.aestronglyMeasurable measurableSet_Ioo

/-! ## The level-`0` integrand in product form -/

/-- **The level-`0` `Hk`-integrand as a product**: on `Iθ`,
`HkIntegrand α 0 g z θ = w(z)² · (g z θ² · σ θ)`. -/
theorem HkIntegrand_zero_eq' {α : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (g : ℝ → ℝ → ℝ)
    (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [HkIntegrand_zero_eq, sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ),
    Work.FTS.EllipticEst.sEta]
  ring

/-- The same identity almost everywhere on `Iθ`. -/
theorem HkIntegrand_zero_eq_ae (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (fun θ => Work.Spaces.HkIntegrand α 0 g z θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  rw [Filter.EventuallyEq, Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards with θ hθ
  exact HkIntegrand_zero_eq' hθ g z

/-! ## Slicewise integrability provided by the honesty of the class -/

/-- **The `θ`-slice of `∂_θθΨ` is `σ`-square integrable**, for every `z > 0`: this is the first
component of `memB`. -/
theorem hon_memB_sigma {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have h2 := (h.memB.1 z (le_of_lt hz)).congr
    (HkIntegrand_zero_eq_ae α (Work.Spaces.pthIter 2 Ψ) z)
  have h4 := h2.const_mul (1 / (Work.Spaces.w z) ^ 2)
  have h3 : (fun θ => (1 / (Work.Spaces.w z) ^ 2)
        * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)))
      = fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    funext θ
    rw [← mul_assoc, one_div, inv_mul_cancel₀ (pow_ne_zero 2 (w_ne_zero hz)), one_mul]
  rw [h3] at h4
  exact h4

/-- **The `θ`-slice of `∂_zzΨ` is `σ`-square integrable**, for every `z > 0`: this is the first
component of `memA` (recall `HkIntegrand α 0 (z²∂_zzΨ) = w(z)² z⁴ (∂_zzΨ)² σ`). -/
theorem hon_memA_sigma {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have h2 := (h.memA.1 z (le_of_lt hz)).congr
    (HkIntegrand_zero_eq_ae α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z)
  have h4 := h2.const_mul (1 / ((Work.Spaces.w z) ^ 2 * z ^ 4))
  have h3 : (fun θ => (1 / ((Work.Spaces.w z) ^ 2 * z ^ 4))
        * ((Work.Spaces.w z) ^ 2
            * (((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      = fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    funext θ
    have hw : Work.Spaces.w z ≠ 0 := w_ne_zero hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    field_simp
  rw [h3] at h4
  exact h4

/-- **The `θ`-slice of `F` is `σ`-square integrable**, for every `z > 0`: this is the first component
of `memF`. -/
theorem hon_memF_sigma {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have h2 := (h.memF.1 z (le_of_lt hz)).congr (HkIntegrand_zero_eq_ae α F z)
  have h4 := h2.const_mul (1 / (Work.Spaces.w z) ^ 2)
  have h3 : (fun θ => (1 / (Work.Spaces.w z) ^ 2)
        * ((Work.Spaces.w z) ^ 2 * ((F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      = fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    funext θ
    rw [← mul_assoc, one_div, inv_mul_cancel₀ (pow_ne_zero 2 (w_ne_zero hz)), one_mul]
  rw [h3] at h4
  exact h4

/-- **Unweighted transfer**: a slice that is a.e. strongly measurable and `σ`-square integrable is
square integrable (because `σ ≥ 1` a.e. on `Iθ`). -/
theorem integrableOn_sq_of_sigma {g : ℝ → ℝ}
    (haesm : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ))
    (h : IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ := by
  refine Integrable.mono' (μ := volume.restrict Work.Spaces.Iθ) h (haesm.pow 2) ?_
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  have h0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  have h1 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]; simp
  filter_upwards [h0, h1] with θ hθ0 hθ1 hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hioo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθ1⟩
  have hs : (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta hioo
  nlinarith [hs, sq_nonneg (g θ)]

end Work.FTS.EllipticEst.Honest
