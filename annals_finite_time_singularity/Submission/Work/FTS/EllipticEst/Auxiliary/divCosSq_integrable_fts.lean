/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of `z ↦ ψ(z) · ∫_θ (Ψ z θ / cos θ)²` on `[0,∞)`

The angular integrand `(Ψ z θ / cos θ)²` blows up at `θ = π/2` unless `Ψ z θ` vanishes there
to first order; the hypothesis `Ψ z (π/2) = 0` (together with smoothness of `Ψ` on a
neighbourhood of the closed quadrant) makes it bounded on the box `[0,R] × [0,π/2]`
(`Work.FTS.EllipticEst.Auxiliary.exists_bound_divCos_box`).  A compactly supported continuous
factor `ψ` (continuous on `[0,R]`, vanishing for `z ≥ R`) therefore makes the product
integrable on `Iz = [0,∞)`.

The three inputs (the box bound, the a.e. strong measurability of the slice integral, and the
extension from `[0,R]` to `[0,∞)` for functions vanishing past `R`) are proved in the sibling
files `exists_bound_divCos_box`, `aesm_integral_divCosSq_Ico` and
`integrableOn_Iz_of_support_Icc` of the same directory.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Auxiliary.exists_bound_divCos_box
import Submission.Work.FTS.EllipticEst.Auxiliary.aesm_integral_divCosSq_Ico
import Submission.Work.FTS.EllipticEst.Auxiliary.integrableOn_Iz_of_support_Icc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Auxiliary

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **Integrability of `z ↦ ψ z · ∫_θ (Ψ z θ / cos θ)²` on `Iz = [0,∞)`.**

`Ψ` is smooth on a neighbourhood of the closed quadrant and vanishes at `θ = π/2` for every
`z`, so that `(Ψ z θ / cos θ)²` is bounded on the box `[0,R] × [0,π/2]`; `ψ` is continuous on
`[0,R]` and vanishes for `z ≥ R`.  Hence the product — which is supported in `[0,R]` — is
integrable on `[0,∞)`. -/
theorem divCosSq_integrable_fts (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) (h1 : ∀ z, Ψ z (Real.pi / 2) = 0) (ψ : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) (hψc : ContinuousOn ψ (Set.Icc 0 R)) (hψ0 : ∀ z, R ≤ z → ψ z = 0) : MeasureTheory.IntegrableOn (fun z => ψ z * ∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2) Work.Spaces.Iz := by
  -- the uniform bound on the box and the resulting bound on the angular slice integral
  obtain ⟨C, hC0, hCbd, hCint⟩ := exists_bound_divCos_box Ψ hsm h1 hR
  -- a bound for the compactly supported factor `ψ`
  obtain ⟨S₀, hS₀⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hψc
  set S : ℝ := max S₀ 0 with hSdef
  have hSnn : 0 ≤ S := le_max_right _ _
  have hSbd : ∀ z ∈ Set.Icc 0 R, |ψ z| ≤ S := by
    intro z hz
    rw [← Real.norm_eq_abs]
    exact le_trans (hS₀ z hz) (le_max_left _ _)
  -- the a.e. strong measurability of the angular slice integral
  have hswap : (fun z => ∫ θ in Set.Ico 0 (Real.pi / 2), (Ψ z θ / Real.cos θ) ^ 2)
      = fun z => ∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 := by
    funext z
    show (∫ θ in Set.Ico 0 (Real.pi / 2), (Ψ z θ / Real.cos θ) ^ 2)
      = ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), (Ψ z θ / Real.cos θ) ^ 2
    rw [Measure.restrict_congr_set
      (MeasureTheory.Ico_ae_eq_Icc (μ := (volume : Measure ℝ)))]
  have hAESM : AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2)
      (volume.restrict (Set.Icc 0 R)) := by
    rw [← hswap]
    exact aesm_integral_divCosSq_Ico Ψ hsm R
  have hAESM_prod : AEStronglyMeasurable
      (fun z => ψ z * ∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2)
      (volume.restrict (Set.Icc 0 R)) :=
    (hψc.aestronglyMeasurable measurableSet_Icc).mul hAESM
  -- the pointwise bound on the box `[0,R]`
  have hpt : ∀ z ∈ Set.Icc 0 R,
      ‖ψ z * ∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2‖
        ≤ S * (C ^ 2 * (Real.pi / 2)) := by
    intro z hz
    have hGnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 :=
      setIntegral_nonneg measurableSet_Icc fun θ _ => sq_nonneg _
    have hGle : (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2) ≤ C ^ 2 * (Real.pi / 2) :=
      hCint z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hGnn]
    exact mul_le_mul (hSbd z hz) hGle hGnn hSnn
  -- integrability on the box
  have hfinmeas : IsFiniteMeasure (volume.restrict (Set.Icc 0 R)) := by
    rw [isFiniteMeasure_restrict]
    exact (measure_Icc_lt_top (μ := (volume : Measure ℝ))).ne
  have hfin : IntegrableOn (fun z => ψ z * ∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2)
      (Set.Icc 0 R) := by
    refine Integrable.of_bound hAESM_prod (S * (C ^ 2 * (Real.pi / 2))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact hpt z hz
  -- extend from `[0,R]` to `Iz = [0,∞)`
  exact integrableOn_Iz_of_support_Icc hR hfin fun z hz => by rw [hψ0 z hz, zero_mul]

end Work.FTS.EllipticEst.Auxiliary
