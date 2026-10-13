/-
# `Work.FTS.BSSwirl.CdCont` — continuity of the singular kernel integral

The derivative `potDeriv ω x` of the Newtonian potential is the singular integral

  `x ↦ ∫ z, (k z).smulRight (ω (x + z))`

of an `L¹`-kernel `k` against the *merely bounded* density `ω`.  The kernel is not continuous
(and neither is `ω`), so the pointwise dominated-convergence theorem does not apply; the correct
mechanism is the **continuity of translations in `L¹`**:

  `‖T (x+h) - T x‖ ≤ M ∫ z, ‖k (z+h) - k z‖ → 0`  as `h → 0`,

where the substitution `z ↦ z + h` (translation invariance of Lebesgue measure) moves the shift
from the density to the kernel.  This file proves that reduction: it takes the translation
continuity as a hypothesis (`htrans`) and derives the continuity of the integral.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.CdAux

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- `smulRight` is additive in its first argument. -/
theorem sub_smulRight (c c' : R3 →L[ℝ] ℝ) (v : R3) :
    (c - c').smulRight v = c.smulRight v - c'.smulRight v := by
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.sub_apply, sub_smul]

/-- The integrand `z ↦ (A z).smulRight (g (c + z))` is a.e. strongly measurable as soon as `A`
and `g` are. -/
theorem aestronglyMeasurable_smulRight_comp {A : R3 → (R3 →L[ℝ] ℝ)} {g : R3 → R3} {c : R3}
    (hA : AEStronglyMeasurable A volume) (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun z : R3 => (A z).smulRight (g (c + z))) volume := by
  have h1 : AEMeasurable A volume := aestronglyMeasurable_iff_aemeasurable.mp hA
  have h2 : AEMeasurable (fun z : R3 => g (c + z)) volume :=
    aestronglyMeasurable_iff_aemeasurable.mp
      (hg.comp_quasiMeasurePreserving
        (measurePreserving_add_left (volume : Measure R3) c).quasiMeasurePreserving)
  have hcont : Continuous fun p : (R3 →L[ℝ] ℝ) × R3 => p.1.smulRight p.2 :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := R3) (F := R3)).continuous
  exact (hcont.aemeasurable2 h1 h2).aestronglyMeasurable

/-- The integrand `z ↦ (A (z + t)).smulRight (g (c + z))` is integrable when `A` is integrable
and `g` is bounded and a.e. strongly measurable. -/
theorem integrable_smulRight_shift {A : R3 → (R3 →L[ℝ] ℝ)} {g : R3 → R3} {M : ℝ} {t c : R3}
    (hA : Integrable A volume) (hg : ∀ y, ‖g y‖ ≤ M) (hgmeas : AEStronglyMeasurable g volume) :
    Integrable (fun z : R3 => (A (z + t)).smulRight (g (c + z))) volume := by
  have hAt : Integrable (fun z : R3 => A (z + t)) volume := by
    simpa only [sub_neg_eq_add] using hA.comp_sub_right (-t)
  refine Integrable.mono' (hAt.norm.mul_const M) ?_ ?_
  · refine aestronglyMeasurable_smulRight_comp ?_ hgmeas
    exact hA.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_add_right (volume : Measure R3) t).quasiMeasurePreserving
  · filter_upwards with z
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_left (hg (c + z)) (norm_nonneg _)

/-- **Continuity of the singular kernel integral.**  If `A` is integrable and `g` is bounded by `M`
and a.e. strongly measurable, and if the `L¹`-norm of `A` is continuous under translations
(`htrans`), then `x ↦ ∫ z, (A z).smulRight (g (x + z))` is continuous. -/
theorem continuous_integral_smulRight_shift {A : R3 → (R3 →L[ℝ] ℝ)} {g : R3 → R3} {M : ℝ}
    (hA : Integrable A volume) (hg : ∀ y, ‖g y‖ ≤ M) (hgmeas : AEStronglyMeasurable g volume)
    (htrans : Tendsto (fun h : R3 => ∫ z, ‖A (z + h) - A z‖) (𝓝 0) (𝓝 0)) :
    Continuous (fun x : R3 => ∫ z, (A z).smulRight (g (x + z))) := by
  have hM : 0 ≤ M := (norm_nonneg (g 0)).trans (hg 0)
  -- the key estimate: shifting the density to the kernel
  have hkey : ∀ x₀ h : R3,
      dist (∫ z, (A z).smulRight (g (x₀ + h + z))) (∫ z, (A z).smulRight (g (x₀ + z)))
        ≤ M * ∫ z, ‖A (z + h) - A z‖ := by
    intro x₀ h
    have hsplit : (∫ z, (A z).smulRight (g (x₀ + z)))
        = ∫ z, (A (z + h)).smulRight (g (x₀ + h + z)) := by
      have hsub := integral_add_right_eq_self (μ := (volume : Measure R3))
        (f := fun z : R3 => (A z).smulRight (g (x₀ + z))) h
      rw [← hsub]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show (A (z + h)).smulRight (g (x₀ + (z + h))) = (A (z + h)).smulRight (g (x₀ + h + z))
      have harg : x₀ + (z + h) = x₀ + h + z := by abel
      rw [harg]
    have hint1 : Integrable (fun z : R3 => (A z).smulRight (g (x₀ + h + z))) volume := by
      simpa only [add_zero] using
        integrable_smulRight_shift (t := 0) (c := x₀ + h) hA hg hgmeas
    have hint2 : Integrable (fun z : R3 => (A (z + h)).smulRight (g (x₀ + h + z))) volume :=
      integrable_smulRight_shift (t := h) (c := x₀ + h) hA hg hgmeas
    have hdiff : (∫ z, (A z).smulRight (g (x₀ + h + z)))
          - (∫ z, (A z).smulRight (g (x₀ + z)))
        = ∫ z, ((A z) - (A (z + h))).smulRight (g (x₀ + h + z)) := by
      rw [hsplit, ← integral_sub hint1 hint2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      exact (sub_smulRight (A z) (A (z + h)) (g (x₀ + h + z))).symm
    have hAh : Integrable (fun z : R3 => A (z + h)) volume := by
      simpa only [sub_neg_eq_add] using hA.comp_sub_right (-h)
    have hint3 : Integrable (fun z : R3 => M * ‖A (z + h) - A z‖) volume :=
      ((hAh.sub hA).norm).const_mul M
    have hbnd : ∀ᵐ z ∂(volume : Measure R3),
        ‖((A z) - (A (z + h))).smulRight (g (x₀ + h + z))‖ ≤ M * ‖A (z + h) - A z‖ := by
      filter_upwards with z
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_sub_rev, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hg (x₀ + h + z)) (norm_nonneg _)
    rw [dist_eq_norm, hdiff]
    calc ‖∫ z, ((A z) - (A (z + h))).smulRight (g (x₀ + h + z))‖
        ≤ ∫ z, M * ‖A (z + h) - A z‖ := norm_integral_le_of_norm_le hint3 hbnd
      _ = M * ∫ z, ‖A (z + h) - A z‖ := integral_const_mul M _
  have hbound : ∀ x x₀ : R3,
      dist (∫ z, (A z).smulRight (g (x + z))) (∫ z, (A z).smulRight (g (x₀ + z)))
        ≤ M * ∫ z, ‖A (z + (x - x₀)) - A z‖ := by
    intro x x₀
    have h := hkey x₀ (x - x₀)
    rwa [show x₀ + (x - x₀) = x from by abel] at h
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hJ : Tendsto (fun h : R3 => M * ∫ z, ‖A (z + h) - A z‖) (𝓝 0) (𝓝 0) := by
    have h1 := htrans.const_mul M
    simpa using h1
  have hJnn : ∀ h : R3, 0 ≤ M * ∫ z, ‖A (z + h) - A z‖ := fun h =>
    mul_nonneg hM (integral_nonneg (fun z => norm_nonneg _))
  have hball : ∀ᶠ h : R3 in 𝓝 (0 : R3), M * ∫ z, ‖A (z + h) - A z‖ < ε := by
    filter_upwards [(Metric.tendsto_nhds.mp hJ) ε hε] with h hh
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hJnn h)] at hh
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hball
  refine ⟨δ, hδpos, fun y hy => ?_⟩
  have hyball : y - x₀ ∈ Metric.ball (0 : R3) δ := by
    rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
    exact hy
  calc dist (∫ z, (A z).smulRight (g (y + z))) (∫ z, (A z).smulRight (g (x₀ + z)))
      ≤ M * ∫ z, ‖A (z + (y - x₀)) - A z‖ := hbound y x₀
    _ < ε := hδ hyball

end

end Work.FTS.BSSwirl
