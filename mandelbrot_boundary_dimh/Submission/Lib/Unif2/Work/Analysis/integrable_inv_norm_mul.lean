import Mathlib

/-!
# Integrability of `z ↦ ‖z - p‖⁻¹ · φ z`

For a continuous compactly supported `φ : ℂ → ℝ` the function `z ↦ ‖z - p‖⁻¹ φ z` is integrable:
in two real dimensions `‖z‖⁻¹` is locally integrable
(`MeasureTheory.locallyIntegrable_of_norm_le_rpow` with `α = 1 < 2 = finrank ℝ ℂ`), and compact
support upgrades local integrability to integrability.

This is the `L¹` input of the chart-wise Green identity: the Dirichlet pairing of a Green function
against a test function is singular only like `1/‖z - pole‖`, hence absolutely convergent.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace Work.Analysis

/-- Integrability of `z ↦ ‖z - p‖⁻¹ * φ z` for continuous compactly supported `φ`. -/
theorem integrable_inv_norm_mul_of_hasCompactSupport (p : ℂ) (φ : ℂ → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : ℂ => (‖z - p‖)⁻¹ * φ z) := by
  have hcK : IsCompact (tsupport φ) := hc
  obtain ⟨M, hM⟩ := hcK.exists_bound_of_continuousOn hφ.continuousOn
  set M' : ℝ := max M 0 with hM'def
  have hM'nn : 0 ≤ M' := le_max_right _ _
  have hM'bound : ∀ z : ℂ, ‖φ z‖ ≤ M' := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · exact le_trans (hM z hz) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]; exact hM'nn
  -- the translation putting the singular point at the origin
  have hshift_def : (fun z : ℂ => (‖z - p‖)⁻¹ * φ z)
      = fun t : ℂ => (fun w : ℂ => (‖w‖)⁻¹ * φ (w + p)) (-p + t) := by
    funext t
    have h1 : -p + t = t - p := by ring
    rw [h1]
    change ‖t - p‖⁻¹ * φ t = ‖t - p‖⁻¹ * φ ((t - p) + p)
    rw [sub_add_cancel]
  rw [hshift_def]
  -- integrability of the translated function
  have hcs : HasCompactSupport (fun w : ℂ => (‖w‖)⁻¹ * φ (w + p)) :=
    HasCompactSupport.mul_left (hc.comp_homeomorph (Homeomorph.addRight p))
  have hdecay : ∀ᵐ w ∂(volume : Measure ℂ),
      ‖(‖w‖)⁻¹ * φ (w + p)‖ ≤ M' * ‖w‖ ^ (-(1 : ℝ)) := by
    refine Filter.Eventually.of_forall (fun w => ?_)
    rw [Real.rpow_neg_one, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg w))]
    calc (‖w‖)⁻¹ * ‖φ (w + p)‖ ≤ (‖w‖)⁻¹ * M' :=
          mul_le_mul_of_nonneg_left (hM'bound (w + p)) (inv_nonneg.mpr (norm_nonneg w))
      _ = M' * (‖w‖)⁻¹ := by ring
  have hli : LocallyIntegrable (fun w : ℂ => (‖w‖)⁻¹ * φ (w + p)) volume :=
    MeasureTheory.locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℝ)
      (by rw [Complex.finrank_real_complex]; norm_num) (C := M') (α := 1)
      (by rw [Complex.finrank_real_complex]; norm_num) hdecay
      (measurable_norm.inv.mul (hφ.measurable.comp
        (measurable_id.add measurable_const))).aestronglyMeasurable
  have h1 : Integrable (fun w : ℂ => (‖w‖)⁻¹ * φ (w + p)) :=
    (hli.integrableOn_isCompact hcs).integrable_of_forall_notMem_eq_zero (fun w hw => by
      by_contra hne
      exact hw (subset_tsupport _ (Function.mem_support.mpr hne)))
  exact h1.comp_add_left (-p)

end Work.Analysis
