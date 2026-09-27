import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.NatMeasure
import Submission.Work.Mostow.visualBasic

set_option linter.style.haveILetI false

/-!
# The pairing identity for the second-moment operator `Hlin`

`Hlin n φ = ∫ ξ, (innerSL ℝ (φ ξ)).smulRight (φ ξ) ∂(sigma n)` is the Bochner integral of the
rank-one operators `v ↦ ⟪φ ξ, v⟫ • φ ξ` against the rotation invariant probability measure
`sigma n` on `Sph n`.  This file evaluates its pairing:

`⟪(Hlin n φ) v, w⟫ = ∫ ξ, ⟪φ ξ, v⟫ * ⟪φ ξ, w⟫ ∂(sigma n)`,

for `φ` an a.e.-measurable map carrying `Sph n` into `Sph n` (the hypotheses below supply this:
`φ` is a continuous bijection of `Sph n` and `sigma n` is carried by `Sph n`).

The proof is the standard interchange of a continuous linear map with a Bochner integral
(`ContinuousLinearMap.integral_apply`, `ContinuousLinearMap.integral_comp_comm`), the only
work being the integrability side conditions: on the support of `sigma n` the function `φ` is
a.e. unit-valued, so both integrands are a.e. bounded and `sigma n` is a finite measure.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- `sigma n` is a finite measure: it is `(sphM n univ)⁻¹ • sphM n`, whose total mass is at
most `1` (it is a probability measure when `sphM n univ ≠ 0`, and the zero measure otherwise). -/
theorem sigma_isFiniteMeasure (n : ℕ) : IsFiniteMeasure (Submission.Mostow.sigma n) := by
  rw [isFiniteMeasure_iff, sigma_eq_smul_sphM, Measure.smul_apply, smul_eq_mul]
  refine lt_of_le_of_lt ?_ ENNReal.one_lt_top
  have hle : (sphM n Set.univ)⁻¹ * sphM n Set.univ ≤ 1 := by
    by_cases h : sphM n Set.univ = 0
    · rw [h]; simp
    · rw [ENNReal.inv_mul_cancel h (sphM_univ_ne_top n)]
  exact hle

/-- `inner ℝ · w` commutes with the Bochner integral of an integrable `E n`-valued function. -/
theorem inner_integral_right {n : ℕ} (μ : Measure (E n)) {g : E n → E n}
    (hg : Integrable g μ) (w : E n) :
    inner ℝ (∫ ξ, g ξ ∂μ) w = ∫ ξ, inner ℝ (g ξ) w ∂μ := by
  have h := ContinuousLinearMap.integral_comp_comm (innerSL ℝ w) hg
  rw [innerSL_apply_apply] at h
  rw [real_inner_comm (∫ ξ, g ξ ∂μ) w] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
    simp only [innerSL_apply_apply]
    exact real_inner_comm (g ξ) w)

/-- Pairing identity for an integral of rank-one operators.  If `f` is a.e.-measurable and
a.e. unit-valued for a finite measure `μ`, then the Bochner integral of the rank-one operators
`(innerSL ℝ (f ξ)).smulRight (f ξ)` pairs with `(v, w)` as the scalar integral of
`⟪f ξ, v⟫ * ⟪f ξ, w⟫`. -/
theorem inner_integral_smulRight {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (f : E n → E n) (hae : AEMeasurable f μ) (hunit : ∀ᵐ ξ ∂μ, ‖f ξ‖ = 1) (v w : E n) :
    inner ℝ ((∫ ξ, (innerSL ℝ (f ξ)).smulRight (f ξ) ∂μ) v) w
      = ∫ ξ, (inner ℝ (f ξ) v) * (inner ℝ (f ξ) w) ∂μ := by
  have hψ : Continuous fun x : E n => (innerSL ℝ x).smulRight x := by fun_prop
  have hφ : Continuous fun x : E n => (inner ℝ x v) • x := by fun_prop
  -- integrability of the rank-one operators
  have hLint : Integrable (fun ξ => (innerSL ℝ (f ξ)).smulRight (f ξ)) μ := by
    refine Integrable.of_bound (hψ.measurable.comp_aemeasurable hae).aestronglyMeasurable 1 ?_
    filter_upwards [hunit] with ξ h
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, h, mul_one]
  -- integrability of the vector integrand
  have hgint : Integrable (fun ξ => (inner ℝ (f ξ) v) • f ξ) μ := by
    refine Integrable.of_bound (hφ.measurable.comp_aemeasurable hae).aestronglyMeasurable
      ‖v‖ ?_
    filter_upwards [hunit] with ξ h
    calc ‖(inner ℝ (f ξ) v) • f ξ‖ = ‖inner ℝ (f ξ) v‖ * ‖f ξ‖ := norm_smul _ _
      _ ≤ (‖f ξ‖ * ‖v‖) * ‖f ξ‖ :=
          mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
      _ = ‖v‖ := by rw [h]; ring
  -- interchange the integral with the two continuous linear maps
  have h1 : (∫ ξ, (innerSL ℝ (f ξ)).smulRight (f ξ) ∂μ) v
      = ∫ ξ, (inner ℝ (f ξ) v) • f ξ ∂μ := by
    rw [ContinuousLinearMap.integral_apply hLint v]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
      simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply])
  rw [h1, inner_integral_right μ hgint w]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
    simp only [real_inner_smul_left])

theorem HlinPairing (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hsupp : Submission.Mostow.sigma n (Submission.Mostow.Sph n)ᶜ = 0)
    (v w : Submission.Mostow.E n) :
    inner ℝ ((Work.Mostow.Hlin n φ) v) w
      = ∫ ξ, (inner ℝ (φ ξ) v) * (inner ℝ (φ ξ) w) ∂(Submission.Mostow.sigma n) := by
  haveI := sigma_isFiniteMeasure n
  -- `φ` is a.e. measurable and almost everywhere unit-valued
  have hae : AEMeasurable φ (sigma n) :=
    aemeasurable_of_continuousOn_of_compl_eq_zero (0 : E n)
      Metric.isClosed_sphere.measurableSet hcont hsupp
  have hmem : ∀ᵐ ξ ∂(sigma n), ξ ∈ Sph n := by
    rw [ae_iff]; simpa only [Set.compl_def] using hsupp
  have hunit : ∀ᵐ ξ ∂(sigma n), ‖φ ξ‖ = 1 :=
    (hmem.mono fun ξ h => hbij.1 h).mono fun ξ h => by
      rw [Submission.Mostow.Sph, Metric.mem_sphere, dist_eq_norm, sub_zero] at h
      exact h
  simpa only [Hlin] using inner_integral_smulRight (sigma n) φ hae hunit v w

end

end Work.Mostow
