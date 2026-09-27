import Mathlib
import Submission.Work.Mostow.Comp0Support
import Submission.Work.Mostow.HlinPairing

set_option linter.style.haveILetI false

/-!
# Auxiliary lemmas for `Comp0`

This file collects everything the proof of `Comp0` needs besides the two "nice" pointwise
evaluations of `DGvIntegrand` (which live in `Comp0Support`):

* `integrable_inner_smul_comp`: the vector integrand `ξ ↦ ⟪φ ξ, w⟫ • φ ξ` of `Hlin n φ` is
  integrable for `sigma n` (its norm is a.e. bounded by `‖w‖`);
* `Hlin_apply`: `(Hlin n φ) w = ∫ ξ, ⟪φ ξ, w⟫ • φ ξ ∂(sigma n)`, the Bochner-integral form of
  the second-moment operator;
* `DGvIntegrand_integrable`: the integrand of `DGv n φ 0 0` is integrable for `sigma n`.  On the
  support of `sigma n` (the sphere) the four hypotheses `hp0`, `hdp`, `hg0`, `hh0` replace the
  integrand by the explicit bounded expression `niceCLM n ξ (φ ξ)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- Integrability of the vector integrand `ξ ↦ ⟪φ ξ, w⟫ • φ ξ`. -/
theorem integrable_inner_smul_comp (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hsupp : (Submission.Mostow.sigma n) (Set.compl (Submission.Mostow.Sph n)) = 0)
    (w : Submission.Mostow.E n) :
    Integrable (fun ξ => (inner ℝ (φ ξ) w) • φ ξ) (Submission.Mostow.sigma n) := by
  haveI : IsFiniteMeasure (Submission.Mostow.sigma n) := sigma_isFiniteMeasure n
  have hae : AEMeasurable φ (Submission.Mostow.sigma n) :=
    aemeasurable_of_continuousOn_of_compl_eq_zero (0 : Submission.Mostow.E n)
      Metric.isClosed_sphere.measurableSet hcont hsupp
  have hunit : ∀ᵐ ξ ∂(Submission.Mostow.sigma n), ‖φ ξ‖ = 1 := ae_norm_phi_eq_one n φ hbij
  have hφ : Continuous fun x : Submission.Mostow.E n => (inner ℝ x w) • x := by fun_prop
  refine Integrable.of_bound (hφ.measurable.comp_aemeasurable hae).aestronglyMeasurable ‖w‖ ?_
  filter_upwards [hunit] with ξ hξ
  calc ‖(inner ℝ (φ ξ) w) • φ ξ‖ = ‖inner ℝ (φ ξ) w‖ * ‖φ ξ‖ := norm_smul _ _
    _ ≤ (‖φ ξ‖ * ‖w‖) * ‖φ ξ‖ :=
        mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
    _ = ‖w‖ := by rw [hξ]; ring

/-- The second-moment operator `Hlin n φ` evaluated at a vector, as a Bochner integral. -/
theorem Hlin_apply (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hsupp : (Submission.Mostow.sigma n) (Set.compl (Submission.Mostow.Sph n)) = 0)
    (w : Submission.Mostow.E n) :
    (Work.Mostow.Hlin n φ) w
      = ∫ ξ, (inner ℝ (φ ξ) w) • φ ξ ∂(Submission.Mostow.sigma n) := by
  haveI : IsFiniteMeasure (Submission.Mostow.sigma n) := sigma_isFiniteMeasure n
  have hae : AEMeasurable φ (Submission.Mostow.sigma n) :=
    aemeasurable_of_continuousOn_of_compl_eq_zero (0 : Submission.Mostow.E n)
      Metric.isClosed_sphere.measurableSet hcont hsupp
  have hunit : ∀ᵐ ξ ∂(Submission.Mostow.sigma n), ‖φ ξ‖ = 1 := ae_norm_phi_eq_one n φ hbij
  have hψ : Continuous fun x : Submission.Mostow.E n => (innerSL ℝ x).smulRight x := by fun_prop
  have hLint : Integrable (fun ξ => (innerSL ℝ (φ ξ)).smulRight (φ ξ))
      (Submission.Mostow.sigma n) := by
    refine Integrable.of_bound (hψ.measurable.comp_aemeasurable hae).aestronglyMeasurable 1 ?_
    filter_upwards [hunit] with ξ hξ
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, hξ, mul_one]
  rw [Work.Mostow.Hlin, ContinuousLinearMap.integral_apply hLint w]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply])

/-- The "sphere form" of the integrand of `DGv n φ 0 0`: with `a = ξ` and `b = φ ξ` it is
`((n-1) • innerSL ℝ a).smulRight (-b) ∘L fst + (1 - (innerSL ℝ b).smulRight b) ∘L snd`. -/
def niceCLM (n : ℕ) (a b : Submission.Mostow.E n) :
    Submission.Mostow.E n × Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n :=
  ((((n : ℝ) - 1) • innerSL ℝ a).smulRight (-b)) ∘L
      ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n) +
    ((1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n) -
      (innerSL ℝ b).smulRight b) ∘L
      ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)

theorem continuous_niceCLM (n : ℕ) :
    Continuous fun p : Submission.Mostow.E n × Submission.Mostow.E n =>
      niceCLM n p.1 p.2 := by
  unfold niceCLM
  fun_prop

/-- On the sphere, the integrand of `DGv n φ 0 0` is the explicit expression `niceCLM n ξ (φ ξ)`. -/
theorem DGvIntegrand_eq_nice (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hp0 : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      Work.Mostow.pfun n 0 ξ = 1)
    (hdp : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      Work.Mostow.dpfun n 0 ξ = ((n : ℝ) - 1) • innerSL ℝ ξ)
    (hg0 : ∀ (η : Submission.Mostow.E n), η ∈ Submission.Mostow.Sph n →
      Work.Mostow.gradB n η 0 = -η)
    (hh0 : ∀ (η : Submission.Mostow.E n), η ∈ Submission.Mostow.Sph n →
      ∀ w : Submission.Mostow.E n,
        Work.Mostow.hessB n η 0 w = w - (inner ℝ η w) • η)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n) :
    Work.Mostow.DGvIntegrand n φ ξ = niceCLM n ξ (φ ξ) := by
  have h1 : (Work.Mostow.dpfun n 0 ξ).smulRight (Work.Mostow.gradB n (φ ξ) 0) =
      (((n : ℝ) - 1) • innerSL ℝ ξ).smulRight (-(φ ξ)) := by
    rw [hdp ξ hξ, hg0 (φ ξ) (hbij.1 hξ)]
  have h2 : Work.Mostow.pfun n 0 ξ • Work.Mostow.hessB n (φ ξ) 0 =
      (1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n) -
        (innerSL ℝ (φ ξ)).smulRight (φ ξ) := by
    rw [hp0 ξ hξ, hessB_zero_eq n (φ ξ) (hh0 (φ ξ) (hbij.1 hξ)), one_smul]
  rw [Work.Mostow.DGvIntegrand, niceCLM, h1, h2]

/-- The integrand of `DGv n φ 0 0` is integrable for `sigma n`. -/
theorem DGvIntegrand_integrable (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hsupp : (Submission.Mostow.sigma n) (Set.compl (Submission.Mostow.Sph n)) = 0)
    (hp0 : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      Work.Mostow.pfun n 0 ξ = 1)
    (hdp : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      Work.Mostow.dpfun n 0 ξ = ((n : ℝ) - 1) • innerSL ℝ ξ)
    (hg0 : ∀ (η : Submission.Mostow.E n), η ∈ Submission.Mostow.Sph n →
      Work.Mostow.gradB n η 0 = -η)
    (hh0 : ∀ (η : Submission.Mostow.E n), η ∈ Submission.Mostow.Sph n →
      ∀ w : Submission.Mostow.E n,
        Work.Mostow.hessB n η 0 w = w - (inner ℝ η w) • η) :
    Integrable (Work.Mostow.DGvIntegrand n φ) (Submission.Mostow.sigma n) := by
  haveI : IsFiniteMeasure (Submission.Mostow.sigma n) := sigma_isFiniteMeasure n
  have hae : AEMeasurable φ (Submission.Mostow.sigma n) :=
    aemeasurable_of_continuousOn_of_compl_eq_zero (0 : Submission.Mostow.E n)
      Metric.isClosed_sphere.measurableSet hcont hsupp
  have hpair : AEMeasurable (fun ξ : Submission.Mostow.E n => (ξ, φ ξ))
      (Submission.Mostow.sigma n) := aemeasurable_id.prodMk hae
  have hmeas : AEStronglyMeasurable (fun ξ : Submission.Mostow.E n => niceCLM n ξ (φ ξ))
      (Submission.Mostow.sigma n) :=
    ((continuous_niceCLM n).measurable.comp_aemeasurable hpair).aestronglyMeasurable
  have hbd : ∀ᵐ ξ ∂(Submission.Mostow.sigma n),
      ‖niceCLM n ξ (φ ξ)‖ ≤ |(n : ℝ) - 1| + 2 := by
    filter_upwards [ae_mem_sph_sigma n, ae_norm_phi_eq_one n φ hbij] with ξ hξ hφξ
    have hξn : ‖ξ‖ = 1 := by
      simpa [Submission.Mostow.Sph, Metric.mem_sphere, dist_eq_norm] using hξ
    have hA' : ‖(((n : ℝ) - 1) • innerSL ℝ ξ).smulRight (-(φ ξ))‖ ≤ |(n : ℝ) - 1| := by
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs, norm_neg,
        innerSL_apply_norm, hξn, hφξ]
      simp
    have hA : ‖((((n : ℝ) - 1) • innerSL ℝ ξ).smulRight (-(φ ξ))) ∘L
        ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)‖
        ≤ |(n : ℝ) - 1| := by
      refine le_trans (ContinuousLinearMap.opNorm_comp_le
        (h := (((n : ℝ) - 1) • innerSL ℝ ξ).smulRight (-(φ ξ)))
        (f := ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n))) ?_
      calc ‖(((n : ℝ) - 1) • innerSL ℝ ξ).smulRight (-(φ ξ))‖ *
              ‖ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)‖
          ≤ |(n : ℝ) - 1| * 1 :=
            mul_le_mul hA' (ContinuousLinearMap.norm_fst_le ℝ (Submission.Mostow.E n)
              (Submission.Mostow.E n)) (norm_nonneg _) (abs_nonneg _)
        _ = |(n : ℝ) - 1| := mul_one _
    have hB' : ‖(1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n) -
        (innerSL ℝ (φ ξ)).smulRight (φ ξ)‖ ≤ 2 := by
      have hone : ‖(1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)‖ ≤ 1 :=
        ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Submission.Mostow.E n)
      have hR : ‖(innerSL ℝ (φ ξ)).smulRight (φ ξ)‖ = 1 := by
        rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, hφξ, mul_one]
      linarith [norm_sub_le (1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)
        ((innerSL ℝ (φ ξ)).smulRight (φ ξ))]
    have hB : ‖((1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n) -
        (innerSL ℝ (φ ξ)).smulRight (φ ξ)) ∘L
        ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)‖ ≤ 2 := by
      refine le_trans (ContinuousLinearMap.opNorm_comp_le
        (h := (1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n) -
          (innerSL ℝ (φ ξ)).smulRight (φ ξ))
        (f := ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n))) ?_
      calc ‖(1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n) -
              (innerSL ℝ (φ ξ)).smulRight (φ ξ)‖ *
              ‖ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)‖
          ≤ 2 * 1 :=
            mul_le_mul hB' (ContinuousLinearMap.norm_snd_le ℝ (Submission.Mostow.E n)
              (Submission.Mostow.E n)) (norm_nonneg _) (by norm_num)
        _ = 2 := mul_one 2
    rw [niceCLM]
    exact le_trans (norm_add_le _ _) (add_le_add hA hB)
  have hInt : Integrable (fun ξ : Submission.Mostow.E n => niceCLM n ξ (φ ξ))
      (Submission.Mostow.sigma n) := Integrable.of_bound hmeas _ hbd
  refine hInt.congr ?_
  filter_upwards [ae_mem_sph_sigma n] with ξ hξ
  exact (DGvIntegrand_eq_nice n φ hbij hp0 hdp hg0 hh0 hξ).symm

end

end Work.Mostow
