import Mathlib
import Submission.Work.Mostow.BCGDefs

/-!
# Support lemmas for the `Comp0` Jacobian computation (`NatMapJacProp`)

`Comp0` evaluates the joint Fréchet derivative `DGv n φ 0 0` of the `y`-gradient `Gv n φ` of the
barycentre functional at the base point `(0,0)`, in the two coordinate directions.  This file
collects the small facts that both the statement and its proof need:

* `sigma n` is carried by the unit sphere `Sph n` (and a.e. every point of it lies on the sphere);
* `dpfun n 0 ξ = (n-1) • innerSL ℝ ξ` identically (sharper than the hypothesis `hdp` of `Comp0`,
  which only asks for `ξ ∈ Sph n`);
* the Hessian of the Busemann function at `0`, read as a continuous linear map, is
  `1 - (innerSL ℝ η).smulRight η`;
* a bijection of the sphere is a.e. unit-valued for `sigma n`;
* the integrand `DGvIntegrand n φ` of `DGv n φ 0 0`, as a named definition.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- `sigma n` is carried by the unit sphere `Sph n`. -/
theorem sigma_supp_compl (n : ℕ) :
    (Submission.Mostow.sigma n) (Submission.Mostow.Sph n)ᶜ = 0 := by
  unfold Submission.Mostow.sigma Submission.Mostow.Sph
  rw [Measure.smul_apply]
  have h0 : (((volume : Measure (Submission.Mostow.E n)).toSphere).map Subtype.val)
      (Metric.sphere (0 : Submission.Mostow.E n) 1)ᶜ = 0 := by
    rw [Measure.map_apply measurable_subtype_coe Metric.isClosed_sphere.measurableSet.compl]
    have h : Subtype.val ⁻¹' (Metric.sphere (0 : Submission.Mostow.E n) 1)ᶜ
        = (∅ : Set (Metric.sphere (0 : Submission.Mostow.E n) 1)) := by
      ext x; simp
    rw [h]; simp
  rw [h0, smul_zero]

/-- Almost every point of `sigma n` lies on the unit sphere. -/
theorem ae_mem_sph_sigma (n : ℕ) :
    ∀ᵐ ξ ∂(Submission.Mostow.sigma n), ξ ∈ Submission.Mostow.Sph n := by
  rw [ae_iff]
  simpa only [Set.compl_def] using sigma_supp_compl n

/-- `dpfun` at the base point `0` is exactly `(n-1) • innerSL ℝ ξ`, for every `ξ`. -/
theorem dpfun_zero (n : ℕ) (ξ : Submission.Mostow.E n) :
    Work.Mostow.dpfun n 0 ξ = ((n : ℝ) - 1) • innerSL ℝ ξ := by
  have h1 : tpart (0 : Submission.Mostow.E n) = 1 := by simp [Submission.Mostow.tpart]
  rw [Work.Mostow.dpfun]
  rw [inner_zero_left, sub_zero, h1]
  rw [Real.one_rpow, mul_one, inv_one, one_smul, map_zero, zero_sub,
    smul_neg, neg_smul, neg_neg]

/-- The Hessian of the Busemann function `busemann η ·` at `0`, as a continuous linear map. -/
theorem hessB_zero_eq (n : ℕ) (η : Submission.Mostow.E n)
    (hh0 : ∀ w : Submission.Mostow.E n,
      Work.Mostow.hessB n η 0 w = w - (inner ℝ η w) • η) :
    Work.Mostow.hessB n η 0
      = (1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n) -
        (innerSL ℝ η).smulRight η := by
  ext w
  rw [hh0 w]
  simp [sub_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/-- A bijection of the sphere is almost everywhere unit-valued for `sigma n`. -/
theorem ae_norm_phi_eq_one (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n)) :
    ∀ᵐ ξ ∂(Submission.Mostow.sigma n), ‖φ ξ‖ = 1 := by
  filter_upwards [ae_mem_sph_sigma n] with ξ hξ
  have h1 : φ ξ ∈ Submission.Mostow.Sph n := hbij.1 hξ
  simpa [Submission.Mostow.Sph, Metric.mem_sphere, dist_eq_norm] using h1

/-- The integrand of `DGv n φ 0 0`. -/
def DGvIntegrand (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (ξ : Submission.Mostow.E n) : Submission.Mostow.E n × Submission.Mostow.E n →L[ℝ]
      Submission.Mostow.E n :=
  ((Work.Mostow.dpfun n 0 ξ).smulRight (Work.Mostow.gradB n (φ ξ) 0)) ∘L
      ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n) +
    (Work.Mostow.pfun n 0 ξ • Work.Mostow.hessB n (φ ξ) 0) ∘L
      ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)

/-- `DGv n φ 0 0` is the Bochner integral of `DGvIntegrand n φ`. -/
theorem DGv_zero_eq_integral (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n) :
    Work.Mostow.DGv n φ 0 0 = ∫ ξ, DGvIntegrand n φ ξ ∂(Submission.Mostow.sigma n) := rfl

/-- Pointwise value of the integrand in the first coordinate direction. -/
theorem DGvIntegrand_apply_inl (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hp0 : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      Work.Mostow.pfun n 0 ξ = 1)
    (hdp : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      Work.Mostow.dpfun n 0 ξ = ((n : ℝ) - 1) • innerSL ℝ ξ)
    (hg0 : ∀ (η : Submission.Mostow.E n), η ∈ Submission.Mostow.Sph n →
      Work.Mostow.gradB n η 0 = -η)
    (v : Submission.Mostow.E n) {ξ : Submission.Mostow.E n}
    (hξ : ξ ∈ Submission.Mostow.Sph n) :
    DGvIntegrand n φ ξ (v, 0) = (-((n : ℝ) - 1)) • ((inner ℝ ξ v) • φ ξ) := by
  rw [DGvIntegrand, add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply]
  rw [show (ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)) (v, 0)
        = v from rfl,
      show (ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)) (v, 0)
        = 0 from rfl]
  rw [hdp ξ hξ, hg0 (φ ξ) (hbij.1 hξ), hp0 ξ hξ, map_zero, one_smul, add_zero,
    smul_apply, innerSL_apply_apply]
  rw [smul_neg, neg_smul, smul_smul, smul_eq_mul]

/-- Pointwise value of the integrand in the second coordinate direction. -/
theorem DGvIntegrand_apply_inr (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hp0 : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      Work.Mostow.pfun n 0 ξ = 1)
    (hh0 : ∀ (η : Submission.Mostow.E n), η ∈ Submission.Mostow.Sph n →
      ∀ w : Submission.Mostow.E n,
        Work.Mostow.hessB n η 0 w = w - (inner ℝ η w) • η)
    (w : Submission.Mostow.E n) {ξ : Submission.Mostow.E n}
    (hξ : ξ ∈ Submission.Mostow.Sph n) :
    DGvIntegrand n φ ξ (0, w) = w - (inner ℝ (φ ξ) w) • φ ξ := by
  rw [DGvIntegrand, add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply]
  rw [show (ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)) (0, w)
        = 0 from rfl,
      show (ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)) (0, w)
        = w from rfl]
  rw [hp0 ξ hξ, hh0 (φ ξ) (hbij.1 hξ) w, map_zero, one_smul, zero_smul, zero_add]

end

end Work.Mostow
