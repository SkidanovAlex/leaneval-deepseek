import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.Comp0Support
import Submission.Work.Mostow.Comp0Aux
import Submission.Work.Mostow.HlinPairing

namespace Work.Mostow

open MeasureTheory

theorem Comp0 (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hp0 : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      Work.Mostow.pfun n 0 ξ = 1)
    (hdp : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      Work.Mostow.dpfun n 0 ξ = ((n : ℝ) - 1) • innerSL ℝ ξ)
    (hg0 : ∀ (η : Submission.Mostow.E n), η ∈ Submission.Mostow.Sph n →
      Work.Mostow.gradB n η 0 = -η)
    (hh0 : ∀ (η : Submission.Mostow.E n), η ∈ Submission.Mostow.Sph n →
      ∀ w : Submission.Mostow.E n,
        Work.Mostow.hessB n η 0 w = w - (inner ℝ η w) • η)
    (hprob : (Submission.Mostow.sigma n) Set.univ = 1) :
    (∀ v : Submission.Mostow.E n,
      Work.Mostow.DGv n φ 0 0 (v, 0) =
        -((n : ℝ) - 1) • ∫ ξ, (inner ℝ ξ v) • φ ξ ∂(Submission.Mostow.sigma n)) ∧
    (∀ w : Submission.Mostow.E n,
      Work.Mostow.DGv n φ 0 0 (0, w) = w - (Work.Mostow.Hlin n φ) w) := by
  have hsupp : (Submission.Mostow.sigma n) (Set.compl (Submission.Mostow.Sph n)) = 0 :=
    sigma_supp_compl n
  have hInt : MeasureTheory.Integrable (Work.Mostow.DGvIntegrand n φ)
      (Submission.Mostow.sigma n) :=
    DGvIntegrand_integrable n φ hbij hcont hsupp hp0 hdp hg0 hh0
  have hGint : ∀ w : Submission.Mostow.E n,
      MeasureTheory.Integrable (fun ξ => (inner ℝ (φ ξ) w) • φ ξ)
        (Submission.Mostow.sigma n) :=
    fun w => integrable_inner_smul_comp n φ hbij hcont hsupp w
  have hHlin : ∀ w : Submission.Mostow.E n, (Work.Mostow.Hlin n φ) w
      = ∫ ξ, (inner ℝ (φ ξ) w) • φ ξ ∂(Submission.Mostow.sigma n) :=
    fun w => Hlin_apply n φ hbij hcont hsupp w
  refine ⟨?_, ?_⟩
  · intro v
    have h1 : Work.Mostow.DGv n φ 0 0 (v, 0)
        = ∫ ξ, Work.Mostow.DGvIntegrand n φ ξ (v, 0) ∂(Submission.Mostow.sigma n) := by
      rw [DGv_zero_eq_integral]
      exact ContinuousLinearMap.integral_apply hInt (v, 0)
    have h2 : ∫ ξ, Work.Mostow.DGvIntegrand n φ ξ (v, 0) ∂(Submission.Mostow.sigma n)
        = ∫ ξ, (-((n : ℝ) - 1)) • ((inner ℝ ξ v) • φ ξ)
            ∂(Submission.Mostow.sigma n) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [ae_mem_sph_sigma n] with ξ hξ
      exact DGvIntegrand_apply_inl n φ hbij hp0 hdp hg0 v hξ
    rw [h1, h2, MeasureTheory.integral_smul]
  · intro w
    have h1 : Work.Mostow.DGv n φ 0 0 (0, w)
        = ∫ ξ, Work.Mostow.DGvIntegrand n φ ξ (0, w) ∂(Submission.Mostow.sigma n) := by
      rw [DGv_zero_eq_integral]
      exact ContinuousLinearMap.integral_apply hInt (0, w)
    have h2 : ∫ ξ, Work.Mostow.DGvIntegrand n φ ξ (0, w) ∂(Submission.Mostow.sigma n)
        = ∫ ξ, (w - (inner ℝ (φ ξ) w) • φ ξ) ∂(Submission.Mostow.sigma n) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [ae_mem_sph_sigma n] with ξ hξ
      exact DGvIntegrand_apply_inr n φ hbij hp0 hh0 w hξ
    have h3 : ∫ ξ, (w - (inner ℝ (φ ξ) w) • φ ξ) ∂(Submission.Mostow.sigma n)
        = w - (Work.Mostow.Hlin n φ) w := by
      haveI : IsFiniteMeasure (Submission.Mostow.sigma n) :=
        ⟨by rw [hprob]; exact ENNReal.one_lt_top⟩
      rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const w) (hGint w),
        ← hHlin w]
      congr 1
      rw [MeasureTheory.integral_const]
      simp [Measure.real, hprob]
    rw [h1, h2, h3]

end Work.Mostow
