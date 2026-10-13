import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.NRow10aux

set_option autoImplicit false

theorem hkmem_of_majorant (α : ℝ) (k : ℕ) {h f : ℝ → ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hsmh : Work.FTS.EllipticEst.SmoothOpen h) (hmf : Work.Spaces.HkMem α k f)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α k h z θ ≤ K * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkMem α k h ∧ Work.Spaces.HkSq α k h ≤ K * Work.Spaces.HkSq α k f := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsmh.continuousOn_HkIntegrand α k
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.HkIntegrand α k h z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k h 0 θ) = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => by simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz0
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hMslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ : ℝ => K * Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ :=
    fun z hz => (hmf.1 z hz).const_mul K
  have hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      K * Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := by
    have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, K * Work.Spaces.HkIntegrand α k f z θ)
        = fun z => K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
      funext fun z => MeasureTheory.integral_const_mul K _
    rw [hfun]
    exact hmf.2.const_mul K
  have hle_ae : ∀ z ∈ Work.Spaces.Iz,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α k h z θ ≤ K * Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) :=
      (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0:ℝ))
          (b := (π/2)))).symm
    rw [hmeas]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hle z hz θ hθ)
  have hmem : Work.Spaces.HkMem α k h := by
    constructor
    · intro z hz
      refine MeasureTheory.Integrable.mono' (hMslice z hz) (hslice z hz) ?_
      filter_upwards [hle_ae z hz] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k h z θ)]
      exact hθ
    · refine MeasureTheory.Integrable.mono' hMz hjoint.integral_prod_right' ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ :=
        MeasureTheory.integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ)
        ((hmf.1 z hz).const_mul K) (hle_ae z hz)
  refine ⟨hmem, ?_⟩
  simp only [Work.Spaces.HkSq]
  have hstep : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ)
      (hmf.2.const_mul K) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have h2 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      have h3 := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k h z θ)
        ((hmf.1 z hz).const_mul K) (hle_ae z hz)
      rwa [MeasureTheory.integral_const_mul] at h3
    exact h2
  exact le_trans hstep (le_of_eq (MeasureTheory.integral_const_mul K _))

end Work.FTS.NonlinRows.NRow10aux
