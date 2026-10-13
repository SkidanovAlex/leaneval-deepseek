import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral
import Submission.Work.FTS.EllipticEst.Honest.honLintegralSliceBridge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.FOH

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- At `z = 0` the level-`0` `HkIntegrand` vanishes identically (the radial weight is `0`). -/
theorem HkIntegrand_zero_left' (α : ℝ) (g : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g 0 θ = 0 := by
  rw [HkIntegrand_zero_eq]
  have h : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
  rw [h]
  simp

/-- **The `∫⁻`-functional of a profile is `ofReal (HkSq)`**, for honest data. -/
theorem lintegral_sig_eq_ofReal_HkSq {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.Spaces.HkMem α 0 g) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)))
      = ENNReal.ofReal (Work.Spaces.HkSq α 0 g) := by
  obtain ⟨hInt, hval⟩ := hksq_eq_w2_sliceIntegral (α := α) hg
  -- Step 1: identify the `z`-integrand a.e. with `ofReal (∫θ HkIntegrand)`.
  have hae : (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici ?_
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz0 with h0 | hpos
    · subst h0
      have hw : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      have hI : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g 0 θ) = 0 := by
        simp [HkIntegrand_zero_left' α g]
      show ENNReal.ofReal ((Work.Spaces.w 0) ^ 2) *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            ((g 0 θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g 0 θ)
      rw [hw, hI]
      simp
    · exact (ofReal_slice_HkIntegrand_eq α g hpos (hg.1 z hz)).symm
  rw [MeasureTheory.lintegral_congr_ae hae]
  -- Step 2: `ofReal` of the Bochner integral of the partial `θ`-integral.
  have hInt2 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) Work.Spaces.Iz := by
    rw [MeasureTheory.IntegrableOn] at hInt ⊢
    exact hInt.congr (Filter.Eventually.of_forall fun z =>
      w2_mul_slice_eq_HkIntegrand_slice α g z)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2
    (Filter.Eventually.of_forall fun z =>
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)]
  have hgoal : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 g z θ) = Work.Spaces.HkSq α 0 g := by
    rw [← hval]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici
      (fun z _ => (w2_mul_slice_eq_HkIntegrand_slice α g z).symm)
  rw [hgoal]

end Work.FTS.EllipticEst.Honest.FOH
