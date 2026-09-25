/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `(1,0)`-derivative of the Bochner–Martinelli potential, compactly supported case

`Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord` proves
`dCoord j (bmPot f) z = Σ_k ∫ x, bmKernel k x * dCoord j (f k) (z + x)`
under the hypothesis that each `f k` vanishes outside a closed ball of radius `R > 0`.
Here we record the same statement for the *untranslated* potential
`bmPotential f z = Σ_k ∫ x, bmKernel k (x - z) * f k x` (which is `bmPot f`, see
`bmPotential_eq_bmPot`), with the equivalent hypothesis that each `f k` has compact support.
The proof is a verbatim transcription of the one in `bmCz/bmPot_dCoord.lean`: the compact
support hypothesis is exactly what `HasCompactSupport.hasFDerivAt_convolution_right` needs.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord

noncomputable section

open scoped NNReal ENNReal Convolution Topology
open MeasureTheory Set Filter

namespace Work.NN.Core

theorem bmPotential_dCoord_eq {n : ℕ} (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ 1 (f j)) (hcs : ∀ j, HasCompactSupport (f j)) (k : Fin n)
    (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord k (Work.CR.Flat.Cauchy.bmPotential f) z
      = ∑ l, ∫ x, Work.CR.Flat.Cauchy.bmKernel l x * Work.CR.Flat.dCoord k (f l) (z + x) := by
  have hcs' : ∀ l, HasCompactSupport (fderiv ℝ (f l)) :=
    fun l => Work.CR.Flat.Cauchy.bmPotDbar_hasCompactSupport_fderiv (hcs l)
  have hcont' : ∀ l, Continuous (fderiv ℝ (f l)) :=
    fun l => (hf l).continuous_fderiv (by simp)
  -- `bmPotential` is minus a sum of convolutions
  have hbmPot : Work.CR.Flat.Cauchy.bmPotential f =
      fun w => -∑ l,
        (Work.CR.Flat.Cauchy.bmKernel l ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f l) w :=
    Work.CR.Flat.Cauchy.bmPotential_eq_neg_conv f
  -- the derivative of the potential
  have hderiv : HasFDerivAt (Work.CR.Flat.Cauchy.bmPotential f)
      (-∑ l, (Work.CR.Flat.Cauchy.bmKernel l ⋆[
                ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ),
                volume] fderiv ℝ (f l)) z) z := by
    rw [hbmPot]
    refine HasFDerivAt.neg ?_
    have hsum : HasFDerivAt
        (fun w => ∑ l, (Work.CR.Flat.Cauchy.bmKernel l ⋆[
          ContinuousLinearMap.mul ℝ ℂ, volume] f l) w)
        (∑ l, (Work.CR.Flat.Cauchy.bmKernel l ⋆[ContinuousLinearMap.precompR (Fin n → ℂ)
          (ContinuousLinearMap.mul ℝ ℂ), volume] fderiv ℝ (f l)) z) z := by
      have h := HasFDerivAt.sum (u := Finset.univ) fun l _ =>
        HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
          (hcs l) (Work.CR.Flat.Cauchy.locallyIntegrable_bmKernel hn l) (hf l) z
      have hfun : (∑ l, (Work.CR.Flat.Cauchy.bmKernel l ⋆[
            ContinuousLinearMap.mul ℝ ℂ, volume] f l))
          = fun w => ∑ l, (Work.CR.Flat.Cauchy.bmKernel l ⋆[
              ContinuousLinearMap.mul ℝ ℂ, volume] f l) w := by
        funext w
        rw [Finset.sum_apply]
      rw [hfun] at h
      exact h
    exact hsum
  -- the `∂`-derivative of a single convolution
  have hval : ∀ l, Work.CR.Flat.Cauchy.bmCz.dCoordPhi k
        ((Work.CR.Flat.Cauchy.bmKernel l ⋆[
        ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ), volume]
        fderiv ℝ (f l)) z)
      = -∫ x, Work.CR.Flat.Cauchy.bmKernel l x * Work.CR.Flat.dCoord k (f l) (z + x) := by
    intro l
    have hInt : MeasureTheory.ConvolutionExistsAt (Work.CR.Flat.Cauchy.bmKernel l)
        (fderiv ℝ (f l)) z
        (ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ)) volume :=
      HasCompactSupport.convolutionExists_right
        (ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ))
        (hcs' l) (Work.CR.Flat.Cauchy.locallyIntegrable_bmKernel hn l) (hcont' l) z
    rw [MeasureTheory.convolution_def]
    rw [← ContinuousLinearMap.integral_comp_comm (Work.CR.Flat.Cauchy.bmCz.dCoordPhi k) hInt]
    have hcongr : (∫ t, Work.CR.Flat.Cauchy.bmCz.dCoordPhi k
          ((ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ))
            (Work.CR.Flat.Cauchy.bmKernel l t) (fderiv ℝ (f l) (z - t))))
        = ∫ t, Work.CR.Flat.Cauchy.bmKernel l t * Work.CR.Flat.dCoord k (f l) (z - t) := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [Work.CR.Flat.Cauchy.bmCz.dCoord_eq_comp,
        Work.CR.Flat.Cauchy.bmCz.dCoordPhi_precompR, Function.comp_apply]
    rw [hcongr]
    exact Work.CR.Flat.Cauchy.bmPotDbar_integral_flip l (Work.CR.Flat.dCoord k (f l)) z
  -- assemble
  have hcomp : Work.CR.Flat.dCoord k (Work.CR.Flat.Cauchy.bmPotential f) z
      = Work.CR.Flat.Cauchy.bmCz.dCoordPhi k
          (fderiv ℝ (Work.CR.Flat.Cauchy.bmPotential f) z) := by
    simpa only [Function.comp_apply] using
      congrFun (Work.CR.Flat.Cauchy.bmCz.dCoord_eq_comp k (Work.CR.Flat.Cauchy.bmPotential f)) z
  rw [hcomp, hderiv.fderiv]
  simp only [map_neg, map_sum, hval, Finset.sum_neg_distrib, neg_neg]

end Work.NN.Core
