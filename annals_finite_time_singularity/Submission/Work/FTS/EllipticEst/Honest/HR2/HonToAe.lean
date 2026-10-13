/-
Copyright: work module for the Elgindi finite-time singularity project.

# `hr2_hon_to_ae` — the honest class sits inside the a.e. class

`Work.FTS.EllipticEst.Honest.Hon α F Ψ` implies `Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F`
(the two classes have the same fields, in a different order), together with the three
almost-everywhere fibre hypotheses required by `Work.FTS.EllipticEst.H2W.AeProof.AeEnergyExpl`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.HonSliceAeYc
import Submission.Work.FTS.EllipticEst.Honest.HR2.Defs
import Submission.Work.FTS.EllipticEst.Honest.HR2.Prep
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.HR2

/-- **Every honest datum is an `AeData`.** -/
theorem hon_to_ae {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) :
    Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F := by
  refine ⟨h.hα, h.hα4, h.eq, h.d0, h.dπ, h.sm, h.memF, h.memA, h.memB, ?_, ?_⟩
  · filter_upwards with z
    simpa only [Work.Elliptic.Fstar] using h.orthΨ z
  · filter_upwards with z
    simpa only [Work.Elliptic.Fstar] using h.orthF z

/-- **The a.e. fibre hypotheses of the honest class.** -/
theorem hon_ae_hyps {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) :
    (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
        ContinuousOn (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (Real.pi / 2))) ∧
      (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
        Filter.Tendsto (fun θ : ℝ => Ψ z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
      (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
        Filter.Tendsto (fun θ : ℝ => Ψ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hsl := HonSliceAeYc α F Ψ h
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hsl, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz hzpos
    refine continuousOn_Icc_of_limits (by positivity : (0 : ℝ) < Real.pi / 2)
      (hon_slice_contDiffOn h hzpos 2) (h.d0 z) (h.dπ z) hz.1 hz.2.1
  · filter_upwards [hsl] with z hz; exact hz.1
  · filter_upwards [hsl] with z hz; exact hz.2.1

end Work.FTS.EllipticEst.Honest.HR2
