import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.solVort_holder_strip
import Submission.Work.ConstructionInstance.solVort_integrable
import Submission.Work.ConstructionInstance.solVort_isBoundedFun
import Submission.Work.ConstructionInstance.solVort_timeHolder_Icc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- The model data satisfies the strip admissibility bundle of `Work.CoreResiduals.BSAdmissibleStrip`, for every strip with S < T. Each conjunct is a claim about the explicit field solVort P: solVort_supp gives the support, solVort_bdd together with the lower bound on the modulation gives the uniform bound, the uniform x-Hölder regularity is the dilation computation of solVort_holder (the constant is the datum constant times a power of the modulation, bounded below on the strip), solVort_timeHolder gives the time-Hölder regularity on window S which contains Icc 0 S, and the measurability comes from solVort_integrable. -/
theorem solVort_BSAdmissibleStrip {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {S : ℝ} (hS : 0 < S) (hST : S < P.T) :
    Work.CoreResiduals.BSAdmissibleStrip α (Work.ConstructionInstance.solVort P) P.R S := by
  have hp : 0 < (P.T - S) / 2 := by linarith
  -- the strip is contained in the half-window where the modulation data lives
  have hsub : ∀ t ∈ Set.Icc (0 : ℝ) S, t ∈ Work.ConstructionInstance.preWindow P.T :=
    fun t ht => ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hST⟩
  -- spatial Hölder regularity with a uniform constant
  obtain ⟨H, hH⟩ := Work.CoreResiduals.solVort_holder_strip P hS hST
  -- time-Hölder regularity with a uniform constant
  obtain ⟨N, hN0, hN⟩ :=
    Work.ConstructionInstance.solVort_timeHolder_Icc P S ⟨hS, hST⟩
  refine ⟨?_, ?_, ?_, ⟨H, hH⟩, ⟨N, ?_⟩, ?_⟩
  · linarith [P.hL, P.hRbig]
  · intro t _ht y hy
    exact Work.ConstructionInstance.solVort_supp P t y hy
  · refine ⟨P.M / ((P.T - S) / 2), fun t ht y => ?_⟩
    have hδle : (P.T - S) / 2 ≤ P.lam t := by
      have h1 := P.hlam_low t ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
      linarith [ht.2]
    exact le_trans (Work.ConstructionInstance.solVort_norm_le P (hsub t ht) y)
      (div_le_div_of_nonneg_left P.hM hp hδle)
  · intro y t ht t' ht'
    by_cases hy : y ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) P.R
    · exact hN y hy t ht t' ht'
    · have h0 : Work.ConstructionInstance.solVort P y t = 0 := by
        by_contra hne
        exact hy (Work.ConstructionInstance.solVort_supp P t y hne)
      have h0' : Work.ConstructionInstance.solVort P y t' = 0 := by
        by_contra hne
        exact hy (Work.ConstructionInstance.solVort_supp P t' y hne)
      rw [h0, h0', sub_zero, norm_zero]
      exact mul_nonneg hN0 (Real.rpow_nonneg (abs_nonneg _) _)
  · intro t ht
    exact (Work.ConstructionInstance.solVort_integrable P t (hsub t ht)).aestronglyMeasurable

end Work.CoreResiduals
