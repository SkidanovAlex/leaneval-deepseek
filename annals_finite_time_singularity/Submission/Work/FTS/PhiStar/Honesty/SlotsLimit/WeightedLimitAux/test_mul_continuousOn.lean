import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux

open scoped MeasureTheory ENNReal Topology
open MeasureTheory Set Filter

/-- A continuous function on the open quadrant is bounded on the (compact) topological support of
a test function, since that support is a compact subset of the quadrant.  Multiplying the test
function by it therefore gives an integrable function on the quadrant: the product is supported
in that compact set, so its integral over `Q0` is a fortiori finite. -/
theorem test_mul_continuousOn {φ V : ℝ → ℝ → ℝ}
    (hφ : Work.FTS.PhiStar.Honesty.SlotsLimit.TestQ0 φ)
    (hV : ContinuousOn (Function.uncurry V) Work.FTS.EllipticEst.Q0) :
    IntegrableOn (fun p : ℝ × ℝ => V p.1 p.2 * φ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  set f : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => V p.1 p.2 * φ p.1 p.2 with hf_def
  change IntegrableOn f Work.FTS.EllipticEst.Q0
  set K : Set (ℝ × ℝ) := tsupport (Function.uncurry φ) with hK_def
  have hKcpt : IsCompact K := hφ.cpt
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 := hφ.tsupp
  have hKfin : volume K < ∞ := hKcpt.measure_lt_top
  have hKmeas : MeasurableSet K := hKcpt.isClosed.measurableSet
  -- a global bound for the test function
  obtain ⟨N, hN⟩ := hφ.cpt.exists_bound_of_continuous hφ.continuous
  -- a bound for `V` on the compact support of `φ`
  obtain ⟨M, hM⟩ := hKcpt.exists_bound_of_continuousOn (hV.mono hKsub)
  have hcont : ContinuousOn f K := by
    rw [hf_def]
    exact (hV.mono hKsub).mul (hφ.continuous.continuousOn.mono hKsub)
  have hAESM : AEStronglyMeasurable f (volume.restrict K) :=
    ContinuousOn.aestronglyMeasurable hcont hKmeas
  have hbnd : ∀ᵐ p ∂(volume.restrict K), ‖f p‖ ≤ |M| * |N| := by
    filter_upwards [ae_restrict_mem hKmeas] with p hp
    have h1 : ‖V p.1 p.2‖ ≤ |M| := le_trans (hM p hp) (le_abs_self M)
    have h2 : ‖φ p.1 p.2‖ ≤ |N| := le_trans (hN p) (le_abs_self N)
    rw [hf_def, norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg _)
  have hKint : IntegrableOn f K volume :=
    IntegrableOn.of_bound hKfin hAESM (|M| * |N|) hbnd
  -- `f` is supported on the compact set `K`
  have hsub : Work.FTS.EllipticEst.Q0 ∩ Function.support f ⊆ K := by
    intro p hp
    obtain ⟨-, hpsup⟩ := hp
    rw [Function.mem_support] at hpsup
    refine subset_tsupport (Function.uncurry φ) ?_
    rw [Function.mem_support]
    intro hcon
    have hcon' : φ p.1 p.2 = 0 := hcon
    exact hpsup (by
      change V p.1 p.2 * φ p.1 p.2 = 0
      rw [hcon', mul_zero])
  refine IntegrableOn.of_inter_support (Work.FTS.EllipticEst.isOpen_Q0.measurableSet) ?_
  exact hKint.mono_set hsub

end Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux
