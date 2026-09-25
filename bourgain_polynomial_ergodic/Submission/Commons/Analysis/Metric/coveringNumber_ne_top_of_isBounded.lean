import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.MetricSpace.CoveringNumbers

namespace Commons.Analysis.Metric

/-- In a finite-dimensional real normed space, every bounded set has finite covering number
for every positive radius. -/
theorem coveringNumber_ne_top_of_isBounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {A : Set E} (hA : Bornology.IsBounded A) {ε : NNReal} (hε : 0 < ε) :
    Metric.coveringNumber ε A ≠ ⊤ := by
  -- A bounded set is contained in a closed ball, which is compact (hence totally bounded).
  obtain ⟨r, hr⟩ := hA.subset_closedBall (0 : E)
  have hcomp : IsCompact (Metric.closedBall (0 : E) r) := isCompact_closedBall 0 r
  have htb : TotallyBounded (Metric.closedBall (0 : E) r) := hcomp.totallyBounded
  have hδpos : (0 : ℝ) < (ε : ℝ) / 2 := by positivity
  obtain ⟨t, htf, ht⟩ :=
    (Metric.totallyBounded_iff.mp htb) ((ε : ℝ) / 2) hδpos
  have hcoe : ((ε / 2 : NNReal) : ℝ) = (ε : ℝ) / 2 := by push_cast; ring
  -- The finite set `t` is an external `ε/2`-cover of `A`.
  have hAcover : Metric.IsCover (ε / 2) A t := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]
    refine hr.trans (ht.trans ?_)
    intro x hx
    simp only [Set.mem_iUnion₂] at hx ⊢
    obtain ⟨y, hyt, hxy⟩ := hx
    refine ⟨y, hyt, ?_⟩
    rw [hcoe]
    exact Metric.ball_subset_closedBall hxy
  -- Hence the external covering number is finite.
  have hfin_ext : Metric.externalCoveringNumber (ε / 2) A ≠ ⊤ := by
    have h1 := hAcover.externalCoveringNumber_le_encard
    have hlt : Metric.externalCoveringNumber (ε / 2) A < ⊤ :=
      lt_of_le_of_lt h1 htf.encard_lt_top
    exact ne_of_lt hlt
  -- The internal covering number at radius `ε` is at most the external one at radius `ε/2`.
  have hle : Metric.coveringNumber ε A ≤ Metric.externalCoveringNumber (ε / 2) A := by
    have h := Metric.coveringNumber_two_mul_le_externalCoveringNumber (ε / 2) A
    rwa [show (2 : NNReal) * (ε / 2) = ε from by ring_nf] at h
  exact ne_of_lt (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin_ext))

end Commons.Analysis.Metric