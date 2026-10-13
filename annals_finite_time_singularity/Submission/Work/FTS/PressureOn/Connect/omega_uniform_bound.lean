import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.aeStronglyMeasurableAndBoundAtZero
import Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem omega_uniform_bound {α : NNReal} {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {T S : ℝ} (hS : S ∈ Set.Ioo 0 T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Icc 0 S, ∀ x, ‖ω x s‖ ≤ M := by
  -- The bound on the half-open interval `(0,S]` and the a.e. strong measurability of the slices.
  obtain ⟨⟨M, hM, hbdd⟩, hmeas⟩ := omegaSliceRegularPos hS hstrips hcurl
  -- Continuity in time of every curve `s ↦ ω x s` on `[0,S]`.
  have hcontω : ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc 0 S) :=
    continuousOn_time_omega_of_strips hS hstrips hcurl
  -- The time-zero slice inherits the same bound `M`.
  obtain ⟨h0, -⟩ := aeStronglyMeasurableAndBoundAtZero hS.1 hM hbdd hmeas hcontω
  refine ⟨M, hM, fun s hs x => ?_⟩
  rcases eq_or_lt_of_le hs.1 with h | h
  · rw [← h]
    exact h0 x
  · exact hbdd s ⟨h, hs.2⟩ x

end Work.FTS.PressureOn.Connect
