import Mathlib
import Submission.Work.Drive.Mono.Band.HeightGoodDefs
import Submission.Work.Drive.Mono.Band.heightGood_exists_in

open scoped Topology
open TopologicalSpace

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion

/-- **A countable dense set of `HeightGood` directions.**  The condition
`Work.Drive.Mono.Band.HeightGood ψ n` (`n` is a good height direction for the sweep of the surface
`ψ`) holds on an open set and meets every non-empty open set, so the surface admits a countable dense
set of such directions.  This is step 3 of the lead's order of choices in
`Submission/Work/Drive/Mono/NOTES_LEAD_geom3Producers.md` (§1, §4.1): route I draws the witness's
kernel direction `n` from such a `Q`, which is independent of the cutting level `u`, so that the
"one event per level" clause can then be taken almost everywhere in `(u, h)`. -/
theorem exists_countable_heightGood_dense (ψ : Submission.Diffeo) :
    ∃ Q : Set LeanEval.KnotTheory.PardonDistortion.R3,
      Q.Countable ∧ (∀ n ∈ Q, Work.Drive.Mono.Band.HeightGood ψ n) ∧
      ∀ U : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen U → U.Nonempty → (U ∩ Q).Nonempty := by
  classical
  -- The set `S` of good directions meets every non-empty open set
  -- (`Work.Drive.Mono.Band.heightGood_exists_in`), hence is dense.
  set S : Set R3 := {n | Work.Drive.Mono.Band.HeightGood ψ n} with hSdef
  have hSdense : Dense S := by
    rw [dense_iff_inter_open]
    intro U hU hne
    obtain ⟨n, hnU, hng⟩ := Work.Drive.Mono.Band.heightGood_exists_in ψ hU hne
    exact ⟨n, hnU, hng⟩
  -- `S` is separable because the whole space is (second countable).
  have hSsep : IsSeparable S := by
    obtain ⟨D, hDc, hDd⟩ := exists_countable_dense R3
    exact ⟨D, hDc, by rw [hDd.closure_eq]; exact Set.subset_univ S⟩
  -- In a pseudo-metrizable space a separable set has a countable dense subset.
  obtain ⟨Q, hQS, hQc, hSQ⟩ := hSsep.exists_countable_dense_subset
  refine ⟨Q, hQc, ?_, ?_⟩
  · intro n hn
    exact hQS hn
  · -- `S ⊆ closure Q` and `S` dense make `Q` dense, which is exactly the stated clause.
    intro U hU hne
    obtain ⟨y, hyU, hyS⟩ := (dense_iff_inter_open.mp hSdense) U hU hne
    exact mem_closure_iff_nhds.mp (hSQ hyS) U (hU.mem_nhds hyU)

end Work.Drive.Mono
