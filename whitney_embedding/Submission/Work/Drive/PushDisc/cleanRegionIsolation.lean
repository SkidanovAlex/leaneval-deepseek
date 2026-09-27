import Mathlib
import Submission.Work.Drive.PushDisc.sweptRow
import Submission.Work.Drive.PushDisc.milnorLens

/-!
# Isolation of a clean region (the general form of `exists_isolation_of_cleanDisc`)

`Work.Drive.PushDisc.exists_isolation_of_cleanDisc` (`discIsolation.lean`) splits a *ball*-shaped
disc into its open ball and its sphere.  The lens `Work.Drive.PushDisc.lensK` of the Milnor route is
not a ball (it is the parabolic cap `{|x| ≤ 1, 0 ≤ y ≤ 1 - x²}`), so this file records the same
statement for an arbitrary pair `Ko ⊆ K` of a compact region and its "interior": if the image of `Ko`
misses `g '' M` and the preimages of `D '' (K \ Ko)` lie in an open `V`, then a whole neighbourhood
of `D '' K` has its `g`-preimage in `V`.

The content is `Work.Drive.PushDisc.isolation_of_compact_anchor` (`sweptRow.lean`), applied to the
compact set `D '' K`; the dichotomy `Ko` / `K \ Ko` is the only new step.
-/

namespace Work.Drive.PushDisc

open Set Metric

/-- **Isolation of a clean compact region.**  Let `g : M → E` be continuous on a compact Hausdorff
`M`, let `D : ℝ² → E` be continuous on `K` whose image on the "interior" `Ko ⊆ K` misses `g '' M`,
and suppose that the preimages of `D '' (K \ Ko)` lie in an open `V ⊆ M`.  Then a neighbourhood of
the whole image `D '' K` has its `g`-preimage in `V`. -/
theorem exists_isolation_of_cleanRegion {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [T2Space M] {E : Type*} [PseudoMetricSpace E] [T2Space E]
    (g : M → E) (hg : Continuous g)
    (D : ℝ × ℝ → E) (K : Set (ℝ × ℝ)) (hKc : IsCompact K)
    (hDc : ContinuousOn D K)
    (Ko : Set (ℝ × ℝ)) (hKo : Ko ⊆ K)
    (hDint : D '' Ko ∩ g '' (Set.univ : Set M) = ∅)
    (V : Set M) (hVo : IsOpen V)
    (hloop : ∀ z : M, g z ∈ D '' (K \ Ko) → z ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : M, (∃ a ∈ D '' K, dist (g z) a < δ) → z ∈ V := by
  have hAc : IsCompact (D '' K) := hKc.image_of_continuousOn hDc
  have hAV : ∀ z : M, g z ∈ D '' K → z ∈ V := by
    intro z hz
    obtain ⟨p, hp, hpg⟩ := hz
    by_cases hpKo : p ∈ Ko
    · exfalso
      have hmem : g z ∈ D '' Ko ∩ g '' (Set.univ : Set M) :=
        ⟨⟨p, hpKo, hpg⟩, ⟨z, Set.mem_univ z, rfl⟩⟩
      rw [hDint] at hmem
      exact hmem
    · exact hloop z ⟨p, ⟨hp, hpKo⟩, hpg⟩
  obtain ⟨δ, hδpos, hδ⟩ := isolation_of_compact_anchor g hg V hVo (D '' K) hAc hAV
  refine ⟨δ, hδpos, fun z hz => ?_⟩
  obtain ⟨a, ha, hlt⟩ := hz
  exact hδ z a ha hlt

end Work.Drive.PushDisc
