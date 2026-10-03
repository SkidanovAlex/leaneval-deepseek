import Mathlib
import Submission.Work.ORReductions.OneRelator.oneRelatorFreeFactorAlt
import Submission.Work.ORReductions.Coherent.coherentOfFiniteSubgroupsAlt
import Submission.Work.ORReductions.Coherent.coherent_of_ringEquiv

namespace Work.ORReductions.OneRelator

open Work.ORReductions.Coherent

/-- Reduction of the coherence of `K[G]`, `G` a one-relator group, to the finitely generated
one-relator groups `PresentedGroup {r}` with `r ∈ FreeGroup (Fin n)`.

Every finite subset of `G` is contained in a subgroup `H` which is (isomorphic to) the image of
such a finitely generated one-relator group inside a free factor of `G`; coherence of `K[G]` then
follows from the finite-subgroup criterion for coherence (`coherent_of_finite_subgroups_alt`),
the finite subset being supplied by `oneRelator_freeFactor_alt` and the isomorphism of group
algebras by `MonoidAlgebra.mapDomainRingEquiv` together with `coherent_of_ringEquiv`. -/
theorem coherent_of_oneRelator_of_fg (G : Type*) [Group G] (K : Type*) [Field K]
    (hG : Group.OneRelator G)
    (h : ∀ (n : ℕ) (r : FreeGroup (Fin n)), Ring.Coherent (MonoidAlgebra K (PresentedGroup {r}))) :
    Ring.Coherent (MonoidAlgebra K G) := by
  refine coherent_of_finite_subgroups_alt G K ?_
  intro s
  obtain ⟨n, r, H, T, hs, ⟨e⟩, -⟩ := oneRelator_freeFactor_alt G hG s
  exact ⟨H, hs, coherent_of_ringEquiv (MonoidAlgebra.mapDomainRingEquiv K e) (h n r)⟩

end Work.ORReductions.OneRelator
