import Mathlib
import Submission.Work.ConCohomology.Defs

namespace Work.ConCohomology

/-- If `G` acts trivially on `M`, the group `B¹(G,M)` of `1`-coboundaries is trivial: every
principal crossed homomorphism `σ ↦ σ•m - m` is the zero cochain. -/
lemma B1_eq_bot_of_trivial {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M]
    (htriv : ∀ (σ : G) (m : M), σ • m = m) : B1 G M = ⊥ := by
  rw [AddSubgroup.eq_bot_iff_forall]
  intro f hf
  rw [mem_B1] at hf
  obtain ⟨m, rfl⟩ := hf
  ext σ
  simp [htriv σ m]

end Work.ConCohomology
