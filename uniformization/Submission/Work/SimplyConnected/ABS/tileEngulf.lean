import Mathlib

/-!
# Engulfing a compact set by finitely many members of a locally finite cover

The elementary covering step of the engulfing argument (ABS, Theorem 12): a compact set is covered by
finitely many members of a locally finite family.  This is the first step of the ABS construction: the
finite union is the compact set whose "filling" produces the exhaustion piece.
-/

open Set

noncomputable section

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X]
variable {ι : Type*} {D : ι → Set X}

/-- **A compact set is covered by finitely many members of a locally finite family.** -/
theorem exists_finset_cover_of_locallyFinite (hlf : LocallyFinite D) (hcov : (⋃ i, D i) = univ)
    {K : Set X} (hK : IsCompact K) :
    ∃ s : Finset ι, K ⊆ ⋃ i ∈ s, D i := by
  classical
  refine ⟨(hlf.finite_nonempty_inter_compact hK).toFinset, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x ∈ D i := by
    simpa only [mem_iUnion] using (show x ∈ (⋃ i, D i) from by rw [hcov]; trivial)
  exact mem_biUnion ((Set.Finite.mem_toFinset _).mpr ⟨x, hi, hx⟩) hi

end Work.SimplyConnected.ABS
