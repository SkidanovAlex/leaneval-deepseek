import Mathlib
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.RatHurewicz.attachIncl_isOpenMap_range
import Submission.Work.RatHurewicz.AttachRange.AttachInclInj
import Submission.Work.AttachPush.exists_homotopy_avoids_cellOrigins

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.StemsB

open Work.RatHurewicz
open scoped Topology

/-- **Compact subsets of an attachment are supported on finitely many cells and a compact piece of
`Y`.**  If `K ⊆ attachCells n Y ι f` is compact, then `K` is covered by the image of `Y` together
with the images of finitely many characteristic maps `cellMap i`, and the `Y`-part of `K` is the
image under `attachIncl` of a compact subset `K₀ ⊆ Y` that moreover contains the images of the
attaching maps of the finitely many cells used. -/
theorem descentCells (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {K : Set (Work.RatHurewicz.attachCells n Y ι f)}
    (hK : IsCompact K) :
    ∃ (J : Finset ι) (K₀ : Set Y), IsCompact K₀ ∧
      (∀ i ∈ J, Set.range (f i) ⊆ K₀) ∧
      (∀ x ∈ K, x ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)
        ∪ ⋃ i ∈ (J : Set ι), Set.range (Work.RatHurewicz.cellMap n Y ι f i)) ∧
      (∀ x ∈ K, x ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f) →
        ∃ y ∈ K₀, Work.RatHurewicz.attachIncl n Y ι f y = x) := by
  classical
  set A : Set (attachCells n Y ι f) := Set.range (attachIncl n Y ι f) with hAdef
  have hAcl : IsClosed A := by rw [hAdef]; exact isClosed_range_attachIncl
  -- the finitely many open cells that `K` meets
  have hfin : {i : ι | (K ∩ cellInterior n Y ι f i).Nonempty}.Finite :=
    Work.AttachPush.finite_meets_cellInterior n Y ι f hK
  set J : Finset ι := hfin.toFinset with hJdef
  have hJmem : ∀ i : ι, i ∈ J ↔ (K ∩ cellInterior n Y ι f i).Nonempty := by
    intro i
    simp only [hJdef, hfin.mem_toFinset, Set.mem_ofPred_eq]
  set K₀ : Set Y := (attachIncl n Y ι f ⁻¹' (K ∩ A)) ∪ ⋃ i ∈ (J : Set ι), Set.range (f i)
    with hK0def
  refine ⟨J, K₀, ?_, ?_, ?_, ?_⟩
  · -- compactness of `K₀`
    rw [hK0def]
    exact ((isInducing_attachIncl n Y ι f).isCompact_preimage hAcl (hK.inter_right hAcl)).union
      (J.finite_toSet.isCompact_biUnion fun i _ => isCompact_range (f i).continuous)
  · -- the attaching maps of the chosen cells land in `K₀`
    intro i hi
    rw [hK0def]
    exact fun x hx => Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩)
  · -- `K` is covered by the `Y`-part and the chosen cells
    intro x hxK
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · refine Or.inr ?_
      have h1 : x ∉ (⋃ i, cellInterior n Y ι f i)ᶜ := by
        intro hcon
        rw [← range_attachIncl_eq_compl_iUnion_cellInterior, ← hAdef] at hcon
        exact hxA hcon
      have hxU : x ∈ ⋃ i, cellInterior n Y ι f i := by
        by_contra hcon
        exact h1 hcon
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
      refine Set.mem_iUnion₂.mpr ⟨i, (hJmem i).mpr ⟨x, hxK, hi⟩, ?_⟩
      obtain ⟨w, -, hw⟩ := hi
      exact ⟨w, hw⟩
  · -- the `Y`-part of `K` is covered by `K₀`
    rintro x hxK hxA
    obtain ⟨y, rfl⟩ := hxA
    exact ⟨y, by rw [hK0def]; exact Or.inl ⟨hxK, ⟨y, rfl⟩⟩, rfl⟩

end Work.StemsB
