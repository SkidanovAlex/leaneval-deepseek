import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Cover

/-- If `X` is covered by a family of open subsets `U k`, each locally compact in the subspace
topology, then `X` itself is locally compact.

Indeed, a point `x` lies in some `U k`; since `U k` is an *open* subset of `X`, neighbourhoods
of `x` in `X` and in `U k` are related by the open embedding `↥(U k) → X`, so a compact
neighbourhood of `x` inside `U k` is also a compact neighbourhood of `x` in `X`. -/
theorem locallyCompactSpace_of_monotone_open_cover {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hopen : ∀ k, IsOpen (U k)) (hcover : (⋃ k, U k) = Set.univ)
    (hlc : ∀ k, LocallyCompactSpace ↥(U k)) : LocallyCompactSpace X := by
  refine ⟨fun x n hn => ?_⟩
  -- the point `x` lies in some `U k`
  have hxmem : x ∈ ⋃ k, U k := by rw [hcover]; exact Set.mem_univ x
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxmem
  -- transfer the neighbourhood `n` to the open subspace `↥(U k)`
  let t : Set ↥(U k) := Subtype.val ⁻¹' n
  have ht : t ∈ nhds (⟨x, hxk⟩ : ↥(U k)) := by
    rw [nhds_subtype_eq_comap]
    exact Filter.mem_comap.mpr ⟨n, hn, le_rfl⟩
  -- `U k` is locally compact, giving a compact neighbourhood of `x` inside `t`
  obtain ⟨s', hs'mem, hs'sub, hs'c⟩ :=
    (hlc k).local_compact_nhds (⟨x, hxk⟩ : ↥(U k)) t ht
  -- push the compact neighbourhood forward to `X` along the open embedding
  refine ⟨Subtype.val '' s', ?_, ?_, hs'c.image continuous_subtype_val⟩
  · exact (hopen k).isOpenEmbedding_subtypeVal.image_mem_nhds.mpr hs'mem
  · rintro y ⟨z, hz, rfl⟩
    exact hs'sub hz

end Work.Brown.Cover
