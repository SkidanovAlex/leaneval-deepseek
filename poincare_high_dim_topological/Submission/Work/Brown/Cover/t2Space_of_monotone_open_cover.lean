import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Cover

open Set

/-- A space covered by an increasing sequence of open subspaces each of which is Hausdorff
is itself Hausdorff.  (Indeed the witness index can be taken to be `max a b`, using monotonicity
of the cover; the separating sets in `U (max a b)` are then pushed forward along the open
embedding `U (max a b) ↪ X`.) -/
theorem t2Space_of_monotone_open_cover {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hopen : ∀ k, IsOpen (U k)) (hmono : Monotone U) (hcover : (⋃ k, U k) = Set.univ)
    (ht2 : ∀ k, T2Space ↥(U k)) : T2Space X := by
  refine ⟨fun x y hxy => ?_⟩
  -- Every point lies in some `U k`, and by monotonicity in a common one.
  have hx : x ∈ ⋃ k, U k := by rw [hcover]; exact mem_univ x
  have hy : y ∈ ⋃ k, U k := by rw [hcover]; exact mem_univ y
  rw [Set.mem_iUnion] at hx hy
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have hxc : x ∈ U (max a b) := hmono (le_max_left a b) ha
  have hyc : y ∈ U (max a b) := hmono (le_max_right a b) hb
  have : T2Space ↥(U (max a b)) := ht2 (max a b)
  obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ :=
    t2_separation (show (⟨x, hxc⟩ : ↥(U (max a b))) ≠ ⟨y, hyc⟩ from
      fun h => hxy (Subtype.ext_iff.mp h))
  -- Push the separating open sets into `X` along the open embedding `U (max a b) ↪ X`.
  refine ⟨Subtype.val '' u, Subtype.val '' v, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hopen (max a b)).isOpenMap_subtype_val u hu
  · exact (hopen (max a b)).isOpenMap_subtype_val v hv
  · exact ⟨⟨x, hxc⟩, hxu, rfl⟩
  · exact ⟨⟨y, hyc⟩, hyv, rfl⟩
  · rw [Set.disjoint_iff_inter_eq_empty] at huv ⊢
    rw [← Set.image_inter Subtype.coe_injective, huv, Set.image_empty]

end Work.Brown.Cover
