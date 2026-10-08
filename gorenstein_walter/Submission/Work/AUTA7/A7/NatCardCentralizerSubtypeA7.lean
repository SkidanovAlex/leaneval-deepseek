import Mathlib

namespace Work.AUTA7.A7

/-- The centralizer in a subgroup `H ≤ G` of a set `T ⊆ H`, pushed forward along the inclusion
`H → G`, is the centralizer in `G` of the image of `T`, intersected with `H`. -/
theorem map_centralizer_subtype_eq_inf {G : Type*} [Group G] (H : Subgroup G) (T : Set H) :
    (Subgroup.centralizer T).map H.subtype = Subgroup.centralizer (H.subtype '' T) ⊓ H := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    rintro - ⟨t, ht, rfl⟩
    simpa using congrArg Subtype.val (hy t ht)
  · rintro ⟨hx, hxH⟩
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    apply Subtype.ext
    simpa using hx (H.subtype t) ⟨t, ht, rfl⟩

theorem NatCardCentralizerSubtypeA7 (z : alternatingGroup (Fin 7)) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set (alternatingGroup (Fin 7)))) =
      Nat.card ↥(Subgroup.centralizer ({(z : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))
        ⊓ alternatingGroup (Fin 7)) := by
  have h := map_centralizer_subtype_eq_inf (alternatingGroup (Fin 7))
    ({z} : Set (alternatingGroup (Fin 7)))
  rw [Set.image_singleton, Subgroup.subtype_apply] at h
  rw [← Subgroup.card_subtype (alternatingGroup (Fin 7))
      (Subgroup.centralizer ({z} : Set (alternatingGroup (Fin 7)))), h]

end Work.AUTA7.A7
