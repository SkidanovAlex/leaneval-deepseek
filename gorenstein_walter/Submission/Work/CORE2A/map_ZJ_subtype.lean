import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.OddOrder.GroupTheory.ThompsonSubgroupAbelian

namespace Work.CORE2A

open Subgroup

/-!
# `Z(J(P))` and passage to a subgroup

The image of `Z(J(P))` under the inclusion `K ↪ G` is `Z(J(P ↪ G))`.  Two ingredients:

* `thompsonJ_map_subtype` : our `thompsonJ` (the join of the abelian subgroups of maximal
  order, `Work.GW2.thompsonJ`) commutes with the map along an injective homomorphism; this is
  the odd-order library's `Subgroup.thompsonJAbelian_map_of_injective` transported across
  `thompsonJ = thompsonJAbelian`;
* `map_inf_centralizer` : for an injective `f`, `(T ⊓ C(T)).map f = T.map f ⊓ C(T.map f)`.
  This is *not* the naive `map`-commutes-with-`centralizer` statement (false in general,
  since `C_G(f(T))` can contain elements outside `f.range`); the intersection with `T.map f`
  is what makes it true.
-/

/-- Our `thompsonJ` is the odd-order library's abelian Thompson subgroup `J_a`. -/
theorem thompsonJ_eq_thompsonJAbelian' {G : Type*} [Group G] (P : Subgroup G) :
    Work.GW2.thompsonJ P = Subgroup.thompsonJAbelian P := by
  rw [Work.GW2.thompsonJ, Subgroup.thompsonJAbelian, Subgroup.maxAbelianIn, sSup_eq_iSup]

/-- **`J` is covariant under injective homomorphisms.** -/
theorem thompsonJ_map_of_injective {H N : Type*} [Group H] [Group N]
    (f : H →* N) (hf : Function.Injective f) (P : Subgroup H) :
    (Work.GW2.thompsonJ P).map f = Work.GW2.thompsonJ (P.map f) := by
  rw [thompsonJ_eq_thompsonJAbelian', thompsonJ_eq_thompsonJAbelian']
  exact (Subgroup.thompsonJAbelian_map_of_injective hf P).symm

/-- **`J` and the subgroup inclusion.** -/
theorem thompsonJ_map_subtype {G : Type} [Group G] (K : Subgroup G) (P : Subgroup ↥K) :
    (Work.GW2.thompsonJ P).map K.subtype = Work.GW2.thompsonJ (P.map K.subtype) :=
  thompsonJ_map_of_injective K.subtype K.subtype_injective P

/-- For an injective `f : H →* N` and `T ≤ H`, the image of `T ⊓ C(T)` is
`f(T) ⊓ C(f(T))`.  Injectivity of `f` is used to move commutativity back. -/
theorem map_inf_centralizer {H N : Type*} [Group H] [Group N]
    (f : H →* N) (hf : Function.Injective f) (T : Subgroup H) :
    (T ⊓ Subgroup.centralizer (T : Set H)).map f
      = T.map f ⊓ Subgroup.centralizer (T.map f : Set N) := by
  refine le_antisymm ?_ ?_
  · rintro - ⟨y, ⟨hyT, hyC⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f hyT, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro z hz
    obtain ⟨w, hwT, rfl⟩ := Subgroup.mem_map.mp hz
    have hcomm : w * y = y * w := Subgroup.mem_centralizer_iff.mp hyC w hwT
    rw [← map_mul, ← map_mul, hcomm]
  · rintro x ⟨hxT, hxC⟩
    obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp hxT
    refine Subgroup.mem_map.mpr ⟨t, ⟨htT, Subgroup.mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro s hsT
    refine hf ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hxC (f s) (Subgroup.mem_map_of_mem f hsT)

theorem map_ZJ_subtype {G : Type} [Group G] [Finite G] (K : Subgroup G) (P : Subgroup ↥K) :
    (Work.GW2.ZJ P).map K.subtype = Work.GW2.ZJ (P.map K.subtype) := by
  rw [Work.GW2.ZJ, Work.GW2.ZJ]
  rw [map_inf_centralizer K.subtype K.subtype_injective (Work.GW2.thompsonJ P)]
  rw [thompsonJ_map_subtype K P]

end Work.CORE2A
