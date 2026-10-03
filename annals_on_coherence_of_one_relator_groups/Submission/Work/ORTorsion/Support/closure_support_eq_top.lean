import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORTorsion.Support.exists_mapToG_eq

namespace Work.ORTorsion.Support

open Work.ORTorsion

theorem closure_support_eq_top {K : Type*} [Field K] {G : Type*} [Group G] {H : Subgroup G}
    (x : MonoidAlgebra K H)
    (hH : H = Subgroup.closure (((mapToG H x).coeff.support : Finset G) : Set G)) :
    Subgroup.closure ((x.coeff.support : Finset H) : Set H) = ⊤ := by
  classical
  have hf : Function.Injective (⇑H.subtype : H → G) := fun a b h => Subtype.ext h
  set S : Subgroup H := Subgroup.closure ((x.coeff.support : Finset H) : Set H) with hS
  have hset : (⇑H.subtype '' ((x.coeff.support : Finset H) : Set H))
      = ((mapToG H x).coeff.support : Set G) := by
    rw [coeff_mapToG]
    rw [Finsupp.mapDomain_support_of_injective hf x.coeff]
    rw [Finset.coe_image]
  have hmap : S.map H.subtype = H := by
    rw [hS, MonoidHom.map_closure, hset, ← hH]
  ext h
  simp only [Subgroup.mem_top, iff_true]
  exact (Subgroup.mem_map_iff_mem hf).mp (by rw [hmap]; exact h.2)

end Work.ORTorsion.Support
