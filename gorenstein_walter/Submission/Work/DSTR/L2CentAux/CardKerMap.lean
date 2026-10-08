import Mathlib

namespace Work.DSTR.L2CentAux

/-- **Cardinality bookkeeping for a homomorphism whose kernel lies in a subgroup.**
If `f.ker ≤ K` then `|K| = |f(K)| * |ker f|` (with `Nat.card`, valid in the
infinite case too since every infinite cardinality is `0` on the relevant side).

Proof: apply `card_eq_card_quotient_mul_card_subgroup` to the restriction
`f.comp K.subtype : K →* H`, whose range is `K.map f` and whose kernel is
`K ⊓ f.ker = f.ker` (using `f.ker ≤ K`). -/
theorem CardKerMap {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (h : f.ker ≤ K) : Nat.card K = Nat.card (K.map f) * Nat.card f.ker := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ((f.comp K.subtype).ker)
  have hrange : (f.comp K.subtype).range = K.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hquot : Nat.card (↥K ⧸ (f.comp K.subtype).ker) = Nat.card (K.map f) := by
    rw [← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
  have hker_eq : Nat.card ((f.comp K.subtype).ker) = Nat.card f.ker := by
    have hcomap : (f.comp K.subtype).ker = Subgroup.comap K.subtype f.ker := by
      ext u
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_comap]
    have hmap : Subgroup.map K.subtype (Subgroup.comap K.subtype f.ker) = f.ker := by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.mpr h
    have hh := Subgroup.card_map_of_injective (K := Subgroup.comap K.subtype f.ker)
      (f := K.subtype) K.subtype_injective
    rw [hmap] at hh
    rw [hcomap]
    exact hh.symm
  rw [hquot, hker_eq] at hcard
  exact hcard

end Work.DSTR.L2CentAux
