import Mathlib

open scoped Pointwise

namespace Work.BSW.Cases.K4

/-- The conjugation action of a subgroup `L ≤ G` on the lattice of subgroups of `G`, given by
`l • Z = Z.map (MulAut.conj l)`.  Its orbit through a subgroup `Y` consists exactly of the
`L`-conjugates of `Y`, and its stabilizer at `Y` is `Subgroup.normalizer Y ⊓ L`. -/
instance instMulActionSubgroupConj {G : Type} [Group G] (L : Subgroup G) :
    MulAction L (Subgroup G) :=
  MulAction.compHom (Subgroup G) (MulAut.conj.comp L.subtype)

/-- The action of `instMulActionSubgroupConj` is given by applying `MulAut.conj`. -/
theorem smul_eq_map_conj {G : Type} [Group G] {L : Subgroup G} (l : L) (Z : Subgroup G) :
    l • Z = Z.map (MulAut.conj (l : G)).toMonoidHom := by
  change (MulAut.conj (l : G)) • Z = Z.map (MulAut.conj (l : G)).toMonoidHom
  rw [Subgroup.pointwise_smul_def]
  rfl

/-- The action of `instMulActionSubgroupConj` is given by applying `MulAut.conj`. -/
@[simp]
theorem smul_eq_map_conj' {G : Type} [Group G] {L : Subgroup G} (l : L) (Z : Subgroup G) :
    l • Z = Z.map (MulAut.conj (l : G)) :=
  smul_eq_map_conj l Z

end Work.BSW.Cases.K4
