import Mathlib

namespace Work.CORE4

/-- The set of conjugates of `y` by elements of `N` is the orbit of `y` under the
conjugation action of the subgroup `N` on `X`. -/
theorem orbit_eq_range_conj {X : Type} [Group X] (N : Subgroup X) (y : X) :
    (letI : MulAction ↥N X := MulAction.compHom X (MulAut.conj.comp N.subtype)
     MulAction.orbit ↥N y) = Set.range (fun n : ↥N => (n : X) * y * (n : X)⁻¹) := by
  ext z
  simp only [Set.mem_range, MulAction.mem_orbit_iff]
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, hn⟩

/-- The stabilizer of `y` under the conjugation action of `N` on `X` is (the image of)
the centralizer of `y` inside `N`. -/
theorem stabilizer_eq_subgroupOf_centralizer {X : Type} [Group X] (N : Subgroup X) (y : X) :
    (letI : MulAction ↥N X := MulAction.compHom X (MulAut.conj.comp N.subtype)
     MulAction.stabilizer ↥N y) = (N ⊓ Subgroup.centralizer ({y} : Set X)).subgroupOf N := by
  ext n
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAction.compHom_smul_def, MulAut.smul_def,
    MonoidHom.comp_apply, MulAut.conj_apply]
  constructor
  · intro h; exact ⟨n.2, mul_inv_eq_iff_eq_mul.mp h⟩
  · rintro ⟨_, h2⟩; exact mul_inv_eq_iff_eq_mul.mpr h2

/-- **Orbit–stabilizer for conjugation**: the number of distinct `N`-conjugates of `y`
times the cardinality of the centralizer of `y` in `N` equals `|N|`. -/
theorem ncard_range_conj_mul_card_centralizer {X : Type} [Group X] [Finite X] (N : Subgroup X) (y : X) : (Set.range (fun n : ↥N => (n : X) * y * (n : X)⁻¹)).ncard * Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set X)) = Nat.card ↥N := by
  classical
  let _ : MulAction ↥N X := MulAction.compHom X (MulAut.conj.comp N.subtype)
  have horbit := orbit_eq_range_conj N y
  have hstab := stabilizer_eq_subgroupOf_centralizer N y
  have hcard : Nat.card ↥(MulAction.stabilizer ↥N y)
      = Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set X)) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have key := Subgroup.index_mul_card (MulAction.stabilizer ↥N y)
  rw [MulAction.index_stabilizer] at key
  rw [horbit, hcard] at key
  exact key

end Work.CORE4
