import Mathlib

namespace Work.CohomologicalShrinking.group

/-- If two subgroups `U` and `V` of a group are abelian and commute with each other, then the
subgroup they generate is abelian, i.e. its commutator subgroup is trivial. -/
theorem commutator_sup_eq_bot {G : Type*} [Group G] {U V : Subgroup G}
    (hU : ⁅U, U⁆ = ⊥) (hUV : ⁅U, V⁆ = ⊥) (hV : ⁅V, V⁆ = ⊥) :
    ⁅U ⊔ V, U ⊔ V⁆ = ⊥ := by
  rw [Subgroup.commutator_self_eq_bot_iff]
  have hcl : Subgroup.closure ((U : Set G) ∪ (V : Set G)) = U ⊔ V := by
    rw [Subgroup.sup_eq_closure]
  rw [← hcl]
  apply Subgroup.isMulCommutative_closure
  intro x hx y hy _
  rw [Set.mem_union] at hx hy
  have hU' : U ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hU
  have hUV' : U ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUV
  have hV' : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hV
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (Subgroup.mem_centralizer_iff.mp (hU' hx) y hy).symm
  · exact (Subgroup.mem_centralizer_iff.mp (hUV' hx) y hy).symm
  · exact Subgroup.mem_centralizer_iff.mp (hUV' hy) x hx
  · exact (Subgroup.mem_centralizer_iff.mp (hV' hx) y hy).symm

theorem commutator_sup_le_of_le {P : Type*} [Group P] {K A B : Subgroup P} [K.Normal]
    (hAA : ⁅A, A⁆ ≤ K) (hAB : ⁅A, B⁆ ≤ K) (hBB : ⁅B, B⁆ ≤ K) :
    ⁅A ⊔ B, A ⊔ B⁆ ≤ K := by
  set f : P →* P ⧸ K := QuotientGroup.mk' K with hf
  have hker : f.ker = K := by rw [hf, QuotientGroup.ker_mk']
  have key : (⁅A ⊔ B, A ⊔ B⁆).map f = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.map_sup]
    apply commutator_sup_eq_bot
    · have h1 : (⁅A, A⁆).map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by rw [hker]; exact hAA)
      rwa [Subgroup.map_commutator] at h1
    · have h1 : (⁅A, B⁆).map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by rw [hker]; exact hAB)
      rwa [Subgroup.map_commutator] at h1
    · have h1 : (⁅B, B⁆).map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by rw [hker]; exact hBB)
      rwa [Subgroup.map_commutator] at h1
  rwa [Subgroup.map_eq_bot_iff, hker] at key

end Work.CohomologicalShrinking.group
