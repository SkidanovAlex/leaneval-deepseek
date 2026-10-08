import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

set_option linter.style.haveILetI false

open Subgroup
open scoped commutatorElement

theorem centralizer_eq_of_maximal_normal_abelian {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] {A : Subgroup G} [A.Normal] (hA : IsMulCommutative A)
    (hmax : ∀ B : Subgroup G, B.Normal → IsMulCommutative B → A ≤ B → B = A) :
    Subgroup.centralizer (A : Set G) = A := by
  classical
  set C : Subgroup G := Subgroup.centralizer (A : Set G) with hC
  have hAC : A ≤ C := by
    intro a ha
    rw [hC, Subgroup.mem_centralizer_iff]
    intro b hb
    exact isMulCommutative_iff_of_setLike.mp hA b hb a ha
  refine le_antisymm ?_ hAC
  by_contra hCA
  haveI hCnormal : C.Normal := by rw [hC]; infer_instance
  set φ : G →* G ⧸ A := QuotientGroup.mk' A with hφ
  have hker : φ.ker = A := QuotientGroup.ker_mk' A
  have hCbar_ne : C.map φ ≠ ⊥ := by
    intro hbot
    have hle : C ≤ φ.ker := (Subgroup.map_eq_bot_iff C).mp hbot
    rw [hker] at hle
    exact hCA hle
  haveI hCbar_normal : (C.map φ).Normal :=
    Subgroup.Normal.map hCnormal φ (QuotientGroup.mk'_surjective A)
  have hK : C.map φ ⊓ Subgroup.center (G ⧸ A) ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hCbar_ne
  obtain ⟨zbar, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK
  have hzbarC : (zbar : G ⧸ A) ∈ C.map φ := zbar.2.1
  have hzbarZ : (zbar : G ⧸ A) ∈ Subgroup.center (G ⧸ A) := zbar.2.2
  have hzbar_ne : (zbar : G ⧸ A) ≠ 1 := fun h => hzne (Subtype.ext h)
  obtain ⟨w, hwC, hw_eq⟩ := Subgroup.mem_map.mp hzbarC
  have hw_notA : w ∉ A := by
    intro hwA
    apply hzbar_ne
    have h1 : φ w = 1 := MonoidHom.mem_ker.mp (by rw [hker]; exact hwA)
    rw [hw_eq] at h1
    exact h1
  have hcomm : ∀ g : G, ⁅g, w⁆ ∈ A := by
    intro g
    have hcentral := (Subgroup.mem_center_iff.mp hzbarZ) (φ g)
    rw [← hw_eq] at hcentral
    have hphi : φ ⁅g, w⁆ = 1 := by
      rw [commutatorElement_def]
      simp only [map_mul, map_inv]
      rw [hcentral]
      group
    have hmem : ⁅g, w⁆ ∈ φ.ker := MonoidHom.mem_ker.mpr hphi
    rwa [hker] at hmem
  set N : Subgroup G := A ⊔ Subgroup.zpowers w with hN
  have hA_le_N : A ≤ N := le_sup_left
  have hwN : w ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hN_ne_A : N ≠ A := by
    intro h
    exact hw_notA (h ▸ hwN)
  have hN_le_C : N ≤ C := by
    rw [hN]
    refine sup_le hAC ?_
    rw [Subgroup.zpowers_le]
    exact hwC
  have hconjw : ∀ g : G, g * w * g⁻¹ ∈ N := by
    intro g
    have hdecomp : g * w * g⁻¹ = ⁅g, w⁆ * w := by
      rw [commutatorElement_def]; group
    rw [hdecomp]
    exact mul_mem (hA_le_N (hcomm g)) hwN
  have hN_normal : N.Normal := by
    refine Subgroup.Normal.mk (fun x hx g => ?_)
    rw [hN, Subgroup.mem_sup_of_normal_left] at hx
    obtain ⟨a, ha, b, hb, hxb⟩ := hx
    rw [Subgroup.mem_zpowers_iff] at hb
    obtain ⟨k, hbk⟩ := hb
    rw [← hxb, ← hbk]
    have h1 : g * a * g⁻¹ ∈ N :=
      hA_le_N ((inferInstance : A.Normal).conj_mem a ha g)
    have h2 : g * w * g⁻¹ ∈ N := hconjw g
    have heq : g * (a * w ^ k) * g⁻¹ = (g * a * g⁻¹) * (g * w * g⁻¹) ^ k := by
      rw [show g * (a * w ^ k) * g⁻¹ = (MulAut.conj g) (a * w ^ k) from rfl,
        map_mul, map_zpow]
      rfl
    rw [heq]
    exact mul_mem h1 (zpow_mem h2 k)
  have hN_comm : IsMulCommutative ↥N := by
    rw [hN, Subgroup.sup_eq_closure]
    apply Subgroup.isMulCommutative_closure
    rintro x hx y hy -
    rw [Set.mem_union] at hx hy
    have hw_comm_A : ∀ a ∈ A, Commute w a := by
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp hwC a ha).symm
    rcases hx with hxA | hxw
    · rcases hy with hyA | hyw
      · exact isMulCommutative_iff_of_setLike.mp hA x hxA y hyA
      · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyw
        exact (hw_comm_A x hxA).symm.zpow_right j
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxw
      rcases hy with hyA | hyw
      · exact (hw_comm_A y hyA).zpow_left i
      · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyw
        exact ((Commute.refl w).zpow_left i).zpow_right j
  have hN_eq_A : N = A := hmax N hN_normal hN_comm hA_le_N
  exact hN_ne_A hN_eq_A

end Work.PGroup
