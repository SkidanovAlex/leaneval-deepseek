import Mathlib
import Submission.Work.RED.Basic

namespace Work.RED

open Subgroup

/-- A subgroup of a cyclic group is cyclic. -/
theorem isCyclic_of_le_isCyclic {G : Type*} [Group G] {A B : Subgroup G} (hAB : A ≤ B)
    [IsCyclic ↥B] : IsCyclic ↥A := by
  haveI : IsCyclic ↥(A.subgroupOf B) := Subgroup.isCyclic (A.subgroupOf B)
  exact Work.RED.GW2.isCyclic_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAB)

theorem DihOrCycIso
    (hsub : ∀ (n : ℕ) [NeZero n] (H : Subgroup (DihedralGroup n)),
      IsCyclic ↥H ∨ ∃ m : ℕ, Nonempty (↥H ≃* DihedralGroup m))
    {G H : Type} [Group G] [Finite G] [Group H] [Finite H] (h : Work.RED.GW2.DihOrCycSylow G)
    (e : G ≃* H) : Work.RED.GW2.DihOrCycSylow H := by
  intro Q
  let Q' : Subgroup G := Subgroup.map e.symm.toMonoidHom (Q : Subgroup H)
  have hQ'e : ↥(Q : Subgroup H) ≃* ↥Q' :=
    Subgroup.equivMapOfInjective (Q : Subgroup H) e.symm.toMonoidHom e.symm.injective
  have hQ'p : IsPGroup 2 ↥Q' := IsPGroup.of_equiv Q.isPGroup' hQ'e
  obtain ⟨P, hPle⟩ := hQ'p.exists_le_sylow
  rcases h P with hcyc | ⟨m, hmd⟩
  · left
    haveI : IsCyclic ↥(P : Subgroup G) := hcyc
    have hQ'cyc : IsCyclic ↥Q' := isCyclic_of_le_isCyclic hPle
    haveI : IsCyclic ↥Q' := hQ'cyc
    exact Work.RED.GW2.isCyclic_of_mulEquiv hQ'e.symm
  · obtain ⟨em⟩ := hmd
    haveI : NeZero m := Work.RED.GW2.neZero_of_mulEquiv_dihedral em
    let KP : Subgroup ↥(P : Subgroup G) := (Q'.subgroupOf (P : Subgroup G))
    let K : Subgroup (DihedralGroup m) := Subgroup.map em.toMonoidHom KP
    have hKPle : ↥KP ≃* ↥Q' := Subgroup.subgroupOfEquivOfLe hPle
    have hKPe : ↥KP ≃* ↥K := Subgroup.equivMapOfInjective KP em.toMonoidHom em.injective
    rcases hsub m K with hKcyc | ⟨k, hkd⟩
    · left
      haveI : IsCyclic ↥K := hKcyc
      have hKPcyc : IsCyclic ↥KP := Work.RED.GW2.isCyclic_of_mulEquiv hKPe.symm
      haveI : IsCyclic ↥KP := hKPcyc
      have hQ'cyc : IsCyclic ↥Q' := Work.RED.GW2.isCyclic_of_mulEquiv hKPle
      haveI : IsCyclic ↥Q' := hQ'cyc
      exact Work.RED.GW2.isCyclic_of_mulEquiv hQ'e.symm
    · right
      obtain ⟨ek⟩ := hkd
      exact ⟨k, ⟨hQ'e.trans (hKPle.symm.trans (hKPe.trans ek))⟩⟩

end Work.RED
