import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.GW14.dihedral_map_rot
import Submission.Work.CORE2A.GW14.orderOf_two_mem_rot
import Submission.Work.CORE2A.GW14.conj_sr_r_half
import Submission.Work.CORE2A.GW14.four_dvd_of_dihedral_sylow

/-!
# CORE2A, design pass 14, leaf **W1**

For an involution `s ∈ S` with `s ≠ t` and `|S| ≥ 8`, some `w ∈ S` has `w s w⁻¹ = t s`.

Mathematical content (a pure fact about dihedral `2`-groups):

* `DihOrCycSylow G` (from `BenderCtx`) says `S` is cyclic or dihedral.  If `S` is cyclic then
  its unique involution would be both `s` and `t`, contradicting `s ≠ t`; hence `S ≅ DihedralGroup n`.
* `S₀ ≤ S` is cyclic of index `2`, and `|S| = 2n ≥ 8` with `S` a `2`-group forces `4 ∣ n` and
  `n ≥ 3` (`Work.CORE2A.GW14.four_dvd_of_dihedral_sylow`).
* Under `S ≅ DihedralGroup n` the cyclic subgroup `S₀` maps onto the rotation subgroup
  `⟨r⟩` (`Work.CORE2A.GW14.dihedral_map_rot`), so `t` maps to the unique involution `r (n/2)` of
  `⟨r⟩` (`Work.CORE2A.GW14.orderOf_two_mem_rot`) and `s` maps to a reflection `sr i`.
* In `DihedralGroup n` the rotation `r (n/4)` exists because `4 ∣ n`, and conjugating the
  reflection `sr i` by it gives `r (n/2) * sr i`
  (`Work.CORE2A.GW14.conj_sr_r_half`).  Transporting back along `S ≅ DihedralGroup n` yields `w`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

section Assembly

variable {G : Type} [Group G]

/-- **W1, general form.**  Let `S₀ ≤ S` be a cyclic subgroup of index `2`, `S ≅ DihedralGroup n`
with `4 ∣ n` and `n ≥ 3`, `t ∈ S₀` an involution and `s ∈ S ∖ S₀` an involution.  Then some
`w ∈ S` conjugates `s` to `t s`.

`t` is the unique involution of the cyclic subgroup `S₀` and `s` is a reflection, so under the
isomorphism these are `r (n/2)` and `sr i`; conjugation by the rotation `r (n/4)` (which exists
since `4 ∣ n`) realises `sr i ↦ r (n/2) · sr i`. -/
theorem exists_conj_mul_of_dihedral (n : ℕ) (hn : 3 ≤ n) (h4 : 4 ∣ n)
    (S S0 : Subgroup G) (e : S ≃* DihedralGroup n)
    (hS0 : S0 ≤ S) (hcyc : IsCyclic S0) (hidx : S0.relIndex S = 2)
    {t s : G} (ht : t ∈ S0) (ht2 : orderOf t = 2)
    (hs : s ∈ S) (hs2 : orderOf s = 2) (hss0 : s ∉ S0) :
    ∃ w ∈ S, w * s * w⁻¹ = t * s := by
  have hT := Work.CORE2A.GW14.dihedral_map_rot n hn S S0 e hS0 hcyc hidx
  -- `t` maps to `r (n/2)`.
  have htm : (⟨t, hS0 ht⟩ : ↥S) ∈ S0.subgroupOf S := by
    rw [Subgroup.mem_subgroupOf]; exact ht
  have het_mem : e ⟨t, hS0 ht⟩ ∈ Work.Dihedral.rot n := by
    rw [← hT]
    exact ⟨⟨t, hS0 ht⟩, htm, rfl⟩
  have het2 : orderOf (e ⟨t, hS0 ht⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, orderOf_mk]; exact ht2
  have het_eq : e ⟨t, hS0 ht⟩ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) :=
    Work.CORE2A.GW14.orderOf_two_mem_rot het_mem het2
  -- `s` maps to a reflection.
  have hes2 : orderOf (e ⟨s, hs⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, orderOf_mk]; exact hs2
  have hes_notmem : e ⟨s, hs⟩ ∉ Work.Dihedral.rot n := by
    intro hmem
    have heq : e ⟨s, hs⟩ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) :=
      Work.CORE2A.GW14.orderOf_two_mem_rot hmem hes2
    have hunit : (⟨s, hs⟩ : ↥S) = ⟨t, hS0 ht⟩ := e.injective (by rw [heq, het_eq])
    have hst' : s = t := congrArg Subtype.val hunit
    exact hss0 (by rw [hst']; exact ht)
  obtain ⟨i, hi⟩ := Work.Dihedral.notMem_rot.mp hes_notmem
  -- The conjugating rotation.
  obtain ⟨W, hW⟩ := Work.CORE2A.GW14.conj_sr_r_half n h4 i
  refine ⟨e.symm W, (e.symm W).2, ?_⟩
  have key : (e.symm W * ⟨s, hs⟩ * (e.symm W)⁻¹ : ↥S) = ⟨t, hS0 ht⟩ * ⟨s, hs⟩ := by
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hi, het_eq]
    exact hW
  have key2 := congrArg Subtype.val key
  simpa using key2

end Assembly

theorem c14_W1 {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (hbc : Work.GW2.BenderCtx G) (hS8 : 8 ≤ Nat.card (B.S : Subgroup G)) {s : G} (hsS : s ∈ (B.S : Subgroup G)) (hs2 : orderOf s = 2) (hst : s ≠ B.t) : ∃ w ∈ (B.S : Subgroup G), w * s * w⁻¹ = B.t * s := by
  rcases hbc.sylow B.S with hcyc | ⟨n, hiso⟩
  · -- `S` cyclic: its unique involution is both `s` and `t`.
    have : IsCyclic ↥(B.S : Subgroup G) := hcyc
    have h1 : orderOf (⟨s, hsS⟩ : ↥(B.S : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hs2
    have h2 : orderOf (⟨B.t, bSetup_t_mem_S B⟩ : ↥(B.S : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact B.t_order
    have hEq : (⟨s, hsS⟩ : ↥(B.S : Subgroup G)) = ⟨B.t, bSetup_t_mem_S B⟩ :=
      eq_of_orderOf_eq_two_of_isCyclic h1 h2
    exact absurd (show s = B.t from congrArg Subtype.val hEq) hst
  · -- `S` dihedral.
    obtain ⟨e⟩ := hiso
    obtain ⟨h4, hn3⟩ :=
      Work.CORE2A.GW14.four_dvd_of_dihedral_sylow (B.S : Subgroup G) (B.S).isPGroup' n ⟨e⟩ hS8
    -- `s ∉ S₀`: otherwise it would be the unique involution `t` of the cyclic `S₀`.
    have hs_notin : s ∉ B.S0 := by
      intro hs0
      have : IsCyclic ↥B.S0 := B.S0_cyclic
      have h1 : orderOf (⟨s, hs0⟩ : ↥B.S0) = 2 := by
        rw [Subgroup.orderOf_mk]; exact hs2
      have h2 : orderOf (⟨B.t, B.t_mem⟩ : ↥B.S0) = 2 := by
        rw [Subgroup.orderOf_mk]; exact B.t_order
      have hEq := eq_of_orderOf_eq_two_of_isCyclic h1 h2
      exact hst (congrArg Subtype.val hEq)
    exact exists_conj_mul_of_dihedral n hn3 h4 (B.S : Subgroup G) B.S0 e B.S0_le B.S0_cyclic
      B.S0_index B.t_mem B.t_order hsS hs2 hs_notin

end Work.CORE2A
