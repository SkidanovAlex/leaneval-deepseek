import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.cyclic_index_two_center_mem
import Submission.Work.CORE2B.L27_aux
import Submission.Work.Dihedral.Defs

/-!
# AREA CORE2B — a cyclic index-two subgroup of a "dihedral" Sylow and its central involution

`dih_helper` produces, inside a Sylow `2`-subgroup `Q` of a finite group `M` that is isomorphic to
`DihedralGroup k` (`k ≥ 4`), a cyclic subgroup `T0` of index two together with its unique
involution `τ`.  This feeds `Work.CORE2B.cyclic_index_two_center_mem` and
`Work.CORE2B.center_of_cyclic_index_two`.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-- Inside a Sylow `2`-subgroup `Q` of a finite group `M` isomorphic to `DihedralGroup k`
(`k ≥ 4`) there is a cyclic subgroup `T0` of index two, whose unique involution `τ` is the
unique involution of `T0`. -/
theorem dih_helper {M : Type*} [Group M] [Finite M] {Q : Sylow 2 M} {k : ℕ} (hk : 4 ≤ k)
    (e : ↥(Q : Subgroup M) ≃* DihedralGroup k) :
    ∃ (T0 : Subgroup M) (τ : M), T0 ≤ (Q : Subgroup M) ∧ IsCyclic ↥T0 ∧
      T0.relIndex (Q : Subgroup M) = 2 ∧ τ ∈ T0 ∧ orderOf τ = 2 ∧
      (∀ y ∈ T0, orderOf y = 2 → y = τ) := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  -- `2k = |Q|` is a power of two, so `k = 2^(a-1)` is even (as `k ≥ 4`)
  obtain ⟨a, ha⟩ := Q.isPGroup'.exists_card_eq
  have hcardQ : Nat.card ↥(Q : Subgroup M) = 2 * k := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hk2 : 2 * k = 2 ^ a := by rw [← hcardQ, ha]
  have ha3 : 3 ≤ a := by
    have h8 : 2 ^ 3 ≤ 2 ^ a := by rw [← hk2]; omega
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h8
  have hk' : k = 2 ^ (a - 1) := by
    have h3 : 2 * k = 2 * 2 ^ (a - 1) := by
      rw [hk2, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ a)]
    exact Nat.mul_left_cancel (by norm_num) h3
  have hkev : Even k := by
    rw [hk', even_iff_two_dvd]
    exact dvd_pow_self 2 (by omega : a - 1 ≠ 0)
  have hhalf : k / 2 + k / 2 = k := by
    rw [← two_mul, Nat.mul_comm]
    exact Nat.div_mul_cancel (even_iff_two_dvd.mp hkev)
  -- the central involution `z` of `DihedralGroup k`
  set z : DihedralGroup k := DihedralGroup.r (((k / 2 : ℕ)) : ZMod k) with hz
  have hk2mul : k = (k / 2) * 2 := by rw [Nat.mul_comm, two_mul]; exact hhalf.symm
  have hz2 : orderOf z = 2 := by
    have hg : Nat.gcd k (k / 2) = k / 2 := Nat.gcd_eq_right ⟨2, hk2mul⟩
    rw [hz, DihedralGroup.orderOf_r,
      ZMod.val_natCast_of_lt (Nat.div_lt_self (by omega : 0 < k) (by norm_num : 1 < 2)), hg]
    nth_rewrite 1 [hk2mul]
    exact Nat.mul_div_cancel_left 2 (by omega : 0 < k / 2)
  have hzrot : z ∈ Work.Dihedral.rot k := by rw [hz]; exact Work.Dihedral.r_mem_rot _
  -- the cyclic index-two subgroup `T0'` of `Q` (preimage of the rotation subgroup)
  set T0' : Subgroup ↥(Q : Subgroup M) := (Work.Dihedral.rot k).comap e.toMonoidHom with hT0'
  have hT0'cyc : IsCyclic ↥T0' := by
    have hiso : T0' = Subgroup.zpowers (e.symm (DihedralGroup.r 1)) := by
      rw [hT0', Work.Dihedral.rot_eq_zpowers_r_one]
      ext x
      rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, by rw [← map_zpow, hn]; exact e.symm_apply_apply x⟩
      · rintro ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [← hn, map_zpow]
        congr 1
        exact (e.apply_symm_apply (DihedralGroup.r 1)).symm
    rw [hiso]
    exact Subgroup.isCyclic_zpowers _
  have hT0'idx : T0'.relIndex (⊤ : Subgroup ↥(Q : Subgroup M)) = 2 := by
    rw [hT0', Subgroup.relIndex_top_right,
      Subgroup.index_comap_of_surjective (Work.Dihedral.rot k) e.surjective]
    have h := Subgroup.card_mul_index (Work.Dihedral.rot k)
    rw [Work.Dihedral.nat_card_rot, DihedralGroup.nat_card] at h
    have h2 : k * (Work.Dihedral.rot k).index = k * 2 := by rw [h]; ring
    exact Nat.mul_left_cancel (by omega : 0 < k) h2
  have hT0'mem : e.symm z ∈ T0' := by
    rw [hT0', Subgroup.mem_comap]; simpa using hzrot
  refine ⟨T0'.map (Q : Subgroup M).subtype, ((e.symm z : ↥(Q : Subgroup M)) : M),
    Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  · -- `IsCyclic ↥T0`
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective T0' (Q : Subgroup M).subtype
        (Q : Subgroup M).subtype_injective)).mp hT0'cyc
  · -- `T0.relIndex Q = 2`
    have hsub : (Subgroup.map (Q : Subgroup M).subtype T0').subgroupOf (Q : Subgroup M) = T0' := by
      rw [← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective (Q : Subgroup M).subtype_injective T0'
    show (Subgroup.map (Q : Subgroup M).subtype T0').relIndex (Q : Subgroup M) = 2
    rw [Subgroup.relIndex, hsub]
    rw [← Subgroup.relIndex_top_right T0']
    exact hT0'idx
  · exact Subgroup.mem_map_of_mem _ hT0'mem
  · -- `orderOf τ = 2`
    have h1 : orderOf (e.symm z : ↥(Q : Subgroup M)) = 2 := by
      rw [← MulEquiv.orderOf_eq e (e.symm z)]
      rw [show e (e.symm z) = z from e.apply_symm_apply z]
      exact hz2
    simpa [Subgroup.orderOf_coe] using h1
  · -- uniqueness of the involution in `T0`
    intro y hy hy2
    obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp hy
    have hya : e y' ∈ Work.Dihedral.rot k := hy'
    have hy'2 : orderOf (⟨e y', hya⟩ : ↥(Work.Dihedral.rot k)) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨e y', hya⟩ : ↥(Work.Dihedral.rot k)), MulEquiv.orderOf_eq e y',
        ← Subgroup.orderOf_coe y', show (y' : M) = y from hyy]
      exact hy2
    have hz2' : orderOf (⟨z, hzrot⟩ : ↥(Work.Dihedral.rot k)) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨z, hzrot⟩ : ↥(Work.Dihedral.rot k))]
      exact hz2
    have hzz : (⟨e y', hya⟩ : ↥(Work.Dihedral.rot k)) = ⟨z, hzrot⟩ :=
      unique_involution_of_cyclic hy'2 hz2'
    have hz' : e y' = z := congrArg Subtype.val hzz
    rw [← show (y' : M) = y from hyy, ← hz']
    exact (congrArg Subtype.val (e.symm_apply_apply y')).symm

end Work.CORE2B
