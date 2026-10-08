import Mathlib
import Submission.Work.Dihedral.Defs
import Submission.Work.L2F.Dihedral.oddSubgroup_le_rotations
import Submission.Work.CORE4.cyclic_order_two_unique

namespace Work.CORE4

open DihedralGroup

/-- In the dihedral group `DihedralGroup n`, if `A` is a subgroup of odd order, `B` is a cyclic
subgroup and `t ∈ B` is an involution commuting with `A`, then `A` and `B` commute.

The subgroup `R = rot n` of rotations is cyclic, hence abelian, and an odd-order subgroup of a
dihedral group consists of rotations (`Work.L2F.Dihedral.oddSubgroup_le_rotations`).  So if the
given `b ∈ B` is a rotation, it commutes with `A`.  Otherwise `b = sr i` is a reflection, so
`b² = 1`; as `B` is cyclic it contains at most one element of order dividing `2`
(`Work.CORE4.cyclic_order_two_unique`), whence `b = t`, and `t` commutes with `A` by hypothesis. -/
theorem dihedral_odd_cyclic_comm {n : ℕ} (A B : Subgroup (DihedralGroup n)) (hAodd : Odd (Nat.card A))
    (hBcyc : IsCyclic B) {t : DihedralGroup n} (htB : t ∈ B) (ht : orderOf t = 2)
    (hcent : A ≤ Subgroup.centralizer ({t} : Set (DihedralGroup n))) :
    ⁅A, B⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  -- an odd-order subgroup of a dihedral group lies in the (cyclic) rotation subgroup
  have hArot : A ≤ Work.Dihedral.rot n :=
    le_trans (Work.L2F.Dihedral.oddSubgroup_le_rotations A hAodd)
      (Subgroup.zpowers_le.mpr (Work.Dihedral.r_mem_rot (1 : ZMod n)))
  have ha_rot : a ∈ Work.Dihedral.rot n := hArot ha
  by_cases hb_rot : b ∈ Work.Dihedral.rot n
  · -- both are rotations, and the rotation subgroup is cyclic hence abelian
    obtain ⟨i, rfl⟩ := Work.Dihedral.mem_rot.mp ha_rot
    obtain ⟨j, rfl⟩ := Work.Dihedral.mem_rot.mp hb_rot
    rw [r_mul_r, r_mul_r, add_comm]
  · -- `b` is a reflection; by uniqueness of the involution in the cyclic group `B`, `b = t`
    obtain ⟨i, rfl⟩ := Work.Dihedral.notMem_rot.mp hb_rot
    have hb2 : (DihedralGroup.sr i : DihedralGroup n) ^ 2 = 1 := by
      rw [← DihedralGroup.orderOf_sr i]; exact pow_orderOf_eq_one _
    have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    have ht1 : t ≠ 1 := by
      intro h; rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
    have hb1 : (DihedralGroup.sr i : DihedralGroup n) ≠ 1 := by
      intro h
      have h2 : orderOf (DihedralGroup.sr i : DihedralGroup n) = 2 := DihedralGroup.orderOf_sr i
      rw [h, orderOf_one] at h2; exact absurd h2 (by norm_num)
    have ht_eq : t = DihedralGroup.sr i :=
      cyclic_order_two_unique hBcyc htB hb ht2 hb2 ht1 hb1
    rw [← ht_eq]
    exact (Subgroup.mem_centralizer_iff.mp (hcent ha)) t (by simp)

end Work.CORE4
