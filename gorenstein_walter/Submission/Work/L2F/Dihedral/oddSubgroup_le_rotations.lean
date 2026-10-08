import Mathlib

namespace Work.L2F.Dihedral

theorem oddSubgroup_le_rotations {n : ℕ} (Y : Subgroup (DihedralGroup n)) (hY : Odd (Nat.card Y)) :
    Y ≤ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n) := by
  intro y hy
  rcases y with i | i
  · rw [Subgroup.mem_zpowers_iff]
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective i
    exact ⟨k, by rw [DihedralGroup.r_one_zpow, hk]⟩
  · exfalso
    have h1 : orderOf (⟨DihedralGroup.sr i, hy⟩ : Y) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨DihedralGroup.sr i, hy⟩ : Y), DihedralGroup.orderOf_sr]
    have h2 : 2 ∣ Nat.card Y := by
      rw [← h1]
      exact orderOf_dvd_natCard _
    exact hY.not_two_dvd_nat h2

end Work.L2F.Dihedral
