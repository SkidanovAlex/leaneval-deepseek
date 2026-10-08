import Mathlib
import Submission.Work.Dihedral.Defs

namespace Work.CORE4NK

open DihedralGroup

/-- An odd-order subgroup of a dihedral group of order `2 * m` has order dividing `m`
(Lagrange plus coprimality with `2`). -/
theorem odd_card_dvd_dihedral {m : ℕ} (Y : Subgroup (DihedralGroup m)) (hY : Odd (Nat.card Y)) :
    Nat.card Y ∣ m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact dvd_zero _
  · have hmne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
    -- An odd order forces `Y` to consist of rotations: a reflection has order `2`.
    have hYle : Y ≤ Work.Dihedral.rot m := by
      intro x hx
      by_contra hxr
      obtain ⟨i, rfl⟩ := Work.Dihedral.notMem_rot.mp hxr
      have hord : orderOf (⟨sr i, hx⟩ : ↥Y) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨sr i, hx⟩ : ↥Y)]
        exact DihedralGroup.orderOf_sr i
      have h2 : (2 : ℕ) ∣ Nat.card ↥Y := by
        rw [← hord]
        exact orderOf_dvd_natCard _
      rcases hY with ⟨k, hk⟩
      omega
    -- Lagrange inside the (cyclic) rotation subgroup, whose order is `m`.
    have hdvd : Nat.card ↥(Y.subgroupOf (Work.Dihedral.rot m)) ∣
        Nat.card ↥(Work.Dihedral.rot m) :=
      Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv] at hdvd
    rw [@Work.Dihedral.nat_card_rot m ⟨hmne⟩] at hdvd
    exact hdvd

end Work.CORE4NK
