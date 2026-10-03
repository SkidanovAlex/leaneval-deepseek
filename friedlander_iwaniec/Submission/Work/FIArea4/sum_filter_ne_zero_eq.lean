import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

theorem sum_filter_ne_zero_eq (q : ℕ) [NeZero q] (F : ZMod q → ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j : ZMod q => j ≠ 0), F j
      = ∑ a ∈ Finset.Icc 1 (q - 1), F (a : ZMod q) := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hlt := ZMod.val_lt j
    have hne : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj
    simp only [Finset.mem_Icc]
    omega
  · intro j hj k hk h
    have h2 : (j.val : ZMod q) = (k.val : ZMod q) := by rw [h]
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h2
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    have hbq : b < q := by omega
    have hbne : b ≠ 0 := by omega
    have hval : ((b : ZMod q)).val = b := ZMod.val_cast_of_lt hbq
    refine ⟨(b : ZMod q), ?_, hval⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (ZMod.val_ne_zero _).mp (by rw [hval]; exact hbne)
  · intro j hj
    rw [ZMod.natCast_zmod_val]

end Work.FIArea4
