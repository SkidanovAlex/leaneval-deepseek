import Mathlib.FieldTheory.Finite.Basic

namespace Commons.NumberTheory.FriedlanderIwaniec

theorem sq_roots_neg_one_mod_two_eq_one : ({α : ZMod 2 | α ^ 2 = -1}.ncard) = 1 := by
  have htwo : (2 : ZMod 2) = 0 := by
    change ((2 : ℕ) : ZMod 2) = 0
    exact ZMod.natCast_self 2
  have hneg : (-1 : ZMod 2) = 1 := by
    rw [neg_eq_iff_add_eq_zero]
    norm_num
    exact htwo
  have hset : {α : ZMod 2 | α ^ 2 = -1} = ({1} : Set (ZMod 2)) := by
    ext α
    constructor
    · intro hα
      have hsq : (α - 1) ^ 2 = 0 := by
        calc
          (α - 1) ^ 2 = α ^ 2 - 2 * α + 1 := by ring
          _ = α ^ 2 + 1 := by
            rw [htwo]
            ring
          _ = 0 := by
            rw [hα]
            exact neg_add_cancel 1
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    · intro hα
      subst α
      rw [hneg]
      norm_num
  rw [hset]
  simp

end Commons.NumberTheory.FriedlanderIwaniec