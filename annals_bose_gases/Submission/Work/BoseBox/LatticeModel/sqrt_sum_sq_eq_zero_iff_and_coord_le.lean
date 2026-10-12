import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox.LatticeModel

theorem sqrt_sum_sq_eq_zero_iff_and_coord_le {u : Fin 3 → ℝ} :
    (Real.sqrt (∑ j : Fin 3, u j ^ 2) = 0 ↔ ∀ j : Fin 3, u j = 0) ∧
    (∀ j : Fin 3, |u j| ≤ Real.sqrt (∑ j : Fin 3, u j ^ 2)) := by
  have hnonneg : 0 ≤ ∑ j : Fin 3, u j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg (u j)
  constructor
  · rw [Real.sqrt_eq_zero hnonneg]
    constructor
    · intro h j
      have hj := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (u i)).mp h j
        (Finset.mem_univ j)
      simpa using hj
    · intro h
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [h j]
  · intro j
    have hle : u j ^ 2 ≤ ∑ i : Fin 3, u i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (u i)) (Finset.mem_univ j)
    calc |u j| = Real.sqrt (u j ^ 2) := (Real.sqrt_sq_eq_abs (u j)).symm
      _ ≤ Real.sqrt (∑ i : Fin 3, u i ^ 2) := Real.sqrt_le_sqrt hle

end Work.BoseBox.LatticeModel
