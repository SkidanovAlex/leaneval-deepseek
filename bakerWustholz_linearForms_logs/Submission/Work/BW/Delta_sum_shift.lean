import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Abel summation (summation by parts) in the form used for the Baker–Wüstholz
Delta-function computation: with `a j = (j+1) * b j` and `b (k+1) = 0`, the
weighted telescoping sum equals the "shifted" sum. -/
theorem Delta_sum_shift {R : Type*} [CommRing R] (b : ℕ → R) (k : ℕ) (hb : b (k+1) = 0)
    (P : ℕ → R) :
    ∑ j ∈ Finset.range (k+1), b j * ((((j+1 : ℕ)) : R) * (P (j+1) - P j))
      = ∑ m ∈ Finset.range (k+2), (((m : R)) * b (m-1) - ((((m+1 : ℕ)) : R)) * b m) * P m := by
  have hL : ∑ j ∈ Finset.range (k+1), b j * ((((j+1 : ℕ)) : R) * (P (j+1) - P j))
      = (∑ j ∈ Finset.range (k+1), ((((j+1 : ℕ)) : R)) * b j * P (j+1))
        - (∑ j ∈ Finset.range (k+1), ((((j+1 : ℕ)) : R)) * b j * P j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hA : (∑ j ∈ Finset.range (k+1), ((((j+1 : ℕ)) : R)) * b j * P (j+1))
      = (∑ m ∈ Finset.range (k+2), ((m : R)) * b (m-1) * P m) := by
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.cast_zero, zero_mul, add_zero]
  have hB : (∑ j ∈ Finset.range (k+1), ((((j+1 : ℕ)) : R)) * b j * P j)
      = (∑ m ∈ Finset.range (k+2), ((((m+1 : ℕ)) : R)) * b m * P m) := by
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [hb, mul_zero, zero_mul, add_zero]
  rw [hL, hA, hB, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

end Work.BW
