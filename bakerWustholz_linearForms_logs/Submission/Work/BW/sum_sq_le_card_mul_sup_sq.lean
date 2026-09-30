import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For a number field `F`, an infinite place `w`, and any finite family `c : Fin N → F`, the sum
of the squares of the values `w (c j)` is bounded by `N` times the square of the supremum of those
values. Each value is nonnegative and bounded by the supremum, so term-wise squaring is monotone. -/
theorem sum_sq_le_card_mul_sup_sq {F : Type*} [Field F] [NumberField F] {N : ℕ}
    (w : NumberField.InfinitePlace F) (c : Fin N → F) :
    ∑ j : Fin N, (w (c j)) ^ 2 ≤ (N : ℝ) * (⨆ j : Fin N, w (c j)) ^ 2 := by
  have hle : ∀ j : Fin N, w (c j) ≤ ⨆ j : Fin N, w (c j) := fun j =>
    le_ciSup (Set.finite_range (fun j : Fin N => w (c j))).bddAbove j
  calc ∑ j : Fin N, (w (c j)) ^ 2
      ≤ ∑ _j : Fin N, (⨆ j : Fin N, w (c j)) ^ 2 :=
        Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (apply_nonneg w (c j)) (hle j) 2)
    _ = (N : ℝ) * (⨆ j : Fin N, w (c j)) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Work.BW
