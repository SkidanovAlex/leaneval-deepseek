import Mathlib

namespace Work.LT

/-- Variance decomposition: subtracting the mean splits off the square of the mean. -/
theorem lr_var_decomp {X : Type} [Fintype X] (f : X → ℝ) :
    ∑ x, f x ^ 2 = (∑ x, (f x - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2)
      + ((∑ y, f y) / (Fintype.card X : ℝ)) ^ 2 * (Fintype.card X : ℝ) := by
  by_cases hcard : (Fintype.card X : ℝ) = 0
  · -- Empty index type: every sum is zero.
    have hemp : IsEmpty X := Fintype.card_eq_zero_iff.mp (Nat.cast_eq_zero.mp hcard)
    rw [Finset.univ_eq_empty_iff.mpr hemp]
    simp
  · -- Main case: the mean `m` satisfies `∑ f = n * m`.
    set n : ℝ := (Fintype.card X : ℝ) with hn
    set m : ℝ := (∑ y, f y) / n with hm
    have hne : n ≠ 0 := by rw [hn]; exact hcard
    have hmean : (∑ x, f x) = n * m := by
      rw [hm, mul_div_cancel₀ _ hne]
    -- Expand the centred squares:
    -- `∑ (f x - m)^2 = ∑ f x^2 - n * m^2`.
    have h1 : (∑ x, (f x - m) ^ 2) = ∑ x, (f x ^ 2 - 2 * m * f x + m ^ 2) :=
      Finset.sum_congr rfl (fun x _ => by ring)
    have hsum : (∑ x, (f x - m) ^ 2) = (∑ x, f x ^ 2) - n * m ^ 2 := by
      rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have h2 : (∑ x, 2 * m * f x) = 2 * m * (∑ x, f x) := by
        rw [Finset.mul_sum]
      have h3 : (∑ _x : X, m ^ 2) = n * m ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ]
        rw [nsmul_eq_mul, ← hn]
      rw [h2, h3, hmean]; ring
    rw [hsum]; ring

end Work.LT
