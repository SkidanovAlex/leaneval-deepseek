import Mathlib

namespace Work.HP.EE

/-- Lagrange's identity for a pair of real vectors: the sum of the squared `2 × 2` minors of
`(a, b)`, summed over all *ordered* pairs of coordinates, equals twice the Gram determinant
`‖a‖²‖b‖² - ⟨a,b⟩²`. -/
lemma gram_double_sum {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∑ m : ι, ∑ m' : ι, (a m * b m' - a m' * b m) ^ 2)
      = 2 * ((∑ m : ι, a m ^ 2) * (∑ m : ι, b m ^ 2) - (∑ m : ι, a m * b m) ^ 2) := by
  have hterm : ∀ m m' : ι, (a m * b m' - a m' * b m) ^ 2
      = a m ^ 2 * b m' ^ 2 + a m' ^ 2 * b m ^ 2 - 2 * (a m * b m) * (a m' * b m') := by
    intro m m'; ring
  have hA : (∑ x : ι, ∑ x_1 : ι, a x ^ 2 * b x_1 ^ 2)
      = (∑ m : ι, a m ^ 2) * (∑ m : ι, b m ^ 2) := by
    rw [Fintype.sum_mul_sum]
  have hB : (∑ x : ι, ∑ x_1 : ι, a x_1 ^ 2 * b x ^ 2)
      = (∑ m : ι, a m ^ 2) * (∑ m : ι, b m ^ 2) := by
    rw [Finset.sum_comm]
    rw [Fintype.sum_mul_sum]
  have hC : (∑ x : ι, ∑ x_1 : ι, 2 * (a x * b x) * (a x_1 * b x_1))
      = 2 * (∑ m : ι, a m * b m) ^ 2 := by
    rw [← Fintype.sum_mul_sum]
    simp only [← Finset.mul_sum]
    rw [pow_two]
    ring
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hA, hB, hC]
  ring

end Work.HP.EE
