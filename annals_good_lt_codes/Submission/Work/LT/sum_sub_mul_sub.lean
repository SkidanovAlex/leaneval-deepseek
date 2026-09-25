import Mathlib

namespace Work.LT

theorem sum_sub_mul_sub {ι : Type*} [Fintype ι] (f u : ι → ℝ) (a b : ℝ) :
    ∑ x, (f x - a) * (u x - b)
      = (∑ x, f x * u x) - a * (∑ x, u x) - b * (∑ x, f x)
        + a * b * (Fintype.card ι : ℝ) := by
  have h : ∀ x, (f x - a) * (u x - b) = f x * u x - a * u x - b * f x + a * b :=
    fun x => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Work.LT
