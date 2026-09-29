import Mathlib
import Submission.Work.Haupt.defs

/-!
# Nonvanishing of the theta-four product `T4prod` on the unit disc

`T4prod x = ∏'_{n≥0} (1 - x^{2(n+1)}) (1 - x^{2n+1})²` is the product formula for
`θ₄` in the nome `x`.  For `‖x‖ < 1` every factor is nonzero and the two products
`∏' (1 - x^{2(n+1)})` and `∏' (1 - x^{2n+1})` converge to nonzero limits, hence so does
their product (with the second squared).
-/

namespace Work.Haupt

open scoped BigOperators

theorem T4prod_ne_zero (x : ℂ) (hx : ‖x‖ < 1) : T4prod x ≠ 0 := by
  have hx2 : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  -- summability of the two exponent families
  have hs1 : Summable (fun n : ℕ => x ^ (2 * (n + 1))) := by
    have h : Summable (fun n : ℕ => (x ^ 2) ^ (n + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hx2)
    exact h.congr (fun n => by rw [pow_mul])
  have hs2 : Summable (fun n : ℕ => x ^ (2 * n + 1)) := by
    have h : Summable (fun n : ℕ => x * (x ^ 2) ^ n) :=
      (summable_geometric_of_norm_lt_one hx2).mul_left x
    exact h.congr (fun n => by rw [← pow_mul, ← pow_succ'])
  have mA2 : Multipliable (fun n : ℕ => 1 - x ^ (2 * (n + 1))) :=
    (Complex.multipliable_one_add_of_summable hs1.neg).congr (fun n => by simp [sub_eq_add_neg])
  have mD : Multipliable (fun n : ℕ => 1 - x ^ (2 * n + 1)) :=
    (Complex.multipliable_one_add_of_summable hs2.neg).congr (fun n => by simp [sub_eq_add_neg])
  -- no power of `x` equals `1`
  have key : ∀ m : ℕ, m ≠ 0 → x ^ m ≠ 1 := by
    intro m hm h1
    have hc := congrArg norm h1
    rw [norm_pow, norm_one] at hc
    have hlt : ‖x‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg x) hx hm
    rw [hc] at hlt
    exact lt_irrefl 1 hlt
  have hT4 : T4prod x
      = (∏' n : ℕ, (1 - x ^ (2 * (n + 1)))) * (∏' n : ℕ, (1 - x ^ (2 * n + 1))) ^ 2 := by
    rw [T4prod, Multipliable.tprod_mul mA2 (mD.pow 2), mD.tprod_pow 2]
  rw [hT4]
  refine mul_ne_zero ?_ (pow_ne_zero 2 ?_)
  · rw [show (∏' n : ℕ, (1 - x ^ (2 * (n + 1))))
        = ∏' n : ℕ, (1 + (-(x ^ (2 * (n + 1))))) from
      tprod_congr (fun n => by ring)]
    refine tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(x ^ (2 * (n + 1))))
      (fun n h => ?_) hs1.neg.norm
    have h1 : x ^ (2 * (n + 1)) = 1 := by
      have h' := (add_eq_zero_iff_eq_neg.mp h)
      simpa using h'.symm
    exact key (2 * (n + 1)) (by positivity) h1
  · rw [show (∏' n : ℕ, (1 - x ^ (2 * n + 1)))
        = ∏' n : ℕ, (1 + (-(x ^ (2 * n + 1)))) from
      tprod_congr (fun n => by ring)]
    refine tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(x ^ (2 * n + 1)))
      (fun n h => ?_) hs2.neg.norm
    have h1 : x ^ (2 * n + 1) = 1 := by
      have h' := (add_eq_zero_iff_eq_neg.mp h)
      simpa using h'.symm
    exact key (2 * n + 1) (by positivity) h1

end Work.Haupt
