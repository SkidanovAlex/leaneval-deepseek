import Mathlib

namespace Work.HP

/-- Crux inequality: multiplying the partial sum `∑_{k ≤ n} ∏_{m<k} a m` by `a n`
is bounded by the sum extended to `n+1`.  Uses antitonicity of `a` to dominate
`a n · ∏_{m<k} a m ≤ ∏_{m≤k} a m` for every `k ≤ n`. -/
lemma a_mul_sum_le_sum_succ (a : ℕ → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (ha : ∀ i j, i ≤ j → a j ≤ a i) (n : ℕ) :
    a n * (∑ k ∈ Finset.range (n + 1), ∏ m ∈ Finset.range k, a m) ≤
      ∑ k ∈ Finset.range (n + 1 + 1), ∏ m ∈ Finset.range k, a m := by
  have hP : ∀ k, (0:ℝ) ≤ ∏ m ∈ Finset.range k, a m :=
    fun k => Finset.prod_nonneg (fun m _ => ha0 m)
  rw [Finset.mul_sum]
  have step : ∀ k ∈ Finset.range (n + 1),
      a n * (∏ m ∈ Finset.range k, a m) ≤ ∏ m ∈ Finset.range (k + 1), a m := by
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have han : a n ≤ a k := ha k n hk'
    rw [Finset.prod_range_succ]
    nlinarith [hP k, mul_le_mul_of_nonneg_right han (hP k)]
  calc ∑ k ∈ Finset.range (n + 1), a n * (∏ m ∈ Finset.range k, a m)
      ≤ ∑ k ∈ Finset.range (n + 1), ∏ m ∈ Finset.range (k + 1), a m :=
        Finset.sum_le_sum step
    _ ≤ ∑ k ∈ Finset.range (n + 1 + 1), ∏ m ∈ Finset.range k, a m := by
        conv_rhs => rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right (hP 0)

theorem prod_one_add_le_sum_prod (a : ℕ → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (ha : ∀ i j, i ≤ j → a j ≤ a i) :
    ∀ R : ℕ, ∏ i ∈ Finset.range R, (1 + a i) ≤
      (2 : ℝ) ^ R * ∑ k ∈ Finset.range (R + 1), ∏ m ∈ Finset.range k, a m := by
  have hP : ∀ k, (0:ℝ) ≤ ∏ m ∈ Finset.range k, a m :=
    fun k => Finset.prod_nonneg (fun m _ => ha0 m)
  intro R
  induction R with
  | zero => simp
  | succ n ih =>
    show ∏ i ∈ Finset.range (n + 1), (1 + a i) ≤
      (2 : ℝ) ^ (n + 1) * ∑ k ∈ Finset.range (n + 1 + 1), ∏ m ∈ Finset.range k, a m
    have hstep : (1 + a n) * (∑ k ∈ Finset.range (n + 1), ∏ m ∈ Finset.range k, a m)
        ≤ 2 * (∑ k ∈ Finset.range (n + 1 + 1), ∏ m ∈ Finset.range k, a m) := by
      have hkey := a_mul_sum_le_sum_succ a ha0 ha n
      have hGn : (∑ k ∈ Finset.range (n + 1), ∏ m ∈ Finset.range k, a m)
          ≤ (∑ k ∈ Finset.range (n + 1 + 1), ∏ m ∈ Finset.range k, a m) := by
        conv_rhs => rw [Finset.sum_range_succ]
        exact le_add_of_nonneg_right (hP (n + 1))
      nlinarith [hkey, hGn]
    calc ∏ i ∈ Finset.range (n + 1), (1 + a i)
        = (∏ i ∈ Finset.range n, (1 + a i)) * (1 + a n) :=
          Finset.prod_range_succ (fun i => 1 + a i) n
      _ ≤ (2 ^ n * ∑ k ∈ Finset.range (n + 1), ∏ m ∈ Finset.range k, a m) * (1 + a n) := by
          exact mul_le_mul_of_nonneg_right ih (by linarith [ha0 n])
      _ = 2 ^ n * ((1 + a n) * ∑ k ∈ Finset.range (n + 1), ∏ m ∈ Finset.range k, a m) := by ring
      _ ≤ 2 ^ n * (2 * ∑ k ∈ Finset.range (n + 1 + 1), ∏ m ∈ Finset.range k, a m) := by
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 2 ^ (n + 1) * ∑ k ∈ Finset.range (n + 1 + 1), ∏ m ∈ Finset.range k, a m := by
          rw [pow_succ]; ring

end Work.HP
