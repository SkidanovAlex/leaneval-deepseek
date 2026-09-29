import Mathlib.Algebra.CharP.Defs
import Mathlib.Analysis.Normed.Field.Basic

namespace Commons.Analysis.Summation

open Finset

/-- Recurrence (finite-difference) identity for an arbitrary sequence `h`:
the `(m+1)`-st binomial alternating sum equals the difference of the `m`-th
binomial alternating sums shifted by one. -/
lemma sum_range_choose_succ_mul_neg_one_pow (m : ℕ) (h : ℕ → ℝ) :
    (∑ i ∈ Finset.range (m + 1 + 1), (-1 : ℝ) ^ i * (Nat.choose (m + 1) i : ℝ) * h i)
      = (∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i * (Nat.choose m i : ℝ) * h i)
        - ∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i * (Nat.choose m i : ℝ) * h (i + 1) := by
  rw [Finset.sum_range_succ (fun i => (-1 : ℝ) ^ i * (Nat.choose (m + 1) i : ℝ) * h i) (m+1),
      Finset.sum_range_succ' (fun i => (-1 : ℝ) ^ i * (Nat.choose (m + 1) i : ℝ) * h i) m,
      Finset.sum_range_succ' (fun i => (-1 : ℝ) ^ i * (Nat.choose m i : ℝ) * h i) m,
      Finset.sum_range_succ (fun i => (-1 : ℝ) ^ i * (Nat.choose m i : ℝ) * h (i + 1)) m]
  simp only [Nat.choose_self, Nat.cast_one, Nat.choose_zero_right, pow_zero, one_mul, mul_one]
  simp_rw [Nat.choose_succ_succ']
  have hsplit : ∑ k ∈ Finset.range m, (-1:ℝ)^(k+1) * ↑(m.choose k + m.choose (k+1)) * h (k+1)
      = ∑ k ∈ Finset.range m, (-1:ℝ)^(k+1) * ↑(m.choose (k+1)) * h (k+1)
        - ∑ k ∈ Finset.range m, (-1:ℝ)^k * ↑(m.choose k) * h (k+1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.cast_add, show (-1:ℝ)^(k+1) = -((-1:ℝ)^k) by rw [pow_succ]; ring]
    ring
  rw [hsplit]
  rw [show (-1:ℝ)^(m+1) = -((-1:ℝ)^m) by rw [pow_succ]; ring]
  ring

/-- Divided form of the recurrence. -/
lemma sum_choose_neg_one_pow_div_succ (x : ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1 + 1), (-1 : ℝ) ^ i * (Nat.choose (m + 1) i : ℝ) / (x + (i : ℝ)))
      = (∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i * (Nat.choose m i : ℝ) / (x + (i : ℝ)))
        - ∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i * (Nat.choose m i : ℝ) / ((x + 1) + (i : ℝ)) := by
  have h := sum_range_choose_succ_mul_neg_one_pow m (fun i => (1 : ℝ) / (x + (i : ℝ)))
  simp only [mul_one_div] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  push_cast
  ring

/-- Non-vanishing of the product `∏_{k ≤ n} (x + k)`. -/
lemma prod_range_add_ne_zero (x : ℝ) (n : ℕ) (hx : ∀ i : ℕ, i ≤ n → x + (i : ℝ) ≠ 0) :
    (∏ k ∈ Finset.range (n + 1), (x + (k : ℝ))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro a ha
  exact hx a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))

/-- `∏_{k ≤ n+1} (x+k) = (∏_{k ≤ n} (x+k)) * (x+n+1)`. -/
lemma prod_range_add_succ (x : ℝ) (n : ℕ) :
    (∏ k ∈ Finset.range (n + 1 + 1), (x + (k : ℝ)))
      = (∏ k ∈ Finset.range (n + 1), (x + (k : ℝ))) * (x + ((n + 1 : ℕ) : ℝ)) := by
  rw [Finset.prod_range_succ]

/-- `∏_{k ≤ n+1} (x+k) = x * ∏_{k ≤ n} ((x+1)+k)`. -/
lemma prod_range_add_succ' (x : ℝ) (n : ℕ) :
    (∏ k ∈ Finset.range (n + 1 + 1), (x + (k : ℝ)))
      = x * (∏ k ∈ Finset.range (n + 1), ((x + 1) + (k : ℝ))) := by
  rw [Finset.prod_range_succ', Nat.cast_zero, add_zero]
  rw [show (∏ k ∈ Finset.range (n + 1), (x + (↑(k + 1) : ℝ)))
      = (∏ k ∈ Finset.range (n + 1), ((x + 1) + (k : ℝ))) from by
    apply Finset.prod_congr rfl
    intro k _
    push_cast
    ring]
  ring

lemma sum_choose_neg_one_pow_div_add (x : ℝ) (n : ℕ)
    (hx : ∀ i : ℕ, i ≤ n → x + (i : ℝ) ≠ 0) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * (Nat.choose n i : ℝ) / (x + (i : ℝ)))
      = (n.factorial : ℝ) / ∏ k ∈ Finset.range (n + 1), (x + (k : ℝ)) := by
  induction n generalizing x with
  | zero => simp
  | succ m ih =>
    have hx0 : ∀ i : ℕ, i ≤ m → x + (i : ℝ) ≠ 0 :=
      fun i hi => hx i (Nat.le_trans hi (Nat.le_succ m))
    have hx1 : ∀ i : ℕ, i ≤ m → (x + 1) + (i : ℝ) ≠ 0 := by
      intro i hi
      have h := hx (i + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at h
      exact fun hz => h (by linarith)
    have hxn : x + ((m + 1 : ℕ) : ℝ) ≠ 0 := hx (m + 1) le_rfl
    have hxu : x ≠ 0 := by simpa using hx 0 (Nat.zero_le _)
    rw [sum_choose_neg_one_pow_div_succ x m, ih x hx0, ih (x + 1) hx1]
    have hd1 : (∏ k ∈ Finset.range (m + 1), (x + (k : ℝ))) ≠ 0 :=
      prod_range_add_ne_zero x m hx0
    have hd2 : (∏ k ∈ Finset.range (m + 1), ((x + 1) + (k : ℝ))) ≠ 0 :=
      prod_range_add_ne_zero (x + 1) m hx1
    have h3a := prod_range_add_succ x m
    have h3b := prod_range_add_succ' x m
    have hd2rel : (∏ k ∈ Finset.range (m + 1), ((x + 1) + (k : ℝ)))
        = (∏ k ∈ Finset.range (m + 1), (x + (k : ℝ))) * (x + ((m + 1 : ℕ) : ℝ)) / x := by
      rw [eq_div_iff hxu, mul_comm, ← h3b, h3a]
    rw [hd2rel, h3a]
    field_simp
    rw [Nat.factorial_succ]
    push_cast
    ring

end Commons.Analysis.Summation