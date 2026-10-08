import Mathlib

open scoped BigOperators

namespace Work.PSTAB

/-- Congruence of the geometric sum modulo the element `x`: for any `x` in a ring and
any `n`, the sum `∑_{i<n} (1+x)^i` differs from the natural number `n` by a left
multiple of `x`. -/
private lemma geom_sum_eq_natCast_add {R : Type*} [Ring R] (x : R) (n : ℕ) :
    ∃ t : R, (∑ i ∈ Finset.range n, (1 + x) ^ i) = (n : R) + x * t := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + ∑ i ∈ Finset.range n, (1 + x) ^ i, ?_⟩
    have hgm : (1 + x) ^ n = 1 + x * (∑ i ∈ Finset.range n, (1 + x) ^ i) := by
      have h1 := mul_geom_sum (1 + x) n
      rw [show (1 + x) - 1 = x from by abel] at h1
      rw [h1]; abel
    calc (∑ i ∈ Finset.range (n+1), (1 + x) ^ i)
        = (∑ i ∈ Finset.range n, (1 + x) ^ i) + (1 + x) ^ n :=
            Finset.sum_range_succ (fun i => (1 + x) ^ i) n
      _ = ((n : R) + x * t) + (1 + x * (∑ i ∈ Finset.range n, (1 + x) ^ i)) := by
            rw [hgm, ht]
      _ = ((n : R) + 1) + (x * t + x * (∑ i ∈ Finset.range n, (1 + x) ^ i)) := by abel
      _ = ((n + 1 : ℕ) : R) + x * (t + ∑ i ∈ Finset.range n, (1 + x) ^ i) := by
            rw [← Nat.cast_succ, ← mul_add]

theorem NilpotentOrder {R : Type*} [Ring R] {d : R} {m : ℕ}
    (hd : IsNilpotent d) (hm : IsUnit (m : R)) (h : (1 + d) ^ m = 1) : d = 0 := by
  -- Write the geometric sum `T = ∑_{i<m} (1+d)^i` as `(m : R) + d * t`.
  obtain ⟨t, ht⟩ := geom_sum_eq_natCast_add d m
  -- `d * T = (1+d)^m - 1 = 0`, hence `(m : R) * d + d ^ 2 * t = 0`.
  have hdt : (m : R) * d + d ^ 2 * t = 0 := by
    have h1 : d * ((m : R) + d * t) = 0 := by
      have h2 := mul_geom_sum (1 + d) m
      rw [show (1 + d) - 1 = d from by abel] at h2
      rw [← ht, h2, h, sub_self]
    rw [mul_add] at h1
    rw [Nat.cast_comm, pow_two, mul_assoc]
    exact h1
  -- Descend along the nilpotency degree: from `d ^ n = 0` with `n ≥ 2` we get `d ^ (n-1) = 0`.
  rcases hd with ⟨N, hN⟩
  have key : ∀ n, d ^ n = 0 → d = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · -- `n = 0` or `n = 1`
        interval_cases n
        · simp only [pow_zero] at hn
          rw [← one_mul d, hn, zero_mul]
        · simpa using hn
      · -- multiply `(m : R) * d + d ^ 2 * t = 0` on the left by `d ^ (n-2)`
        have hB : d ^ (n - 2) * (d ^ 2 * t) = 0 := by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h2, hn, zero_mul]
        have hA : d ^ (n - 2) * ((m : R) * d) = (m : R) * d ^ (n - 1) := by
          rw [← mul_assoc, ← Nat.cast_comm m (d ^ (n - 2)), mul_assoc, ← pow_succ,
              show n - 2 + 1 = n - 1 from by omega]
        have h1 : d ^ (n - 2) * ((m : R) * d) + d ^ (n - 2) * (d ^ 2 * t) = 0 := by
          rw [← mul_add, hdt, mul_zero]
        have hmain : (m : R) * d ^ (n - 1) = 0 := by
          rw [hA, hB, add_zero] at h1
          exact h1
        have hd1 : d ^ (n - 1) = 0 :=
          hm.mul_left_cancel (by rw [hmain, mul_zero])
        exact ih (n - 1) (by omega) hd1
  exact key N hN

end Work.PSTAB
