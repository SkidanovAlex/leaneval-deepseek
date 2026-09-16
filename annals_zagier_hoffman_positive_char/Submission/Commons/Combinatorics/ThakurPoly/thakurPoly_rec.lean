import Mathlib

/-!
# The Thakur–Pascal recursion for the Thakur polynomials `b_n`

For `q ≥ 2` and a commutative ring `R` in which either `2 = 0` or `q` is odd, the Thakur
polynomials
`b_n(T) = ∑_{m} (-1)^m C(n - 1 - m(q-1), m) T^m`
satisfy the recursion
`b_n(T) = b_{n-1}(T) + (-1)^q T b_{n-q}(T)`   for `n ≥ q + 1`,
i.e. `b_n(T) = b_{n-1}(T) - T b_{n-q}(T)` in the odd case and `b_n(T) = b_{n-1}(T) + T b_{n-q}(T)`
in characteristic two.

The proof is coefficientwise: for `k ≥ 1`, Pascal's rule
`C(N+1,k) = C(N,k) + C(N,k-1)` with `N = n - 2 - k(q-1)` yields the coefficient identity, where
the sign `(-1)^q` is absorbed using `(-1)^(q-1) = 1` (true when `q` is odd, and in char. `2`).
Summing over the relevant ranges (the terms outside them vanish because the upper entry of the
binomial coefficient drops below the lower one) gives the result.
-/

namespace Commons.Combinatorics.ThakurPoly

/-- Pascal's rule for the shifted upper argument: for `k ≥ 1` and `q + 1 ≤ n` the binomial
coefficient with upper entry `(n - 2 - k(q-1)) + 1` agrees with the one with upper entry
`n - 1 - k(q-1)` (the two agree unless the upper entry has been truncated to `0`, in which case
both vanish since `k ≥ 2` there). -/
lemma thakurPoly_choose_arg (n q k : ℕ) (hq : 2 ≤ q) (hn : q + 1 ≤ n) (hk : 1 ≤ k) :
    Nat.choose ((n - 2 - k * (q - 1)) + 1) k = Nat.choose (n - 1 - k * (q - 1)) k := by
  by_cases hc : k * (q - 1) ≤ n - 2
  · have h1 : (n - 2 - k * (q - 1)) + 1 = n - 1 - k * (q - 1) := by omega
    rw [h1]
  · have hle : n - 1 ≤ k * (q - 1) := by omega
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk1 : k = 1 := by omega
      subst hk1
      simp only [one_mul] at hc
      omega
    have hz2 : n - 2 - k * (q - 1) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have hz1 : n - 1 - k * (q - 1) = 0 := Nat.sub_eq_zero_of_le hle
    rw [hz2, hz1]
    rw [Nat.choose_eq_zero_of_lt (show (0 : ℕ) + 1 < k by omega),
      Nat.choose_eq_zero_of_lt (show (0 : ℕ) < k by omega)]

/-- Index shift for the middle entries of the binomial coefficients: for `q + 1 ≤ n`,
`n - q - 1 - m(q-1) = n - 2 - (m+1)(q-1)`. -/
lemma thakurPoly_sub_shift (n q m : ℕ) (hq : 2 ≤ q) (hn : q + 1 ≤ n) :
    n - q - 1 - m * (q - 1) = n - 2 - (m + 1) * (q - 1) := by
  have h1 : (n - 2) - (q - 1) = n - q - 1 := by omega
  have h2 : (n - 2) - (m + 1) * (q - 1) = (n - 2) - (q - 1) - m * (q - 1) := by
    rw [Nat.succ_mul, ← Nat.sub_sub, Nat.sub_right_comm]
  rw [h2, h1]

/-- Vanishing of the tail coefficients: for `n + 1 - q ≤ j` the binomial coefficient
`C(n - 2 - j(q-1), j-1)` vanishes. -/
lemma thakurPoly_choose_vanish (n q j : ℕ) (hq : 2 ≤ q) (hn : q + 1 ≤ n)
    (hj : n + 1 - q ≤ j) :
    Nat.choose (n - 2 - j * (q - 1)) (j - 1) = 0 := by
  have hj2 : 2 ≤ j := by omega
  apply Nat.choose_eq_zero_of_lt
  by_cases hc : j * (q - 1) ≤ n - 2
  · have hprod : n + 1 ≤ j * q := by
      have h1 : n + 1 ≤ j + q := by omega
      have h2 : j + q ≤ j * q := Nat.add_le_mul hj2 hq
      omega
    have hq' : q = (q - 1) + 1 := by omega
    rw [hq', Nat.mul_add, Nat.mul_one] at hprod
    have hnj : n - 2 ≤ (j - 1) + j * (q - 1) := by
      have : j - 1 + (j * (q - 1) + 1) = (j - 1) + j * (q - 1) + 1 := by ring
      omega
    have hMc : n - 2 - j * (q - 1) + j * (q - 1) = n - 2 := Nat.sub_add_cancel hc
    omega
  · rw [Nat.sub_eq_zero_of_le (by omega : n - 2 ≤ j * (q - 1))]
    omega

/-- The top coefficient of the `n`-th Thakur polynomial beyond the range of the recursion:
`C(n - 2 - n(q-1), n) = 0`. -/
lemma thakurPoly_choose_n_zero (n q : ℕ) (hq : 2 ≤ q) (hn : q + 1 ≤ n) :
    Nat.choose (n - 2 - n * (q - 1)) n = 0 := by
  apply Nat.choose_eq_zero_of_lt
  by_cases hc : n * (q - 1) ≤ n - 2
  · omega
  · rw [Nat.sub_eq_zero_of_le (by omega : n - 2 ≤ n * (q - 1))]
    omega

/-- **The Thakur–Pascal recursion.** For `q ≥ 2`, a commutative ring `R` with `(2 : R) = 0` or
`q` odd, and `n ≥ q + 1`,
`b_n(T) = b_{n-1}(T) + (-1)^q T b_{n-q}(T)` where
`b_k(T) = ∑_{m} (-1)^m C(k - 1 - m(q-1), m) T^m` (truncated at `m ≤ k`). -/
theorem thakurPoly_rec {R : Type*} [CommRing R] (q : ℕ) (hq : 2 ≤ q)
    (h2 : (2 : R) = 0 ∨ Odd q) (T : R) (n : ℕ) (hn : q + 1 ≤ n) :
    (∑ m ∈ Finset.range (n + 1),
        (-1 : R) ^ m * ((Nat.choose (n - 1 - m * (q - 1)) m : ℕ) : R) * T ^ m)
      = (∑ m ∈ Finset.range n,
          (-1 : R) ^ m * ((Nat.choose (n - 2 - m * (q - 1)) m : ℕ) : R) * T ^ m)
        + (-1 : R) ^ q * T *
          (∑ m ∈ Finset.range (n + 1 - q),
            (-1 : R) ^ m * ((Nat.choose (n - q - 1 - m * (q - 1)) m : ℕ) : R) * T ^ m) := by
  have hq1 : (-1 : R) ^ (q - 1) = 1 := by
    rcases h2 with h | h
    · have hneg : (-1 : R) = 1 := by
        rw [neg_eq_iff_add_eq_zero]
        norm_num at h ⊢
        exact h
      rw [hneg, one_pow]
    · obtain ⟨k, hk⟩ := h
      have hkeq : q - 1 = 2 * k := by omega
      rw [hkeq]
      exact Even.neg_one_pow ⟨k, by ring⟩
  let A : ℕ → R := fun m => (-1 : R) ^ m * ((Nat.choose (n - 1 - m * (q - 1)) m : ℕ) : R) * T ^ m
  let B : ℕ → R := fun m => (-1 : R) ^ m * ((Nat.choose (n - 2 - m * (q - 1)) m : ℕ) : R) * T ^ m
  let C : ℕ → R := fun m => (-1 : R) ^ m * ((Nat.choose (n - q - 1 - m * (q - 1)) m : ℕ) : R) * T ^ m
  let X : ℕ → R := fun j =>
    (-1 : R) ^ j * ((Nat.choose (n - 2 - j * (q - 1)) (j - 1) : ℕ) : R) * T ^ j
  show (∑ m ∈ Finset.range (n + 1), A m)
      = (∑ m ∈ Finset.range n, B m) + (-1 : R) ^ q * T * (∑ m ∈ Finset.range (n + 1 - q), C m)
  have hpascal : ∀ k : ℕ, 1 ≤ k →
      Nat.choose (n - 1 - k * (q - 1)) k
        = Nat.choose (n - 2 - k * (q - 1)) k + Nat.choose (n - 2 - k * (q - 1)) (k - 1) := by
    intro k hk
    rw [← thakurPoly_choose_arg n q k hq hn hk]
    have h := Nat.choose_succ_succ (n - 2 - k * (q - 1)) (k - 1)
    rw [show (k - 1).succ = k by omega] at h
    exact h.trans (add_comm _ _)
  have hAB : ∀ k : ℕ, 1 ≤ k → A k = B k + X k := by
    intro k hk
    simp only [A, B, X]
    rw [hpascal k hk, Nat.cast_add]
    ring
  have hA0 : A 0 = 1 := by simp [A]
  have hB0 : B 0 = 1 := by simp [B]
  have hBn : B n = 0 := by
    simp only [B, thakurPoly_choose_n_zero n q hq hn, Nat.cast_zero, mul_zero, zero_mul]
  have hXvanish : ∀ j : ℕ, n + 1 - q ≤ j → X j = 0 := by
    intro j hj
    simp only [X, thakurPoly_choose_vanish n q j hq hn hj, Nat.cast_zero, mul_zero, zero_mul]
  have hXC : ∀ m : ℕ, m < n + 1 - q → X (m + 1) = (-1 : R) ^ q * T * C m := by
    intro m hm
    simp only [X, C]
    rw [show m + 1 - 1 = m by omega, ← thakurPoly_sub_shift n q m hq hn]
    have hsign : (-1 : R) ^ (m + 1) = (-1 : R) ^ q * (-1 : R) ^ m := by
      have h1 : (-1 : R) ^ (m + 1) * (-1 : R) ^ (q - 1) = (-1 : R) ^ q * (-1 : R) ^ m := by
        rw [← pow_add, ← pow_add, show m + 1 + (q - 1) = q + m by omega]
      simpa [hq1] using h1
    rw [hsign, pow_succ]
    ring
  have hstep2 : (∑ m ∈ Finset.range n, A (m + 1))
      = (∑ m ∈ Finset.range n, B (m + 1)) + (∑ m ∈ Finset.range n, X (m + 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun m _ => hAB (m + 1) (by omega))
  have hstep3 : A 0 + (∑ m ∈ Finset.range n, B (m + 1)) = ∑ m ∈ Finset.range (n + 1), B m := by
    rw [Finset.sum_range_succ', hA0, hB0]
    ring
  have hstep4 : (∑ m ∈ Finset.range (n + 1), B m) = ∑ m ∈ Finset.range n, B m := by
    rw [Finset.sum_range_succ, hBn]
    ring
  have hstep5 : (∑ m ∈ Finset.range n, X (m + 1))
      = ∑ m ∈ Finset.range (n + 1 - q), X (m + 1) := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x hx hxs
      simp only [Finset.mem_range] at hx hxs
      exact hXvanish (x + 1) (by omega)
  have hstep6 : (∑ m ∈ Finset.range (n + 1 - q), X (m + 1))
      = (-1 : R) ^ q * T * (∑ m ∈ Finset.range (n + 1 - q), C m) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m hm => hXC m (Finset.mem_range.mp hm))
  calc (∑ m ∈ Finset.range (n + 1), A m)
      = (∑ m ∈ Finset.range n, A (m + 1)) + A 0 := Finset.sum_range_succ' A n
    _ = ((∑ m ∈ Finset.range n, B (m + 1)) + (∑ m ∈ Finset.range n, X (m + 1))) + A 0 := by
          rw [hstep2]
    _ = (A 0 + ∑ m ∈ Finset.range n, B (m + 1)) + (∑ m ∈ Finset.range n, X (m + 1)) := by abel
    _ = (∑ m ∈ Finset.range (n + 1), B m) + (∑ m ∈ Finset.range n, X (m + 1)) := by rw [hstep3]
    _ = (∑ m ∈ Finset.range n, B m) + (∑ m ∈ Finset.range n, X (m + 1)) := by rw [hstep4]
    _ = (∑ m ∈ Finset.range n, B m) + (∑ m ∈ Finset.range (n + 1 - q), X (m + 1)) := by
          rw [hstep5]
    _ = (∑ m ∈ Finset.range n, B m)
          + (-1 : R) ^ q * T * (∑ m ∈ Finset.range (n + 1 - q), C m) := by rw [hstep6]

end Commons.Combinatorics.ThakurPoly
