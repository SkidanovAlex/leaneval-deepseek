import Mathlib

namespace Work.A3

open Finset

/-- Lipschitz pairing bound for one pair of consecutive blocks
`B_r = ∑_{p < (N-r)/q+1} φ(r+pq)` and `B_{r+1} = ∑_{p < (N-(r+1))/q+1} φ(r+1+pq)`.

Pairing the `i`-th term of `B_r` with the `i`-th term of `B_{r+1}` for as long as both
exist (`(N-(r+1))/q+1` terms) and using the Lipschitz bound (the two arguments differ by
exactly `1`) gives `L·((N-(r+1))/q+1)`; at most one term of `B_r` is left over, which is
bounded by `1` thanks to `hnorm`.  The number of leftover terms is exactly
`(N-r)/q+1 - ((N-(r+1))/q+1) ∈ {0,1}`. -/
lemma block_pair_bound (N q r : ℕ) (hq : 1 ≤ q) (hr : r < q - 1)
    (φ : ℝ → ℂ) (L : ℝ)
    (hlip : ∀ x ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)), ∀ y ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)),
      ‖φ x - φ y‖ ≤ L * |x - y|)
    (hnorm : ∀ x ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)), ‖φ x‖ ≤ 1) :
    ‖(∑ p ∈ Finset.range ((N - r) / q + 1), φ ((r + p * q : ℕ) : ℝ))
      - (∑ p ∈ Finset.range ((N - (r+1)) / q + 1), φ (((r+1) + p * q : ℕ) : ℝ))‖
    ≤ L * (((N - (r+1)) / q + 1 : ℕ) : ℝ)
      + (((N - r) / q + 1 - ((N - (r+1)) / q + 1) : ℕ) : ℝ) := by
  have hkey : r + (N - r) ≤ N + q := by omega
  have hmem : ∀ p : ℕ, p ≤ (N - r) / q →
      ((r + p * q : ℕ) : ℝ) ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)) ∧
      (((r+1) + p * q : ℕ) : ℝ) ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)) := by
    intro p hp
    have hpq : p * q ≤ N - r := le_trans (Nat.mul_le_mul_right q hp) (Nat.div_mul_le_self _ _)
    have hx : r + p * q ≤ N + q := by omega
    have hy : (r + 1) + p * q ≤ N + q := by omega
    exact ⟨⟨by positivity, by exact_mod_cast hx⟩, ⟨by positivity, by exact_mod_cast hy⟩⟩
  have hpair : ∀ k : ℕ, k ≤ (N - r) / q + 1 →
      ‖∑ p ∈ Finset.range k, (φ ((r + p * q : ℕ) : ℝ) - φ (((r+1) + p * q : ℕ) : ℝ))‖ ≤ L * k := by
    intro k hk
    have step : ∀ p ∈ Finset.range k,
        ‖φ ((r + p * q : ℕ) : ℝ) - φ (((r+1) + p * q : ℕ) : ℝ)‖ ≤ L := by
      intro p hp
      have hp' : p ≤ (N - r) / q := by
        have := Finset.mem_range.mp hp
        omega
      obtain ⟨hxmem, hymem⟩ := hmem p hp'
      have h := hlip _ hxmem _ hymem
      have habs : |((r + p * q : ℕ) : ℝ) - (((r+1) + p * q : ℕ) : ℝ)| = 1 := by
        have hcast : (((r+1) + p * q : ℕ) : ℝ) = ((r + p * q : ℕ) : ℝ) + 1 := by
          push_cast; ring
        rw [hcast,
          show ((r + p * q : ℕ) : ℝ) - (((r + p * q : ℕ) : ℝ) + 1) = -(1:ℝ) by ring,
          abs_neg, abs_one]
      rwa [habs, mul_one] at h
    calc ‖∑ p ∈ Finset.range k, (φ ((r + p * q : ℕ) : ℝ) - φ (((r+1) + p * q : ℕ) : ℝ))‖
        ≤ ∑ p ∈ Finset.range k, ‖φ ((r + p * q : ℕ) : ℝ) - φ (((r+1) + p * q : ℕ) : ℝ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ Finset.range k, L := Finset.sum_le_sum step
      _ = L * k := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul']
  have hcases : (N - r) / q + 1 = (N - (r+1)) / q + 1 ∨
      (N - r) / q + 1 = (N - (r+1)) / q + 1 + 1 := by
    have h1 : N - (r+1) ≤ N - r := by omega
    have h2 : (N - (r+1)) / q ≤ (N - r) / q := Nat.div_le_div_right h1
    have h3 : (N - r) / q ≤ (N - (r+1)) / q + 1 := by
      refine Nat.div_le_of_le_mul ?_
      rw [Nat.mul_add, Nat.mul_one]
      have hdm := Nat.div_add_mod (N - (r+1)) q
      have hmod := Nat.mod_lt (N - (r+1)) (by omega : 0 < q)
      omega
    omega
  rcases hcases with hcase | hcase
  · rw [hcase, Nat.sub_self, Nat.cast_zero, add_zero, ← Finset.sum_sub_distrib]
    exact hpair _ (le_of_eq hcase.symm)
  · have hB : (N - (r+1)) / q + 1 = (N - r) / q := by omega
    rw [hcase, Finset.sum_range_succ, Nat.add_sub_cancel_left, Nat.cast_one]
    have hsplit : (∑ p ∈ Finset.range ((N - (r+1)) / q + 1), φ ((r + p * q : ℕ) : ℝ))
        + φ ((r + ((N - (r+1)) / q + 1) * q : ℕ) : ℝ)
        - (∑ p ∈ Finset.range ((N - (r+1)) / q + 1), φ (((r+1) + p * q : ℕ) : ℝ))
        = (∑ p ∈ Finset.range ((N - (r+1)) / q + 1),
            (φ ((r + p * q : ℕ) : ℝ) - φ (((r+1) + p * q : ℕ) : ℝ)))
          + φ ((r + ((N - (r+1)) / q + 1) * q : ℕ) : ℝ) := by
      rw [Finset.sum_sub_distrib]; ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖∑ p ∈ Finset.range ((N - (r+1)) / q + 1),
        (φ ((r + p * q : ℕ) : ℝ) - φ (((r+1) + p * q : ℕ) : ℝ))‖
        ≤ L * ((N - (r+1)) / q + 1 : ℕ) :=
      hpair _ (by omega)
    have h2 : ‖φ ((r + ((N - (r+1)) / q + 1) * q : ℕ) : ℝ)‖ ≤ 1 := by
      have hrq : r + ((N - (r+1)) / q + 1) * q ≤ N + q := by
        rw [hB]
        have hmul := Nat.div_mul_le_self (N - r) q
        omega
      exact hnorm _ ⟨by positivity, by exact_mod_cast hrq⟩
    linarith

/-- The lengths `(N-(r+1))/q+1` sum to at most `N + q` over `r < q-1`. -/
lemma blockLenSumAux (N q : ℕ) (hq : 1 ≤ q) :
    ∑ r ∈ Finset.range (q - 1), ((N - (r + 1)) / q + 1) ≤ N + q := by
  have hterm : ∀ r ∈ Finset.range (q - 1), (N - (r + 1)) / q + 1 ≤ N / q + 1 := by
    intro r _
    exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le N (r+1))) 1
  calc ∑ r ∈ Finset.range (q - 1), ((N - (r + 1)) / q + 1)
      ≤ ∑ _r ∈ Finset.range (q - 1), (N / q + 1) := Finset.sum_le_sum hterm
    _ = (q - 1) * (N / q + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ N + q := by
        have hmul : (q - 1) * (N / q) ≤ N := by
          have h1 : (q - 1) * (N / q) ≤ q * (N / q) := Nat.mul_le_mul_right _ (Nat.sub_le q 1)
          have h2 : q * (N / q) ≤ N := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self N q
          omega
        have h3 : (q - 1) * (N / q + 1) = (q - 1) * (N / q) + (q - 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        omega

/-- The block lengths `(N-r)/q+1` are nonincreasing in `r` and drop by at most one at each
step; summing the drops over `r < q-1` therefore gives at most `1`
(a telescoping sum to `(N/q+1) - ((N-(q-1))/q+1)`). -/
lemma blockBadSumAux (N q : ℕ) (hq : 1 ≤ q) :
    ∑ r ∈ Finset.range (q - 1), ((N - r) / q + 1 - ((N - (r + 1)) / q + 1)) ≤ 1 := by
  rw [← Nat.cast_le (α := ℝ), Nat.cast_sum, Nat.cast_one]
  have hle : ∀ r, (N - (r+1)) / q + 1 ≤ (N - r) / q + 1 := by
    intro r
    exact Nat.add_le_add_right (Nat.div_le_div_right (by omega : N - (r+1) ≤ N - r)) 1
  calc ∑ r ∈ Finset.range (q - 1), (((N - r) / q + 1 - ((N - (r + 1)) / q + 1) : ℕ) : ℝ)
      = ∑ r ∈ Finset.range (q - 1),
          ((((N - r) / q + 1 : ℕ) : ℝ) - (((N - (r + 1)) / q + 1 : ℕ) : ℝ)) :=
        Finset.sum_congr rfl (fun r _ => Nat.cast_sub (hle r))
    _ = (((N - 0) / q + 1 : ℕ) : ℝ) - (((N - (q - 1)) / q + 1 : ℕ) : ℝ) :=
        Finset.sum_range_sub' (fun r => (((N - r) / q + 1 : ℕ) : ℝ)) (q - 1)
    _ ≤ 1 := by
        have hNq : N / q ≤ (N - (q-1)) / q + 1 := by
          rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < q)]
          rw [Nat.mul_add, Nat.mul_one]
          have hdm : q * ((N - (q-1)) / q) + (N - (q-1)) % q = N - (q-1) :=
            Nat.div_add_mod (N - (q-1)) q
          have hmod : (N - (q-1)) % q ≤ q - 1 := by
            have := Nat.mod_lt (N - (q-1)) (by omega : 0 < q); omega
          omega
        have hcast : ((N / q : ℕ) : ℝ) ≤ (((N - (q-1)) / q : ℕ) : ℝ) + 1 := by
          exact_mod_cast hNq
        simp only [Nat.sub_zero]
        push_cast
        linarith

/-- Total variation in `r` of the residue block sums `B_r = ∑_{p < (N-r)/q+1} φ(r+p*q)` of a Lipschitz modulus-`1` function: consecutive blocks differ by at most `P_{r+1} L` plus one unpaired term (bounded by `1` thanks to `hnorm`), and since the lengths `P_r = (N-r)/q+1` are antitone with at most one strict drop, the total is `≤ L(N+q)+3`.  (`P_{r+1} = P_r` or `P_r - 1` throughout, because `P` is nonincreasing and `P_0 - P_{q-1} ≤ 1`.) -/
lemma block_variation_bound (N q : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N)
    (φ : ℝ → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)), ∀ y ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)),
      ‖φ x - φ y‖ ≤ L * |x - y|)
    (hnorm : ∀ x ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)), ‖φ x‖ ≤ 1) :
    ∑ r ∈ Finset.range (q - 1),
        ‖(∑ p ∈ Finset.range ((N - r) / q + 1), φ ((r + p * q : ℕ) : ℝ))
          - (∑ p ∈ Finset.range ((N - (r+1)) / q + 1), φ (((r+1) + p * q : ℕ) : ℝ))‖
      ≤ L * ((N:ℝ) + (q:ℝ)) + 3 := by
  have hstep : ∀ r ∈ Finset.range (q - 1),
      ‖(∑ p ∈ Finset.range ((N - r) / q + 1), φ ((r + p * q : ℕ) : ℝ))
        - (∑ p ∈ Finset.range ((N - (r+1)) / q + 1), φ (((r+1) + p * q : ℕ) : ℝ))‖
      ≤ L * (((N - (r+1)) / q + 1 : ℕ) : ℝ)
        + (((N - r) / q + 1 - ((N - (r+1)) / q + 1) : ℕ) : ℝ) := by
    intro r hr
    exact block_pair_bound N q r hq (Finset.mem_range.mp hr) φ L hlip hnorm
  calc ∑ r ∈ Finset.range (q - 1),
        ‖(∑ p ∈ Finset.range ((N - r) / q + 1), φ ((r + p * q : ℕ) : ℝ))
          - (∑ p ∈ Finset.range ((N - (r+1)) / q + 1), φ (((r+1) + p * q : ℕ) : ℝ))‖
      ≤ ∑ r ∈ Finset.range (q - 1),
          (L * (((N - (r+1)) / q + 1 : ℕ) : ℝ)
            + (((N - r) / q + 1 - ((N - (r+1)) / q + 1) : ℕ) : ℝ)) :=
        Finset.sum_le_sum hstep
    _ = L * (∑ r ∈ Finset.range (q - 1), (((N - (r+1)) / q + 1 : ℕ) : ℝ))
          + ∑ r ∈ Finset.range (q - 1),
              (((N - r) / q + 1 - ((N - (r+1)) / q + 1) : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ L * ((N:ℝ) + (q:ℝ)) + 1 := by
        have h1 : (∑ r ∈ Finset.range (q - 1), (((N - (r+1)) / q + 1 : ℕ) : ℝ))
            ≤ (N:ℝ) + (q:ℝ) := by
          rw [← Nat.cast_sum]
          exact_mod_cast blockLenSumAux N q hq
        have h2 : (∑ r ∈ Finset.range (q - 1),
              (((N - r) / q + 1 - ((N - (r+1)) / q + 1) : ℕ) : ℝ)) ≤ 1 := by
          rw [← Nat.cast_sum]
          exact_mod_cast blockBadSumAux N q hq
        have h3 := mul_le_mul_of_nonneg_left h1 hL
        linarith
    _ ≤ L * ((N:ℝ) + (q:ℝ)) + 3 := by linarith

end Work.A3
