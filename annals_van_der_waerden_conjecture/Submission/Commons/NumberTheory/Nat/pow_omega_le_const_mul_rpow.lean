import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sub-polynomial growth of `a ^ ω(n)`

We prove that for every real `a ≥ 0` and every `ε > 0` the quantity `a ^ ω(n)`
(where `ω(n) = n.primeFactors.card` is the number of distinct prime divisors of `n`)
is bounded by `C * n ^ ε` for a suitable constant `C > 0`.

The proof rests on the elementary lower bound
`(ω(n) + 1)! ≤ ∏_{p ∣ n} p ≤ n` (the product of the distinct prime factors of `n`
is at least `(ω(n) + 1)!`, hence divides `n`), together with the fact that the
factorial grows faster than any exponential.
-/

open Finset

namespace Commons.NumberTheory.Nat

/-- If every element of a finite set `s` of naturals is at least `2`, then the product
of the elements of `s` is at least `(card s + 1)!`. -/
theorem factorial_card_succ_le_prod (s : Finset ℕ) (hs : ∀ x ∈ s, 2 ≤ x) :
    (s.card + 1).factorial ≤ ∏ x ∈ s, x := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
      have ha_notin : a ∉ s := fun h => absurd (hlt a h) (lt_irrefl a)
      have hs2 : ∀ x ∈ s, 2 ≤ x := fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have ha2 : 2 ≤ a := hs a (Finset.mem_insert_self a s)
      rw [Finset.card_insert_of_notMem ha_notin, Finset.prod_insert ha_notin]
      have hih := ih hs2
      -- every element of `s` lies in `{2, …, a-1}`, so `s.card + 2 ≤ a`
      have hsub : s ⊆ Finset.Icc 2 (a - 1) := by
        intro x hx
        rw [Finset.mem_Icc]
        exact ⟨hs2 x hx, Nat.le_sub_one_of_lt (hlt x hx)⟩
      have hcard : s.card ≤ a - 2 := by
        have h1 : s.card ≤ (Finset.Icc 2 (a - 1)).card := Finset.card_le_card hsub
        rw [Nat.card_Icc] at h1
        omega
      have hk2 : s.card + 2 ≤ a := by omega
      have step1 : (s.card + 2).factorial ≤ a * (s.card + 1).factorial := by
        rw [show s.card + 2 = (s.card + 1) + 1 from by omega, Nat.factorial_succ]
        exact Nat.mul_le_mul_right _ hk2
      have step2 : a * (s.card + 1).factorial ≤ a * ∏ x ∈ s, x := Nat.mul_le_mul_left a hih
      have hEq : ((s.card + 1) + 1).factorial = (s.card + 2).factorial := by ring_nf
      rw [hEq]
      exact le_trans step1 step2

/-- For `n ≥ 1` we have `(ω(n) + 1)! ≤ n`, where `ω(n) = n.primeFactors.card`. -/
theorem factorial_card_primeFactors_le (n : ℕ) (hn : 1 ≤ n) :
    (n.primeFactors.card + 1).factorial ≤ n := by
  have hs : ∀ x ∈ n.primeFactors, 2 ≤ x := fun x hx => (Nat.prime_of_mem_primeFactors hx).two_le
  have h1 := factorial_card_succ_le_prod n.primeFactors hs
  have h2 : ∏ p ∈ n.primeFactors, p ≤ n :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
  exact le_trans h1 h2

/-- For every real `b ≥ 1` there is `N` such that `b ^ k ≤ b ^ N * (k+1)!` for all `k`. -/
theorem pow_le_factorial_mul (b : ℝ) (hb : 1 ≤ b) :
    ∃ N : ℕ, ∀ k : ℕ, b ^ k ≤ b ^ N * (((k + 1).factorial : ℕ) : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge b
  refine ⟨N, ?_⟩
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  have hbN0 : 0 < b ^ N := pow_pos hb0 N
  have hfac1 : ∀ k : ℕ, (1 : ℝ) ≤ (((k + 1).factorial : ℕ) : ℝ) := by
    intro k
    have : 0 < ((k + 1).factorial : ℕ) := Nat.factorial_pos _
    exact_mod_cast this
  have main : ∀ k : ℕ, N ≤ k → b ^ k ≤ b ^ N * (((k + 1).factorial : ℕ) : ℝ) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_mul_of_one_le_right (le_of_lt hbN0) (hfac1 N)
    | succ k hk ih =>
        have hk2 : b ≤ (k : ℝ) + 2 := by
          have h1 : b ≤ (N : ℝ) := hN
          have h2 : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          linarith
        have hfacstep : b * (((k + 1).factorial : ℕ) : ℝ) ≤ (((k + 2).factorial : ℕ) : ℝ) := by
          rw [show (((k + 2).factorial : ℕ) : ℝ)
                = ((k : ℝ) + 2) * (((k + 1).factorial : ℕ) : ℝ) by
                rw [show k + 2 = (k + 1) + 1 from by omega, Nat.factorial_succ]
                push_cast; ring]
          exact mul_le_mul_of_nonneg_right hk2 (by positivity)
        calc b ^ (k + 1) = b ^ k * b := by rw [pow_succ]
          _ ≤ (b ^ N * (((k + 1).factorial : ℕ) : ℝ)) * b :=
                mul_le_mul_of_nonneg_right ih (le_of_lt hb0)
          _ = b ^ N * (b * (((k + 1).factorial : ℕ) : ℝ)) := by ring
          _ ≤ b ^ N * (((k + 2).factorial : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_left hfacstep (le_of_lt hbN0)
  intro k
  rcases lt_or_ge k N with h | h
  · have h1 : b ^ k ≤ b ^ N := pow_le_pow_right₀ hb (le_of_lt h)
    exact le_trans h1 (le_mul_of_one_le_right (le_of_lt hbN0) (hfac1 k))
  · exact main k h

/-- `((a ^ (1/ε)) ^ k) ^ ε = a ^ k` for `a ≥ 0` and `ε ≠ 0`. -/
theorem rpow_div_pow_rpow (a eps : ℝ) (ha : 0 ≤ a) (heps : eps ≠ 0) (k : ℕ) :
    ((a ^ (1 / eps)) ^ k) ^ eps = a ^ k := by
  set b := a ^ (1 / eps) with hbdef
  have hb0 : 0 ≤ b := by rw [hbdef]; exact Real.rpow_nonneg ha _
  have hbeps : b ^ eps = a := by
    rw [hbdef, ← Real.rpow_mul ha (1 / eps) eps]
    rw [show (1 / eps) * eps = 1 by rw [one_div, inv_mul_cancel₀ heps]]
    rw [Real.rpow_one]
  calc (b ^ k) ^ eps = (b ^ (k : ℝ)) ^ eps := by rw [← Real.rpow_natCast]
    _ = b ^ ((k : ℝ) * eps) := by rw [← Real.rpow_mul hb0]
    _ = b ^ (eps * (k : ℝ)) := by rw [mul_comm]
    _ = (b ^ eps) ^ (k : ℝ) := by rw [Real.rpow_mul hb0]
    _ = (b ^ eps) ^ k := by rw [Real.rpow_natCast]
    _ = a ^ k := by rw [hbeps]

/-- `((a ^ (1/ε)) ^ N * c) ^ ε = a ^ N * c ^ ε` for `a, c ≥ 0` and `ε ≠ 0`. -/
theorem rpow_div_mul_rpow (a eps : ℝ) (ha : 0 ≤ a) (heps : eps ≠ 0) (N : ℕ) (c : ℝ)
    (hc : 0 ≤ c) :
    ((a ^ (1 / eps)) ^ N * c) ^ eps = a ^ N * c ^ eps := by
  set b := a ^ (1 / eps) with hbdef
  have hb0 : 0 ≤ b := by rw [hbdef]; exact Real.rpow_nonneg ha _
  have hbeps : b ^ eps = a := by
    rw [hbdef, ← Real.rpow_mul ha (1 / eps) eps]
    rw [show (1 / eps) * eps = 1 by rw [one_div, inv_mul_cancel₀ heps]]
    rw [Real.rpow_one]
  have key : (b ^ N) ^ eps = a ^ N := by
    calc (b ^ N) ^ eps = (b ^ (N : ℝ)) ^ eps := by rw [← Real.rpow_natCast]
      _ = b ^ ((N : ℝ) * eps) := by rw [← Real.rpow_mul hb0]
      _ = b ^ (eps * (N : ℝ)) := by rw [mul_comm]
      _ = (b ^ eps) ^ (N : ℝ) := by rw [Real.rpow_mul hb0]
      _ = (b ^ eps) ^ N := by rw [Real.rpow_natCast]
      _ = a ^ N := by rw [hbeps]
  rw [Real.mul_rpow (pow_nonneg hb0 N) hc, key]

/-- For every real `a ≥ 0` and every `ε > 0`, the function `n ↦ a ^ ω(n)` is bounded
by a constant times `n ^ ε`. -/
theorem pow_omega_le_const_mul_rpow (a eps : ℝ) (ha : 0 ≤ a) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → a ^ n.primeFactors.card ≤ C * (n : ℝ) ^ eps := by
  rcases le_or_gt a 1 with ha1 | ha1
  · refine ⟨1, one_pos, ?_⟩
    intro n hn
    have hk : a ^ n.primeFactors.card ≤ 1 := pow_le_one₀ ha ha1
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hle : (1 : ℝ) ≤ (n : ℝ) ^ eps := Real.one_le_rpow hn1 (le_of_lt heps)
    calc a ^ n.primeFactors.card ≤ 1 := hk
      _ ≤ (n : ℝ) ^ eps := hle
      _ = 1 * (n : ℝ) ^ eps := by ring
  · have ha0 : 0 < a := lt_trans one_pos ha1
    have hb1 : 1 ≤ a ^ (1 / eps) := le_of_lt (Real.one_lt_rpow ha1 (by positivity))
    obtain ⟨N, hN⟩ := pow_le_factorial_mul (a ^ (1 / eps)) hb1
    refine ⟨a ^ N, pow_pos ha0 N, ?_⟩
    intro n hn
    set k := n.primeFactors.card with hkdef
    have hfacN : ((k + 1).factorial : ℕ) ≤ n := factorial_card_primeFactors_le n hn
    have hfacR : (((k + 1).factorial : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfacN
    have hc0 : (0 : ℝ) ≤ (((k + 1).factorial : ℕ) : ℝ) := by positivity
    have hpow_nn : (0 : ℝ) ≤ (a ^ (1 / eps)) ^ k := pow_nonneg (Real.rpow_nonneg ha _) _
    have hraise : ((a ^ (1 / eps)) ^ k) ^ eps
        ≤ ((a ^ (1 / eps)) ^ N * (((k + 1).factorial : ℕ) : ℝ)) ^ eps :=
      Real.rpow_le_rpow hpow_nn (hN k) (le_of_lt heps)
    rw [rpow_div_pow_rpow a eps ha heps.ne' k,
        rpow_div_mul_rpow a eps ha heps.ne' N _ hc0] at hraise
    calc a ^ k ≤ a ^ N * (((k + 1).factorial : ℕ) : ℝ) ^ eps := hraise
      _ ≤ a ^ N * (n : ℝ) ^ eps := by
            apply mul_le_mul_of_nonneg_left _
            · positivity
            · exact Real.rpow_le_rpow hc0 hfacR (le_of_lt heps)

end Commons.NumberTheory.Nat