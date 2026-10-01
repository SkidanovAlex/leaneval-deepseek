import Mathlib
import Submission.Work.ZeroDensity.Huxley.succ_le_ceilInv_mul_rpow
import Submission.Work.ZeroDensity.Huxley.succ_le_rpow_of_two_le_rpow
import Submission.Work.ZeroDensity.Huxley.rpow_eq_prod_factorization

namespace Work.ZeroDensity.Huxley

/-- **The divisor function is dominated by any power of `n`.**  For every `δ > 0` there is `C > 0` with `#{d : d ∣ n} ≤ C · n^δ` for every `n ≥ 1`.

Proof sketch: for a prime power `p^v ‖ n`, the factor `v+1` of `τ(n) = ∏_{p^v‖n}(v+1)` satisfies
`v + 1 ≤ c_p · p^{δv}` where `c_p := sup_{v}(v+1)/p^{δv} < ∞`; `c_p ≤ 1` once `p ≥ 2^{1/δ}`, and the
remaining factors have `p < 2^{1/δ}`, so `∏_{p ∣ n} c_p ≤ ∏_{p < 2^{1/δ}} c_p =: C` is finite and
`τ(n) ≤ C n^δ`. -/
theorem cardDivisorsLe {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((n.divisors.card : ℕ) : ℝ) ≤ C * (n : ℝ) ^ δ := by
  classical
  -- `k = ⌈1/δ⌉` is the uniform constant for the small prime factors,
  -- `T = 2^{1/δ}` the threshold beyond which the constant is `1`,
  -- `B` an upper bound for the number of primes below `T`.
  set k : ℕ := ⌈(1 : ℝ) / δ⌉₊ with hk
  set T : ℝ := (2 : ℝ) ^ (1 / δ) with hT
  set B : ℕ := ⌈T⌉₊ with hB
  have hk1 : 1 ≤ k := by
    rw [hk]; exact Nat.one_le_ceil_iff.mpr (by positivity)
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  refine ⟨(k : ℝ) ^ B, pow_pos hkpos B, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  -- expand `τ(n)` into the product of `v_p(n) + 1` over the prime factors
  rw [Nat.card_divisors hn0]
  push_cast
  -- each factor is dominated by the appropriate constant times `p^{δ·v_p(n)}`
  have hstep : ∀ x ∈ n.primeFactors, (n.factorization x : ℝ) + 1 ≤
      (if (x : ℝ) < T then (k : ℝ) else 1) * (x : ℝ) ^ ((n.factorization x : ℝ) * δ) := by
    intro x hx
    have hxp : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
    have hx2 : 2 ≤ x := hxp.two_le
    by_cases hxT : (x : ℝ) < T
    · -- small prime: use the uniform constant `k = ⌈1/δ⌉`
      rw [if_pos hxT]
      exact succ_le_ceilInv_mul_rpow hδ x (n.factorization x) hx2
    · -- large prime: `x^δ ≥ 2`, so the constant is `1`
      rw [if_neg hxT, one_mul]
      refine succ_le_rpow_of_two_le_rpow x (n.factorization x) hx2 ?_
      have hxT' : T ≤ (x : ℝ) := not_lt.mp hxT
      have hTδ : T ^ δ = 2 := by
        rw [hT, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
      calc (2 : ℝ) = T ^ δ := hTδ.symm
        _ ≤ (x : ℝ) ^ δ := Real.rpow_le_rpow
              (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) hxT' hδ.le
  -- at most `B` prime factors are below the threshold `T`
  have hcount : (n.primeFactors.filter (fun x : ℕ => (x : ℝ) < T)).card ≤ B := by
    have hsub : n.primeFactors.filter (fun x : ℕ => (x : ℝ) < T) ⊆ Finset.range B := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_range]
      have hTB : T ≤ (B : ℝ) := by rw [hB]; exact Nat.le_ceil T
      have : (x : ℝ) < (B : ℝ) := lt_of_lt_of_le hx.2 hTB
      exact_mod_cast this
    calc (n.primeFactors.filter (fun x : ℕ => (x : ℝ) < T)).card
        ≤ (Finset.range B).card := Finset.card_le_card hsub
      _ = B := Finset.card_range B
  -- assemble
  calc ∏ x ∈ n.primeFactors, ((n.factorization x : ℝ) + 1)
      ≤ ∏ x ∈ n.primeFactors,
          ((if (x : ℝ) < T then (k : ℝ) else 1) * (x : ℝ) ^ ((n.factorization x : ℝ) * δ)) :=
        Finset.prod_le_prod₀ (fun x _ => by positivity) hstep
    _ = (∏ x ∈ n.primeFactors, (if (x : ℝ) < T then (k : ℝ) else 1))
          * (∏ x ∈ n.primeFactors, (x : ℝ) ^ ((n.factorization x : ℝ) * δ)) :=
        Finset.prod_mul_distrib
    _ = (k : ℝ) ^ ((n.primeFactors.filter (fun x : ℕ => (x : ℝ) < T)).card)
          * (n : ℝ) ^ δ := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]
        rw [rpow_eq_prod_factorization hn0]
    _ ≤ (k : ℝ) ^ B * (n : ℝ) ^ δ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) δ)
        exact pow_le_pow_right₀ (by exact_mod_cast hk1) hcount

end Work.ZeroDensity.Huxley
