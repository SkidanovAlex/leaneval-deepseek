import Mathlib
import Submission.Work.A3.factorial_le_prod_of_one_le
import Submission.Work.A3.factorial_ge_div_exp

/-!
# The number of distinct prime factors is `O(q ^ δ)`

For every real `C₀ ≥ 1` and every `δ > 0` there is a constant `C > 0` with

  `C₀ ^ (q.primeFactors.card) ≤ C * q ^ δ`   for all `q ≥ 1`.

(The "ℴ-trick" input of Area A3: it converts a factor `C₀` taken to the power
"number of distinct primes dividing `q`" into an arbitrarily small power of `q`.)

## Proof

Let `k` be the number of distinct prime factors of `q`.  The product of `k` distinct primes is at
least the product of `k` distinct positive integers, hence at least `k!`, and it divides `q`
(`Nat.prod_primeFactors_dvd`); so `k! ≤ q`.  On the other hand `k! ≥ (k/e)^k`
(`Work.A3.factorial_ge_div_exp`), so if `k` is large enough that `k/e ≥ C₀ ^ δ⁻¹`, i.e.
`k ≥ e * C₀ ^ δ⁻¹`, then

  `C₀ ^ k = ((C₀ ^ δ⁻¹) ^ k) ^ δ ≤ ((k/e) ^ k) ^ δ ≤ (k!) ^ δ ≤ q ^ δ`.

For the finitely many remaining `k ≤ K` we simply take `C = max (C₀ ^ K) 1`, and the resulting
constant is positive.
-/

namespace Work.A3

/-- The product of the distinct primes dividing `q` is at most `q` (the radical of `q` divides
`q`). -/
theorem prod_primeFactors_le (q : ℕ) (hq : 1 ≤ q) : ∏ p ∈ q.primeFactors, p ≤ q :=
  Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)

/-- The factorial of the number of distinct prime factors of `q ≥ 1` is at most `q`: the product
of `k` distinct primes is at least `k!`, and it divides `q`. -/
theorem factorial_card_primeFactors_le (q : ℕ) (hq : 1 ≤ q) :
    Nat.factorial q.primeFactors.card ≤ q := by
  refine le_trans (factorial_le_prod_of_one_le q.primeFactors ?_) (prod_primeFactors_le q hq)
  intro p hp
  exact le_trans (by norm_num) (Nat.mem_primeFactors.mp hp).1.two_le

/-- `(x ^ m) ^ y = x ^ (m * y)` for `x ≥ 0` (`m` a natural exponent). -/
private lemma rpow_nat_pow_rpow (x : ℝ) (hx : 0 ≤ x) (m : ℕ) (y : ℝ) :
    (x ^ m) ^ y = x ^ ((m : ℝ) * y) := by
  have h : (x ^ m : ℝ) = x ^ (m : ℝ) := (Real.rpow_natCast x m).symm
  rw [h, Real.rpow_mul hx]

/-- `((x ^ a) ^ m) ^ y = x ^ (a * m * y)` for `x ≥ 0`. -/
private lemma rpow_mul_nat_pow_rpow (x : ℝ) (hx : 0 ≤ x) (a : ℝ) (m : ℕ) (y : ℝ) :
    ((x ^ a) ^ m) ^ y = x ^ (a * (m : ℝ) * y) := by
  have h1 : ((x ^ a) ^ m : ℝ) = (x ^ a) ^ (m : ℝ) := (Real.rpow_natCast (x ^ a) m).symm
  rw [h1, ← Real.rpow_mul hx a (m : ℝ), ← Real.rpow_mul hx (a * (m : ℝ)) y]

theorem card_primeFactors_rpow_le (C₀ : ℝ) (hC : 1 ≤ C₀) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q → C₀ ^ q.primeFactors.card ≤ C * (q : ℝ) ^ δ := by
  have hCpos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC
  have hδne : δ ≠ 0 := ne_of_gt hδ
  -- pick `K ≥ e * C₀ ^ δ⁻¹`
  obtain ⟨K, hK⟩ := exists_nat_ge (Real.exp 1 * C₀ ^ δ⁻¹)
  refine ⟨max (C₀ ^ K) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro q hq
  set k : ℕ := q.primeFactors.card with hk
  by_cases hkK : k ≤ K
  · -- small `k`: the constant `max (C₀ ^ K) 1` alone suffices
    have h1 : C₀ ^ k ≤ max (C₀ ^ K) 1 := le_trans (pow_le_pow_right₀ hC hkK) (le_max_left _ _)
    have h2 : (1 : ℝ) ≤ (q : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast hq) hδ.le
    have h3 : (0 : ℝ) ≤ max (C₀ ^ K) 1 := le_trans zero_le_one (le_max_right _ _)
    calc C₀ ^ k ≤ max (C₀ ^ K) 1 := h1
      _ = max (C₀ ^ K) 1 * 1 := (mul_one _).symm
      _ ≤ max (C₀ ^ K) 1 * (q : ℝ) ^ δ := mul_le_mul_of_nonneg_left h2 h3
  · -- large `k ≥ K`: use `k! ≥ (k/e)^k`
    have hKk : K < k := not_le.mp hkK
    have hk1 : 1 ≤ k := by omega
    have hkK' : Real.exp 1 * C₀ ^ δ⁻¹ ≤ (k : ℝ) := le_trans hK (by exact_mod_cast hKk.le)
    have hdiv : C₀ ^ δ⁻¹ ≤ (k : ℝ) / Real.exp 1 := by
      rw [le_div_iff₀ (Real.exp_pos 1), mul_comm]
      exact hkK'
    have hstep : (C₀ ^ δ⁻¹) ^ k ≤ ((k : ℝ) / Real.exp 1) ^ k :=
      pow_le_pow_left₀ (Real.rpow_nonneg hCpos.le δ⁻¹) hdiv k
    have hstep2 : (C₀ ^ δ⁻¹) ^ k ≤ (Nat.factorial k : ℝ) :=
      le_trans hstep (factorial_ge_div_exp k)
    have hpowδ' : ((C₀ ^ δ⁻¹) ^ k) ^ δ = C₀ ^ (k : ℝ) := by
      rw [rpow_mul_nat_pow_rpow C₀ hCpos.le δ⁻¹ k δ]
      have h : δ⁻¹ * (k : ℝ) * δ = (k : ℝ) := by
        rw [show δ⁻¹ * (k : ℝ) * δ = (δ⁻¹ * δ) * (k : ℝ) by ring,
          inv_mul_cancel₀ hδne, one_mul]
      rw [h]
    have hpowδ : ((C₀ ^ δ⁻¹) ^ k) ^ δ = C₀ ^ k := by
      rw [hpowδ', Real.rpow_natCast]
    have hfinal : C₀ ^ k ≤ (Nat.factorial k : ℝ) ^ δ := by
      have h := Real.rpow_le_rpow (pow_nonneg (Real.rpow_nonneg hCpos.le δ⁻¹) k) hstep2 hδ.le
      rwa [hpowδ] at h
    have hfk : (Nat.factorial k : ℝ) ≤ (q : ℝ) := by
      have h := factorial_card_primeFactors_le q hq
      rw [← hk] at h
      exact_mod_cast h
    have hle1 : (Nat.factorial k : ℝ) ^ δ ≤ (q : ℝ) ^ δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hfk hδ.le
    have hle2 : (q : ℝ) ^ δ ≤ max (C₀ ^ K) 1 * (q : ℝ) ^ δ :=
      le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg _) δ) (le_max_right _ _)
    exact le_trans hfinal (le_trans hle1 hle2)

end Work.A3
