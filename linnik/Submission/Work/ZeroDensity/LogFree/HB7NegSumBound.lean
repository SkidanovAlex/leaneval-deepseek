import Mathlib

/-!
# A convergent exponential series bound (Heath-Brown 1992, auxiliary estimate)

We prove that the series
`∑ n, exp(-(exp n)) * exp(2 (n+1))`
converges and that its sum is at most `20000`.

The term rewrites as `exp (2 (n+1) - exp n)`.  Since `2^n ≤ exp n` and
`2^n ≥ 3n+2` for `n ≥ 4`, the term is eventually dominated by `(1/2)^n`, which
gives summability and a very small tail.  The finitely many initial terms
(`n < 4`) are each at most `exp 8`, and `exp 8 < 3000` by a numerical bound on
`Real.exp 1`.  This is far below the required `20000`.
-/

namespace Work.ZeroDensity.LogFree

/-- `exp n = (exp 1)^n` for natural `n`. -/
private lemma exp_nat_eq_pow (n : ℕ) : Real.exp (n:ℝ) = Real.exp 1 ^ n := by
  rw [← Real.exp_nat_mul, mul_one]

/-- `3 n + 2 ≤ 2^n` for `n ≥ 4`. -/
private lemma two_pow_ge_nat (n : ℕ) (hn : 4 ≤ n) : 3*n + 2 ≤ 2^n :=
  Nat.le_induction (m := 4) (by norm_num) (fun n _ ih => by
    calc 3*(n+1) + 2 = 3*n + 5 := by omega
      _ ≤ (3*n+2)*2 := by omega
      _ ≤ 2^n * 2 := Nat.mul_le_mul_right 2 ih
      _ = 2^(n+1) := (pow_succ 2 n).symm) n hn

/-- `exp` dominates the linear polynomial: `3 n + 2 ≤ exp n` for `n ≥ 4`. -/
private lemma exp_ge_poly (n : ℕ) (hn : 4 ≤ n) : 3*(n:ℝ) + 2 ≤ Real.exp (n:ℝ) := by
  have h := two_pow_ge_nat n hn
  have h' : ((3*n+2 : ℕ) : ℝ) ≤ ((2^n : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  have h2 : (2:ℝ)^n ≤ Real.exp (n:ℝ) := by
    rw [exp_nat_eq_pow]
    exact pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (le_of_lt Real.exp_one_gt_two) n
  linarith

/-- `exp (-n) ≤ (1/2)^n`. -/
private lemma exp_neg_le_half_pow (n : ℕ) : Real.exp (-(n:ℝ)) ≤ (1/2:ℝ)^n := by
  calc Real.exp (-(n:ℝ)) = (Real.exp (n:ℝ))⁻¹ := Real.exp_neg _
    _ ≤ ((2:ℝ)^n)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) (pow_pos (by norm_num) n)).mpr (by
          rw [exp_nat_eq_pow]
          exact pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_two) n)
    _ = (1/2:ℝ)^n := by rw [one_div, inv_pow]

/-- Numerical bound `exp 8 < 3000`. -/
private lemma exp8_lt : Real.exp 8 < 3000 := by
  rw [show Real.exp (8:ℝ) = Real.exp 1 ^ 8 from by rw [← Real.exp_nat_mul]; norm_num]
  calc Real.exp 1 ^ 8 < (2.7182818286:ℝ)^8 :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos 1)) (by norm_num)
      _ < 3000 := by norm_num

theorem HB7NegSumBound :
    Summable (fun n : ℕ => Real.exp (-(Real.exp (n:ℝ))) * Real.exp (2 * ((n:ℝ) + 1))) ∧
    (∑' n : ℕ, Real.exp (-(Real.exp (n:ℝ))) * Real.exp (2 * ((n:ℝ) + 1))) ≤ 20000 := by
  -- Rewrite each term as a single exponential.
  have ha_eq : ∀ n : ℕ,
      Real.exp (-(Real.exp (n:ℝ))) * Real.exp (2 * ((n:ℝ) + 1))
        = Real.exp (2 * ((n:ℝ) + 1) - Real.exp (n:ℝ)) := by
    intro n
    rw [← Real.exp_add]
    congr 1
    ring
  -- Eventual domination by `(1/2)^n`.
  have ha_le : ∀ n : ℕ, 4 ≤ n →
      Real.exp (-(Real.exp (n:ℝ))) * Real.exp (2 * ((n:ℝ) + 1)) ≤ (1/2:ℝ)^n := by
    intro n hn
    rw [ha_eq n]
    have h1 : 2 * ((n:ℝ) + 1) - Real.exp (n:ℝ) ≤ -(n:ℝ) := by
      have := exp_ge_poly n hn; linarith
    calc Real.exp (2 * ((n:ℝ) + 1) - Real.exp (n:ℝ)) ≤ Real.exp (-(n:ℝ)) := Real.exp_le_exp.mpr h1
      _ ≤ (1/2:ℝ)^n := exp_neg_le_half_pow n
  have hnorm : ∀ n : ℕ, ‖Real.exp (-(Real.exp (n:ℝ))) * Real.exp (2 * ((n:ℝ) + 1))‖
      = Real.exp (-(Real.exp (n:ℝ))) * Real.exp (2 * ((n:ℝ) + 1)) := by
    intro n
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
  have hsum : Summable (fun n : ℕ => Real.exp (-(Real.exp (n:ℝ))) * Real.exp (2 * ((n:ℝ) + 1))) := by
    apply Summable.of_norm_bounded_eventually (g := fun n => (1/2:ℝ)^n)
    · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
    · rw [Nat.cofinite_eq_atTop]
      apply Filter.eventually_atTop.mpr
      refine ⟨4, fun n hn => ?_⟩
      rw [hnorm n]
      exact ha_le n hn
  refine ⟨hsum, ?_⟩
  -- Split off the first four terms.
  have hsplit := hsum.sum_add_tsum_nat_add 4
  rw [← hsplit]
  have hfin : (∑ i ∈ Finset.range 4,
        Real.exp (-(Real.exp (i:ℝ))) * Real.exp (2*((i:ℝ)+1))) ≤ 4 * Real.exp 8 := by
    calc (∑ i ∈ Finset.range 4, Real.exp (-(Real.exp (i:ℝ))) * Real.exp (2*((i:ℝ)+1)))
        ≤ ∑ i ∈ Finset.range 4, Real.exp 8 := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          rw [ha_eq i]
          apply Real.exp_le_exp.mpr
          have hi3 : (i:ℝ) ≤ 3 := by exact_mod_cast (by omega : i ≤ 3)
          have hp : (0:ℝ) < Real.exp (i:ℝ) := Real.exp_pos _
          nlinarith
      _ = 4 * Real.exp 8 := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
  have htail : (∑' i : ℕ,
        Real.exp (-(Real.exp (((i+4:ℕ):ℝ)))) * Real.exp (2*((((i+4:ℕ):ℝ))+1))) ≤ 1/8 := by
    calc (∑' i : ℕ, Real.exp (-(Real.exp (((i+4:ℕ):ℝ)))) * Real.exp (2*((((i+4:ℕ):ℝ))+1)))
        ≤ ∑' i : ℕ, (1/2:ℝ)^(i+4) := by
          apply Summable.tsum_le_tsum
          · intro i; exact ha_le (i+4) (by omega)
          · exact (summable_nat_add_iff 4).mpr hsum
          · exact (summable_nat_add_iff 4).mpr
              (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      _ = 1/8 := by
          rw [tsum_congr (fun i => by rw [pow_add])]
          rw [tsum_mul_right]
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
  have h4 : 4 * Real.exp 8 ≤ 12000 := by
    have := exp8_lt; linarith
  linarith [hfin, htail, h4]

end Work.ZeroDensity.LogFree
