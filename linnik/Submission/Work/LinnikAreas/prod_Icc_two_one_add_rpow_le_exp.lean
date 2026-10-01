import Mathlib

/-!
# Bound for `∏_{j=2}^{k+1} (1 + j^{-1/2})`

We prove that the finite product `∏_{j ∈ Icc 2 (k+1)} (1 + (j:ℝ)^(-(1/2)))` is bounded above
by `exp ((log ((k+1)!))^(3/4))`.

The proof strategy:
* each factor satisfies `1 + x ≤ exp x` for `x ≥ 0`, whence the product is at most
  `exp (∑_{j ∈ Icc 2 (k+1)} j^{-1/2})`;
* the remainder of the work is the purely analytic estimate
  `∑_{j ∈ Icc 2 n} j^{-1/2} ≤ (log n!)^(3/4)` for `n ≥ 2`, proved by induction on `n`,
  using the concavity of `x ↦ x^(3/4)` and the elementary upper bound `log n! ≤ n log n`.
-/

namespace Work.LinnikAreas

/-- Concavity increment for `x ↦ x^(3/4)`: for `a, b > 0`,
`(a+b)^(3/4) - a^(3/4) ≥ (3/4) b (a+b)^(-1/4)`. -/
private lemma rpow_increment (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (3/4) * b * (a + b) ^ (-(1/4 : ℝ)) ≤ (a + b) ^ (3/4 : ℝ) - a ^ (3/4 : ℝ) := by
  have hc : 0 < a + b := add_pos ha hb
  set r : ℝ := b / (a + b) with hr
  have hr1 : r ≤ 1 := by rw [hr]; rw [div_le_one hc]; linarith
  have hkey : (1 - r) ^ (3/4 : ℝ) ≤ 1 - (3/4) * r := by
    have h := rpow_one_add_le_one_add_mul_self (s := -r) (by linarith) (p := (3/4 : ℝ))
      (by norm_num) (by norm_num)
    have h1 : (1 + -r) = 1 - r := by ring
    rw [h1] at h
    calc (1 - r) ^ (3/4 : ℝ) ≤ 1 + (3/4 : ℝ) * (-r) := h
      _ = 1 - (3/4) * r := by ring
  have ha_eq : a = (a + b) * (1 - r) := by rw [hr]; field_simp; ring
  have hnonneg : (0 : ℝ) ≤ 1 - r := by linarith
  have h2 : a ^ (3/4 : ℝ) = (a + b) ^ (3/4 : ℝ) * (1 - r) ^ (3/4 : ℝ) := by
    conv_lhs => rw [ha_eq]
    rw [Real.mul_rpow hc.le hnonneg]
  have hpos : 0 < (a + b) ^ (3/4 : ℝ) := Real.rpow_pos_of_pos hc _
  have h3 : (3/4) * b * (a + b) ^ (-(1/4 : ℝ)) = (a + b) ^ (3/4 : ℝ) * ((3/4) * r) := by
    rw [hr]
    have h34 : (3/4 : ℝ) - 1 = -(1/4) := by norm_num
    rw [← h34, Real.rpow_sub hc (3/4) 1, Real.rpow_one, div_eq_mul_inv]
    ring
  rw [h2, h3]
  have he : (a + b) ^ (3/4 : ℝ) - (a + b) ^ (3/4 : ℝ) * (1 - r) ^ (3/4 : ℝ)
      = (a + b) ^ (3/4 : ℝ) * (1 - (1 - r) ^ (3/4 : ℝ)) := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hpos.le
  linarith

/-- `log n! ≤ n log n`. -/
private lemma log_factorial_le_mul_log (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
  have hle : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log (by positivity) hle
    _ = (n : ℝ) * Real.log n := Real.log_pow n n

/-- Base case `n = 2`: `2^(-1/2) ≤ (log 2)^(3/4)`. -/
private lemma base_case : (2 : ℝ) ^ (-(1/2 : ℝ)) ≤ (Real.log 2) ^ (3/4 : ℝ) := by
  have hlog : (2/3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hbase : (2 : ℝ) ^ (-(2/3 : ℝ)) ≤ (2/3 : ℝ) := by
    have hl : ((2 : ℝ) ^ (-(2/3 : ℝ))) ^ (3 : ℝ) = (1/4 : ℝ) := by
      rw [← Real.rpow_mul (x := 2) (by norm_num : (0 : ℝ) ≤ 2) (-(2/3 : ℝ)) 3]
      rw [show (-(2/3 : ℝ)) * 3 = -2 by norm_num]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
      norm_num
    have hcube : ((2 : ℝ) ^ (-(2/3 : ℝ))) ^ (3 : ℝ) ≤ ((2/3 : ℝ)) ^ (3 : ℝ) := by
      rw [hl]; norm_num
    exact (Real.rpow_le_rpow_iff (x := (2 : ℝ) ^ (-(2/3 : ℝ))) (y := (2/3 : ℝ)) (z := 3)
      (by positivity) (by norm_num) (by norm_num)).mp hcube
  have h1 : (2 : ℝ) ^ (-(1/2 : ℝ)) = ((2 : ℝ) ^ (-(2/3 : ℝ))) ^ (3/4 : ℝ) := by
    rw [← Real.rpow_mul (x := 2) (by norm_num : (0 : ℝ) ≤ 2) (-(2/3 : ℝ)) (3/4 : ℝ)]
    norm_num
  rw [h1]
  exact Real.rpow_le_rpow (by positivity) (le_trans hbase hlog) (by norm_num)

/-- A rational lower bound for `log 3`. -/
private lemma log_three_lower : (1.02 : ℝ) ≤ Real.log 3 := by
  have h1 : (1/3 : ℝ) ≤ Real.log (3/2) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (3/2 : ℝ)) (by norm_num)
    norm_num at this ⊢
    linarith
  have h2 : Real.log 3 = Real.log 2 + Real.log (3/2) := by
    have h : (3 : ℝ) = 2 * (3/2) := by norm_num
    conv_lhs => rw [h]
    rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [h2]
  linarith [Real.log_two_gt_d9]

/-- For every `n ≥ 3`, `(4/3)^4 = 256/81 ≤ n (log n)^3`. -/
private lemma nat_mul_log_cube_ge (n : ℕ) (hn : 3 ≤ n) :
    (256/81 : ℝ) ≤ (n : ℝ) * (Real.log n) ^ 3 := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : (1.02 : ℝ) ≤ Real.log n :=
    le_trans log_three_lower (Real.log_le_log (by norm_num) hn3)
  have hcube : (1.02 : ℝ) ^ 3 ≤ (Real.log n) ^ 3 := pow_le_pow_left₀ (by norm_num) hlogn 3
  have hmul : (3 : ℝ) * (1.02 : ℝ) ^ 3 ≤ (n : ℝ) * (Real.log n) ^ 3 :=
    mul_le_mul hn3 hcube (by positivity) (by linarith)
  have hnum : (256/81 : ℝ) ≤ 3 * (1.02 : ℝ) ^ 3 := by norm_num
  linarith

/-- The arithmetic core of the induction step: for `N ≥ 3` and `b ≥ 1.02`,
`N^(-1/2) ≤ (3/4) b^(3/4) N^(-1/4)`. -/
private lemma step_key (N b : ℝ) (hN : 3 ≤ N) (hb : 1.02 ≤ b) :
    N ^ (-(1/2 : ℝ)) ≤ (3/4) * b ^ (3/4 : ℝ) * N ^ (-(1/4 : ℝ)) := by
  have hNpos : 0 < N := by linarith
  have hbpos : 0 < b := by linarith
  have h1 : N ^ (-(1/2 : ℝ)) = N ^ (-(1/4 : ℝ)) * N ^ (-(1/4 : ℝ)) := by
    rw [← Real.rpow_add hNpos]; norm_num
  rw [h1, show (3/4) * b ^ (3/4 : ℝ) * N ^ (-(1/4 : ℝ))
      = N ^ (-(1/4 : ℝ)) * ((3/4) * b ^ (3/4 : ℝ)) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc N ^ (-(1/4 : ℝ)) ≤ 3 ^ (-(1/4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 3) hN (by norm_num)
    _ ≤ (3/4) * b ^ (3/4 : ℝ) := by
        have h2 : (3 : ℝ) ^ (-(1/4 : ℝ)) ≤ (3/4) * (1.02 : ℝ) ^ (3/4 : ℝ) := by
          rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 4)]
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (-(1/4 : ℝ)) 4]
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3/4)
            (by positivity : (0 : ℝ) ≤ (1.02) ^ (3/4 : ℝ))]
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1.02) (3/4 : ℝ) 4]
          rw [show (-(1/4 : ℝ)) * 4 = -1 by norm_num, show (3/4 : ℝ) * 4 = 3 by norm_num]
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_one]
          simp only [Real.rpow_ofNat]
          norm_num
        have h3 : (3/4) * (1.02 : ℝ) ^ (3/4 : ℝ) ≤ (3/4) * b ^ (3/4 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.rpow_le_rpow (by norm_num) hb (by norm_num)
        linarith

/-- The analytic estimate `∑_{j ∈ Icc 2 n} j^{-1/2} ≤ (log n!)^(3/4)` for `n ≥ 2`,
proved by induction on `n`. -/
private lemma sum_le_log_factorial (n : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.Icc 2 n, (j : ℝ) ^ (-(1/2 : ℝ)))
      ≤ (Real.log (n.factorial : ℝ)) ^ (3/4 : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.factorial_two]
      exact base_case
  | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
      have hterm : ((n + 1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) = ((n : ℝ) + 1) ^ (-(1/2 : ℝ)) := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hterm]
      have hN3 : (3 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (3 : ℕ) ≤ n + 1 := by omega
        exact_mod_cast this
      have hlogfac : Real.log ((n + 1).factorial : ℝ)
          = Real.log (n.factorial : ℝ) + Real.log ((n : ℝ) + 1) := by
        have hfc : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        rw [hfc, Real.log_mul (by positivity) (by positivity), add_comm]
      rw [hlogfac]
      have ha_pos : 0 < Real.log (n.factorial : ℝ) := by
        apply Real.log_pos
        exact_mod_cast (show 1 < n.factorial by
          have := Nat.factorial_le hn
          simp only [Nat.factorial_two] at this
          omega)
      have hb_pos : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
      have hab_pos : 0 < Real.log (n.factorial : ℝ) + Real.log ((n : ℝ) + 1) :=
        add_pos ha_pos hb_pos
      have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hab_le : Real.log (n.factorial : ℝ) + Real.log ((n : ℝ) + 1)
          ≤ ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) := by
        have h := log_factorial_le_mul_log (n + 1)
        rw [hlogfac] at h
        simpa using h
      have hincr := rpow_increment (Real.log (n.factorial : ℝ)) (Real.log ((n : ℝ) + 1))
        ha_pos hb_pos
      have hstep := step_key ((n : ℝ) + 1) (Real.log ((n : ℝ) + 1)) hN3
        (le_trans log_three_lower (Real.log_le_log (by norm_num) hN3))
      have hbpow : (Real.log ((n : ℝ) + 1)) ^ (3/4 : ℝ)
          = Real.log ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1)) ^ (-(1/4 : ℝ)) := by
        have h := Real.rpow_add hb_pos (1 : ℝ) (-(1/4 : ℝ))
        rw [show (1 : ℝ) + (-(1/4 : ℝ)) = 3/4 by norm_num, Real.rpow_one] at h
        exact h
      have hcorr : (3/4) * (Real.log ((n : ℝ) + 1)) ^ (3/4 : ℝ) * ((n : ℝ) + 1) ^ (-(1/4 : ℝ))
          = (3/4) * Real.log ((n : ℝ) + 1)
              * (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) ^ (-(1/4 : ℝ)) := by
        rw [hbpow, Real.mul_rpow hNpos.le hb_pos.le]
        ring
      have hcmp : (3/4) * Real.log ((n : ℝ) + 1)
            * (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) ^ (-(1/4 : ℝ))
          ≤ (3/4) * Real.log ((n : ℝ) + 1)
            * (Real.log (n.factorial : ℝ) + Real.log ((n : ℝ) + 1)) ^ (-(1/4 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_nonpos hab_pos hab_le (by norm_num)
      have hNterm : ((n : ℝ) + 1) ^ (-(1/2 : ℝ))
          ≤ (3/4) * Real.log ((n : ℝ) + 1)
            * (Real.log (n.factorial : ℝ) + Real.log ((n : ℝ) + 1)) ^ (-(1/4 : ℝ)) := by
        rw [hcorr] at hstep
        linarith
      have hfinal : (Real.log (n.factorial : ℝ)) ^ (3/4 : ℝ) + ((n : ℝ) + 1) ^ (-(1/2 : ℝ))
          ≤ (Real.log (n.factorial : ℝ) + Real.log ((n : ℝ) + 1)) ^ (3/4 : ℝ) := by
        linarith [hNterm, hincr]
      calc (∑ j ∈ Finset.Icc 2 n, (j : ℝ) ^ (-(1/2 : ℝ))) + ((n : ℝ) + 1) ^ (-(1/2 : ℝ))
          ≤ (Real.log (n.factorial : ℝ)) ^ (3/4 : ℝ) + ((n : ℝ) + 1) ^ (-(1/2 : ℝ)) := by
            linarith [ih]
        _ ≤ (Real.log (n.factorial : ℝ) + Real.log ((n : ℝ) + 1)) ^ (3/4 : ℝ) := hfinal

theorem prod_Icc_two_one_add_rpow_le_exp (k : ℕ) (hk : 1 ≤ k) :
    ∏ j ∈ Finset.Icc 2 (k + 1), (1 + (j : ℝ) ^ (-(1/2 : ℝ)))
      ≤ Real.exp ((Real.log ((k + 1).factorial : ℝ)) ^ (3/4 : ℝ)) := by
  have hn : 2 ≤ k + 1 := by omega
  have hprod : ∏ j ∈ Finset.Icc 2 (k + 1), (1 + (j : ℝ) ^ (-(1/2 : ℝ)))
      ≤ Real.exp (∑ j ∈ Finset.Icc 2 (k + 1), (j : ℝ) ^ (-(1/2 : ℝ))) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro j hj
      have hj0 : (0 : ℝ) < (j : ℝ) := by
        have := (Finset.mem_Icc.mp hj).1
        exact_mod_cast (by omega : 0 < j)
      exact add_nonneg zero_le_one (Real.rpow_nonneg hj0.le _)
    · intro j hj
      have hj0 : (0 : ℝ) < (j : ℝ) := by
        have := (Finset.mem_Icc.mp hj).1
        exact_mod_cast (by omega : 0 < j)
      linarith [Real.add_one_le_exp ((j : ℝ) ^ (-(1/2 : ℝ)))]
  have hsum := sum_le_log_factorial (k + 1) hn
  calc ∏ j ∈ Finset.Icc 2 (k + 1), (1 + (j : ℝ) ^ (-(1/2 : ℝ)))
      ≤ Real.exp (∑ j ∈ Finset.Icc 2 (k + 1), (j : ℝ) ^ (-(1/2 : ℝ))) := hprod
    _ ≤ Real.exp ((Real.log ((k + 1).factorial : ℝ)) ^ (3/4 : ℝ)) := Real.exp_le_exp.mpr hsum

end Work.LinnikAreas
