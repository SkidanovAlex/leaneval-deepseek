import Mathlib

namespace Work.LinnikAreas.HypAAux

/-!
# `∏_{2 ≤ j ≤ k+1} (1 + j^{-1/2}) ≤ exp((log (k+1)!)^{3/4})`

Every factor is dominated by an exponential, `1 + j^{-1/2} ≤ exp (j^{-1/2})`, so the
product is at most `exp (∑_{2 ≤ j ≤ k+1} j^{-1/2})`.  The heart of the argument is the
elementary estimate

`∑_{2 ≤ j ≤ n} j^{-1/2} ≤ (log n!)^{3/4}`   (`n ≥ 2`),

proved by induction on `n`.  The inductive step needs the increment of `(log ·!)^{3/4}` to
dominate `(n+1)^{-1/2}`; this follows from the tangent-line (concavity) inequality for
`x ↦ x^{3/4}` together with `log (n+1)! ≤ (n+1) log (n+1)` and the numerical bound
`(3/4) B^{3/4} (n+1)^{-1/4} ≥ (n+1)^{-1/2}` valid for `B ≥ log 3` and `n + 1 ≥ 3`.
-/

/-! ## Elementary estimates -/

/-- `log (m+1)! = log m! + log (m+1)`. -/
private lemma log_factorial_succ (m : ℕ) :
    Real.log (((m + 1).factorial : ℕ) : ℝ)
      = Real.log ((m.factorial : ℕ) : ℝ) + Real.log ((m : ℝ) + 1) := by
  rw [Nat.factorial_succ]
  push_cast
  rw [Real.log_mul (by positivity) (by exact_mod_cast Nat.factorial_ne_zero m)]
  ring

/-- `log m! ≤ m log m`. -/
private lemma log_factorial_le_mul_log (m : ℕ) :
    Real.log ((m.factorial : ℕ) : ℝ) ≤ (m : ℝ) * Real.log (m : ℝ) := by
  have hfac : (m.factorial : ℕ) ≤ m ^ m := Nat.factorial_le_pow m
  have hcast : ((m.factorial : ℕ) : ℝ) ≤ ((m : ℝ)) ^ m := by
    calc ((m.factorial : ℕ) : ℝ) ≤ ((m ^ m : ℕ) : ℝ) := by exact_mod_cast hfac
      _ = (m : ℝ) ^ m := by rw [Nat.cast_pow]
  have hpos : 0 < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
  calc Real.log ((m.factorial : ℕ) : ℝ) ≤ Real.log ((m : ℝ) ^ m) := Real.log_le_log hpos hcast
    _ = (m : ℝ) * Real.log (m : ℝ) := by rw [Real.log_pow]

/-- Tangent-line (concavity) inequality for `x ↦ x ^ (3/4)`: for `a, b ≥ 0` and `a + b > 0`
the increment of `x ↦ x ^ (3/4)` over `[a, a+b]` dominates `(3/4) b (a+b)^{-1/4}`. -/
private lemma rpow_three_quarters_sub_ge (a b : ℝ) (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hab : 0 < a + b) :
    (3 / 4 : ℝ) * b * (a + b) ^ (-(1 / 4 : ℝ))
      ≤ (a + b) ^ (3 / 4 : ℝ) - a ^ (3 / 4 : ℝ) := by
  set V : ℝ := a + b with hVdef
  have hVpos : 0 < V := by rw [hVdef]; exact hab
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have haV : 0 ≤ a / V := div_nonneg ha hVpos.le
  -- Bernoulli / tangent inequality at `w = a / V`
  have hbern := rpow_one_add_le_one_add_mul_self (s := a / V - 1)
      (by linarith) (p := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hbern' : (a / V) ^ (3 / 4 : ℝ) ≤ 1 / 4 + (3 / 4 : ℝ) * (a / V) := by
    have h1 : (1 : ℝ) + (a / V - 1) = a / V := by ring
    have h2 : (1 : ℝ) + (3 / 4 : ℝ) * (a / V - 1) = 1 / 4 + (3 / 4 : ℝ) * (a / V) := by ring
    rw [h1, h2] at hbern
    exact hbern
  have hbV : b / V = 1 - a / V := by field_simp; ring
  have hkey : (3 / 4 : ℝ) * (b / V) + (a / V) ^ (3 / 4 : ℝ) ≤ 1 := by
    rw [hbV]
    nlinarith [hbern']
  have hV34 : 0 < V ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hVpos _
  have hmul := mul_le_mul_of_nonneg_left hkey hV34.le
  rw [mul_one] at hmul
  have h1 : V ^ (3 / 4 : ℝ) * (a / V) ^ (3 / 4 : ℝ) = a ^ (3 / 4 : ℝ) := by
    rw [← Real.mul_rpow hVpos.le haV]
    have : V * (a / V) = a := by field_simp
    rw [this]
  have hdiv : V ^ (3 / 4 : ℝ) / V = V ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_sub_one hVne (3 / 4 : ℝ), show (3 / 4 : ℝ) - 1 = -(1 / 4 : ℝ) by norm_num]
  have h2 : V ^ (3 / 4 : ℝ) * (b / V) = b * V ^ (-(1 / 4 : ℝ)) := by
    rw [← hdiv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hX : V ^ (3 / 4 : ℝ) * ((3 / 4 : ℝ) * (b / V))
      = (3 / 4 : ℝ) * b * V ^ (-(1 / 4 : ℝ)) := by
    rw [show V ^ (3 / 4 : ℝ) * ((3 / 4 : ℝ) * (b / V))
          = (3 / 4 : ℝ) * (V ^ (3 / 4 : ℝ) * (b / V)) by ring, h2]
    ring
  rw [mul_add, hX, h1] at hmul
  linarith [hmul]

/-- `2^{-1/2} ≤ (log 2)^{3/4}`. -/
private lemma inv_sqrt_two_le_log_two_rpow :
    (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (Real.log 2) ^ (3 / 4 : ℝ) := by
  have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog0 : 0 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = ((2 : ℝ) ^ (-(2 : ℝ))) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h3 : (Real.log 2) ^ (3 / 4 : ℝ) = ((Real.log 2) ^ (3 : ℝ)) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_mul hlog0]
    norm_num
  rw [h2, h3]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  simp only [Real.rpow_ofNat]
  have hp : (2 / 3 : ℝ) ^ 3 ≤ (Real.log 2) ^ 3 := pow_le_pow_left₀ (by norm_num) hlog 3
  norm_num at hp ⊢
  linarith

/-- For `x ≥ 3` and `B ≥ log 3`: `x^{-1/2} ≤ (3/4) B (x B)^{-1/4}`. -/
private lemma inv_sqrt_le_three_quarters_mul (x B : ℝ) (hx : 3 ≤ x) (hB : Real.log 3 ≤ B) :
    x ^ (-(1 / 2 : ℝ)) ≤ (3 / 4 : ℝ) * B * (x * B) ^ (-(1 / 4 : ℝ)) := by
  have hxpos : 0 < x := by linarith
  have hBpos : 0 < B := by linarith [Real.log_three_gt_d9]
  have hB3 : 0 < B ^ 3 := pow_pos hBpos 3
  have hx12 : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hBM : (Real.log 3) ^ 3 ≤ B ^ 3 :=
    pow_le_pow_left₀ (by linarith [Real.log_three_gt_d9]) hB 3
  have hnum : (1 : ℝ) ≤ (3 / 4 : ℝ) ^ 4 * (1.0986122885 : ℝ) ^ 3 * 3 := by norm_num
  have hkey : (1 : ℝ) ≤ (3 / 4 : ℝ) ^ 4 * B ^ 3 * x := by
    have h34 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ 4 := by norm_num
    have hlog3R : (1.0986122885 : ℝ) ^ 3 ≤ B ^ 3 :=
      le_trans (pow_le_pow_left₀ (by norm_num) (le_of_lt Real.log_three_gt_d9) 3) hBM
    have h1 : (3 / 4 : ℝ) ^ 4 * (1.0986122885 : ℝ) ^ 3 ≤ (3 / 4 : ℝ) ^ 4 * B ^ 3 :=
      mul_le_mul_of_nonneg_left hlog3R h34
    have h2 : (3 / 4 : ℝ) ^ 4 * (1.0986122885 : ℝ) ^ 3 * 3 ≤ (3 / 4 : ℝ) ^ 4 * B ^ 3 * 3 := by
      linarith
    have h3 : (3 / 4 : ℝ) ^ 4 * B ^ 3 * 3 ≤ (3 / 4 : ℝ) ^ 4 * B ^ 3 * x :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    linarith
  have hB34 : B * B ^ (-(1 / 4 : ℝ)) = B ^ (3 / 4 : ℝ) := by
    have h := Real.rpow_add hBpos (1 : ℝ) (-(1 / 4 : ℝ))
    rw [show (1 : ℝ) + (-(1 / 4)) = (3 / 4 : ℝ) by norm_num, Real.rpow_one] at h
    exact h.symm
  have hmul2 : (3 / 4 : ℝ) * B * (x * B) ^ (-(1 / 4 : ℝ))
      = (3 / 4 : ℝ) * B ^ (3 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ)) := by
    rw [Real.mul_rpow hxpos.le hBpos.le]
    rw [show (3 / 4 : ℝ) * B * (x ^ (-(1 / 4 : ℝ)) * B ^ (-(1 / 4 : ℝ)))
          = (3 / 4 : ℝ) * x ^ (-(1 / 4 : ℝ)) * (B * B ^ (-(1 / 4 : ℝ))) by ring, hB34]
    ring
  rw [hmul2]
  rw [← mul_le_mul_iff_of_pos_right hx12]
  have hxm : x ^ (-(1 / 4 : ℝ)) * x ^ (1 / 2 : ℝ) = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hxpos, show (-(1 / 4 : ℝ)) + (1 / 2) = (1 / 4 : ℝ) by norm_num]
  have hlin : x ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hxpos, show (-(1 / 2 : ℝ)) + (1 / 2) = (0 : ℝ) by norm_num, Real.rpow_zero]
  rw [hlin, mul_assoc ((3 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) (x ^ (-(1 / 4 : ℝ))) (x ^ (1 / 2 : ℝ)), hxm]
  refine (Real.rpow_le_rpow_iff (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    (by norm_num : (0 : ℝ) < 4)).mp ?_
  rw [Real.one_rpow]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ (3 / 4 : ℝ)) (by positivity)]
  rw [← Real.rpow_mul hBpos.le (3 / 4) 4, ← Real.rpow_mul hxpos.le (1 / 4) 4]
  rw [show (3 / 4 : ℝ) * 4 = (3 : ℝ) by norm_num, show (1 / 4 : ℝ) * 4 = (1 : ℝ) by norm_num]
  simp only [Real.rpow_ofNat, Real.rpow_one]
  linarith [hkey]

/-! ## The inductive sum estimate -/

/-- The increment of `(log n!)^{3/4}` between `n = m` and `n = m + 1` is at least
`(m+1)^{-1/2}`. -/
private lemma log_factorial_increment (m : ℕ) (hm : 2 ≤ m) :
    ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))
      ≤ (Real.log (((m + 1).factorial : ℕ) : ℝ)) ^ (3 / 4 : ℝ)
        - (Real.log ((m.factorial : ℕ) : ℝ)) ^ (3 / 4 : ℝ) := by
  set A : ℝ := Real.log ((m.factorial : ℕ) : ℝ) with hA
  set B : ℝ := Real.log ((m : ℝ) + 1) with hB
  have hm1 : (1 : ℕ) ≤ m.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hA0 : 0 ≤ A := by rw [hA]; exact Real.log_nonneg (by exact_mod_cast hm1)
  have hB0 : 0 < B := by
    rw [hB]
    exact Real.log_pos (by linarith [show (2 : ℝ) ≤ (m : ℝ) by exact_mod_cast hm])
  have hV : Real.log (((m + 1).factorial : ℕ) : ℝ) = A + B := by
    rw [log_factorial_succ m, hA, hB]
  have hunit : 1 < (m + 1).factorial := Nat.one_lt_factorial.mpr (by omega)
  have hVpos : 0 < A + B := by
    rw [← hV]
    exact Real.log_pos (by exact_mod_cast hunit)
  have htan : (3 / 4 : ℝ) * B * (A + B) ^ (-(1 / 4 : ℝ))
      ≤ (A + B) ^ (3 / 4 : ℝ) - A ^ (3 / 4 : ℝ) :=
    rpow_three_quarters_sub_ge A B hA0 hB0.le hVpos
  have hABm : A + B ≤ ((m : ℝ) + 1) * B := by
    rw [← hV]
    calc Real.log (((m + 1).factorial : ℕ) : ℝ)
        ≤ ((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ) :=
          log_factorial_le_mul_log (m + 1)
      _ = ((m : ℝ) + 1) * B := by push_cast; rw [hB]
  have hrpow : (((m : ℝ) + 1) * B) ^ (-(1 / 4 : ℝ)) ≤ (A + B) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hVpos hABm (by norm_num)
  have h3 : ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))
      ≤ (3 / 4 : ℝ) * B * (((m : ℝ) + 1) * B) ^ (-(1 / 4 : ℝ)) :=
    inv_sqrt_le_three_quarters_mul ((m : ℝ) + 1) B
      (by exact_mod_cast (by omega : 3 ≤ m + 1))
      (by rw [hB]
          exact Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 3 ≤ m + 1)))
  have hcomb : ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))
      ≤ (3 / 4 : ℝ) * B * (A + B) ^ (-(1 / 4 : ℝ)) :=
    h3.trans (mul_le_mul_of_nonneg_left hrpow (by positivity))
  have hstep : ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))
      ≤ (Real.log (((m + 1).factorial : ℕ) : ℝ)) ^ (3 / 4 : ℝ) - A ^ (3 / 4 : ℝ) := by
    rw [hV]
    exact hcomb.trans htan
  rw [hA] at hstep
  exact hstep

/-- `∑_{2 ≤ j ≤ n} j^{-1/2} ≤ (log n!)^{3/4}` for `n ≥ 2`. -/
private lemma sum_rpow_le_log_factorial (n : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.Icc 2 n, (j : ℝ) ^ (-(1 / 2 : ℝ)))
      ≤ (Real.log (n.factorial : ℝ)) ^ (3 / 4 : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    simpa using inv_sqrt_two_le_log_two_rpow
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1)]
    have hcast : (((m + 1 : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) = ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
      push_cast
      rfl
    rw [hcast]
    have hinc := log_factorial_increment m hm
    linarith

/-! ## The main theorem -/

theorem prod_Icc_two_one_add_rpow_le_exp (k : ℕ) (hk : 1 ≤ k) :
    ∏ j ∈ Finset.Icc 2 (k + 1), (1 + (j : ℝ) ^ (-(1 / 2 : ℝ)))
      ≤ Real.exp ((Real.log ((k + 1).factorial : ℝ)) ^ (3 / 4 : ℝ)) := by
  have hprod : ∏ j ∈ Finset.Icc 2 (k + 1), (1 + (j : ℝ) ^ (-(1 / 2 : ℝ)))
      ≤ Real.exp (∑ j ∈ Finset.Icc 2 (k + 1), (j : ℝ) ^ (-(1 / 2 : ℝ))) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun j _ => by positivity) ?_
    intro j _
    have h := Real.add_one_le_exp ((j : ℝ) ^ (-(1 / 2 : ℝ)))
    linarith
  have hsum := sum_rpow_le_log_factorial (k + 1) (by omega)
  calc ∏ j ∈ Finset.Icc 2 (k + 1), (1 + (j : ℝ) ^ (-(1 / 2 : ℝ)))
      ≤ Real.exp (∑ j ∈ Finset.Icc 2 (k + 1), (j : ℝ) ^ (-(1 / 2 : ℝ))) := hprod
    _ ≤ Real.exp ((Real.log ((k + 1).factorial : ℝ)) ^ (3 / 4 : ℝ)) :=
        Real.exp_le_exp.mpr hsum

end Work.LinnikAreas.HypAAux
