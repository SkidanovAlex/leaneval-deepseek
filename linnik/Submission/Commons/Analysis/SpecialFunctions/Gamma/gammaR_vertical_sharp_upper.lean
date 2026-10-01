import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_abs_sq_half
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_log_norm_sub_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_vertical_poly_lower

open Complex
open scoped Real
set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- `exp (π |v|) ≤ 2 cosh (π v)`. -/
private lemma exp_pi_abs_le_two_cosh (v : ℝ) :
    Real.exp (Real.pi * |v|) ≤ 2 * Real.cosh (Real.pi * v) := by
  have h1 : Real.exp (Real.pi * |v|) ≤ 2 * Real.cosh (Real.pi * |v|) := by
    rw [Real.cosh_eq]
    have hpos : 0 < Real.exp (-(Real.pi * |v|)) := Real.exp_pos _
    linarith
  have h2 : Real.cosh (Real.pi * |v|) = Real.cosh (Real.pi * v) := by
    rw [← Real.cosh_abs (Real.pi * v), abs_mul, abs_of_pos Real.pi_pos]
  rwa [h2] at h1

/-- Modulus bound on the critical line: `‖Γ(1/2 + i v)‖ ≤ √(2π) · e^{-π|v|/2}`. -/
private lemma Gamma_half_vertical_le (v : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (v : ℂ))‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|) := by
  set B : ℝ := ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (v : ℂ))‖ with hB
  have hsq : B ^ 2 = Real.pi / Real.cosh (Real.pi * v) := by
    rw [hB]
    exact gamma_abs_sq_half v
  have hcosh : Real.exp (Real.pi * |v|) / 2 ≤ Real.cosh (Real.pi * v) := by
    have h := exp_pi_abs_le_two_cosh v
    linarith
  have hle : B ^ 2 ≤ 2 * Real.pi * Real.exp (-(Real.pi * |v|)) := by
    rw [hsq]
    calc Real.pi / Real.cosh (Real.pi * v)
        ≤ Real.pi / (Real.exp (Real.pi * |v|) / 2) :=
          div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hcosh
      _ = 2 * Real.pi * Real.exp (-(Real.pi * |v|)) := by
          rw [Real.exp_neg]; field_simp
  have hRsq : (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|)) ^ 2
      = 2 * Real.pi * Real.exp (-(Real.pi * |v|)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hBnonneg : 0 ≤ B := norm_nonneg _
  have hRnonneg : 0 ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|) := by
    positivity
  calc B = Real.sqrt (B ^ 2) := (Real.sqrt_sq hBnonneg).symm
    _ ≤ Real.sqrt ((Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [hRsq]
          exact hle
    _ = Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|) := Real.sqrt_sq hRnonneg

/-- Logarithmic half-line bound. -/
private lemma log_Gamma_half_le (v : ℝ) :
    Real.log ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (v : ℂ))‖ ≤
      (1 / 2) * Real.log (2 * Real.pi) - (Real.pi / 2) * |v| := by
  have hBpos : 0 < ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (v : ℂ))‖ := by
    rw [norm_pos_iff]
    exact Gamma_ne_zero_of_re_pos (by simp)
  have hlog := Real.log_le_log hBpos (Gamma_half_vertical_le v)
  rw [Real.log_mul (Real.sqrt_pos.mpr (by positivity)).ne' (Real.exp_ne_zero _),
    Real.log_sqrt (by positivity), Real.log_exp] at hlog
  linarith

/-- Base vertical bound (log form) for `1/2 ≤ u ≤ 2`. -/
private lemma base_bound (u v : ℝ) (hu : 1 / 2 ≤ u) (hu2 : u ≤ 2) :
    Real.log ‖Complex.Gamma ((u : ℂ) + Complex.I * (v : ℂ))‖ ≤
      (1 / 2) * Real.log (2 * Real.pi) - (Real.pi / 2) * |v| +
        (u - 1 / 2) * (Real.log (2 + |v|) + 2) := by
  have hincr := log_norm_Gamma_sub_le (1 / 2) u v le_rfl hu (by linarith : u ≤ 8)
  have hhalf := log_Gamma_half_le v
  have e1 : (u : ℂ) + (v : ℂ) * Complex.I = (u : ℂ) + Complex.I * (v : ℂ) := by ring
  have e2 : ((1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I = (1 / 2 : ℂ) + Complex.I * (v : ℂ) := by
    push_cast; ring
  rw [e1, e2] at hincr
  linarith

/-- `∏_{j<n} (j+2) = (n+1)!`. -/
private lemma prod_range_add_two (n : ℕ) :
    (∏ j ∈ Finset.range n, ((j : ℝ) + 2)) = ((n + 1).factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    rw [show (n + 1 + 1).factorial = (n + 1 + 1) * (n + 1).factorial from
      Nat.factorial_succ (n + 1)]
    push_cast
    ring

/-- `(n+1)! ≤ (2π)^n` for `n ≤ 7`. -/
private lemma factorial_succ_le_two_pi_pow (n : ℕ) (hn : n ≤ 7) :
    ((n + 1).factorial : ℝ) ≤ (2 * Real.pi) ^ n := by
  have h6 : ((n + 1).factorial : ℝ) ≤ (6 : ℝ) ^ n := by
    interval_cases n <;> norm_num [Nat.factorial]
  have hpi : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hpow : (6 : ℝ) ^ n ≤ (2 * Real.pi) ^ n := pow_le_pow_left₀ (by norm_num) hpi n
  linarith

/-- `ascPochhammer ℂ n` evaluated at `z` is `∏_{j<n} (z+j)`. -/
private lemma ascPochhammer_eval_eq_prod (n : ℕ) (z : ℂ) :
    Polynomial.eval z (ascPochhammer ℂ n) = ∏ j ∈ Finset.range n, (z + (j : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, ih, Finset.prod_range_succ,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]

/-- Shift bound: for `1 ≤ u ≤ 2` and `n ≤ 7`,
`log ‖Γ(u+n+iv)‖ ≤ log ‖Γ(u+iv)‖ + n log(1+|v|) + n log(2π)`. -/
private lemma shift_log_bound (u v : ℝ) (n : ℕ) (hu : 1 ≤ u) (hu2 : u ≤ 2) (hn : n ≤ 7) :
    Real.log ‖Complex.Gamma (((u + n : ℝ) : ℂ) + Complex.I * (v : ℂ))‖ ≤
      Real.log ‖Complex.Gamma ((u : ℂ) + Complex.I * (v : ℂ))‖ +
        n * Real.log (1 + |v|) + n * Real.log (2 * Real.pi) := by
  set z : ℂ := (u : ℂ) + Complex.I * (v : ℂ) with hz
  have hzre : z.re = u := by simp [hz]
  have hzneg : ∀ k : ℕ, z ≠ -(k : ℂ) := by
    intro k hk
    have h := congrArg Complex.re hk
    rw [hzre] at h
    simp only [Complex.neg_re, Complex.natCast_re] at h
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith
  have hGammane : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [hzre]; linarith
  have hdiv := Complex.Gamma_add_nat_div_Gamma_eq (n := n) z hzneg
  have hmul : Complex.Gamma (z + (n : ℂ)) =
      Complex.Gamma z * Polynomial.eval z (ascPochhammer ℂ n) := by
    have h := (div_eq_iff hGammane).mp hdiv
    rw [h]; ring
  have hzeq : z + (n : ℂ) = ((u + n : ℝ) : ℂ) + Complex.I * (v : ℂ) := by
    rw [hz]; push_cast; ring
  have heval_bound : ‖Polynomial.eval z (ascPochhammer ℂ n)‖ ≤
      (2 * Real.pi) ^ n * (1 + |v|) ^ n := by
    rw [ascPochhammer_eval_eq_prod n z, norm_prod]
    have hpt : ∀ j ∈ Finset.range n, ‖z + (j : ℂ)‖ ≤ ((j : ℝ) + 2) * (1 + |v|) := by
      intro j hj
      have hzjeq : z + (j : ℂ) = ((u + j : ℝ) : ℂ) + Complex.I * (v : ℂ) := by
        rw [hz]; push_cast; ring
      rw [hzjeq]
      have hnorm : ‖((u + j : ℝ) : ℂ) + Complex.I * (v : ℂ)‖ ≤ (u + j) + |v| := by
        have h1 : ‖((u + j : ℝ) : ℂ) + Complex.I * (v : ℂ)‖ ≤ |(u + j : ℝ)| + |v| := by
          calc ‖((u + j : ℝ) : ℂ) + Complex.I * (v : ℂ)‖
              ≤ ‖((u + j : ℝ) : ℂ)‖ + ‖Complex.I * (v : ℂ)‖ := norm_add_le _ _
            _ = |(u + j : ℝ)| + |v| := by
                simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul]
        rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u + j)] at h1
      have h1 : (u + j) + |v| ≤ (u + j) * (1 + |v|) := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
        nlinarith [abs_nonneg v, hu]
      have h2 : (u + j) * (1 + |v|) ≤ ((j : ℝ) + 2) * (1 + |v|) := by
        have : (0 : ℝ) ≤ 1 + |v| := by positivity
        apply mul_le_mul_of_nonneg_right _ this
        linarith
      linarith
    calc ∏ j ∈ Finset.range n, ‖z + (j : ℂ)‖
        ≤ ∏ j ∈ Finset.range n, (((j : ℝ) + 2) * (1 + |v|)) :=
          Finset.prod_le_prod₀ (fun j hj => norm_nonneg _) hpt
      _ = (∏ j ∈ Finset.range n, ((j : ℝ) + 2)) * (1 + |v|) ^ n := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      _ = ((n + 1).factorial : ℝ) * (1 + |v|) ^ n := by rw [prod_range_add_two]
      _ ≤ (2 * Real.pi) ^ n * (1 + |v|) ^ n :=
          mul_le_mul_of_nonneg_right (factorial_succ_le_two_pi_pow n hn) (by positivity)
  have hevalne : Polynomial.eval z (ascPochhammer ℂ n) ≠ 0 := by
    intro h0
    have hzn : Complex.Gamma (z + (n : ℂ)) = 0 := by rw [hmul, h0, mul_zero]
    have hre : (z + (n : ℂ)).re = u + n := by
      rw [hz]; simp [Complex.add_re]
    exact Complex.Gamma_ne_zero_of_re_pos (by rw [hre]; positivity) hzn
  have hlogmul : Real.log ‖Complex.Gamma (z + (n : ℂ))‖
      = Real.log ‖Complex.Gamma z‖ +
        Real.log ‖Polynomial.eval z (ascPochhammer ℂ n)‖ := by
    rw [hmul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hGammane) (norm_ne_zero_iff.mpr hevalne)]
  have hlogeval : Real.log ‖Polynomial.eval z (ascPochhammer ℂ n)‖
      ≤ n * Real.log (1 + |v|) + n * Real.log (2 * Real.pi) := by
    have hpos : 0 < ‖Polynomial.eval z (ascPochhammer ℂ n)‖ := norm_pos_iff.mpr hevalne
    have h1 := Real.log_le_log hpos heval_bound
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h1
    linarith
  rw [← hzeq, hz, hlogmul]
  linarith

/-- Numeric inequality `2 log π ≥ 1 + (1/2) log (2π)`. -/
private lemma numer : (0 : ℝ) ≤ 2 * Real.log Real.pi - 1 - (1 / 2) * Real.log (2 * Real.pi) := by
  have hlogpi1 : 1 ≤ Real.log Real.pi := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (by linarith [Real.exp_one_lt_three, Real.pi_gt_three] : Real.exp 1 ≤ Real.pi)
    rwa [Real.log_exp] at h
  have hlog2_1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by linarith [Real.exp_one_gt_two] : (2 : ℝ) ≤ Real.exp 1)
    rwa [Real.log_exp] at h
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero]
  linarith

/-- Core real inequality reducing the target to the base + shift bounds. -/
private lemma core_ineq (a u v : ℝ) (n : ℕ) (hau : a = u + n) (hu1 : 1 / 2 ≤ u)
    (hu2 : u ≤ 2) :
    -a * Real.log Real.pi +
        ((1 / 2) * Real.log (2 * Real.pi) - (Real.pi / 2) * |v| +
          (u - 1 / 2) * (Real.log (2 + |v|) + 2) + n * Real.log (1 + |v|) +
            n * Real.log (2 * Real.pi))
      ≤ (a - 1 / 2) * Real.log (2 + 2 * |v|) + 2 - (Real.pi / 2) * |v| := by
  have hV0 : 0 ≤ |v| := abs_nonneg v
  have h1V : (0 : ℝ) < 1 + |v| := by linarith
  have hlog22 : Real.log (2 + 2 * |v|) = Real.log 2 + Real.log (1 + |v|) := by
    rw [show (2 : ℝ) + 2 * |v| = 2 * (1 + |v|) by ring,
      Real.log_mul (by norm_num) (ne_of_gt h1V)]
  have hlog2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  have hlogpi_le2 : Real.log Real.pi ≤ 2 := by
    have hp : Real.pi < Real.exp 1 ^ 2 := by
      have h4 : (4 : ℝ) < Real.exp 1 ^ 2 := by nlinarith [Real.exp_one_gt_two]
      linarith [Real.pi_lt_four]
    have h := Real.log_lt_log Real.pi_pos hp
    rw [Real.log_pow, Real.log_exp] at h
    norm_num at h
    linarith
  have hA : 0 ≤ (u - 1 / 2) * (Real.log 2 + Real.log (1 + |v|) - Real.log (2 + |v|)) := by
    apply mul_nonneg (by linarith)
    have hle : Real.log (2 + |v|) ≤ Real.log 2 + Real.log (1 + |v|) := by
      rw [← hlog22]
      exact Real.log_le_log (by positivity) (by linarith)
    linarith
  have hB : 0 ≤ 3 - u * (2 - Real.log Real.pi) - (1 / 2) * Real.log (2 * Real.pi) := by
    have hup : u * (2 - Real.log Real.pi) ≤ 2 * (2 - Real.log Real.pi) :=
      mul_le_mul_of_nonneg_right hu2 (by linarith)
    linarith [numer]
  have hid : (a - 1 / 2) * Real.log (2 + 2 * |v|) + 2 - (Real.pi / 2) * |v| -
      (-a * Real.log Real.pi +
        ((1 / 2) * Real.log (2 * Real.pi) - (Real.pi / 2) * |v| +
          (u - 1 / 2) * (Real.log (2 + |v|) + 2) + n * Real.log (1 + |v|) +
            n * Real.log (2 * Real.pi)))
      = (u - 1 / 2) * (Real.log 2 + Real.log (1 + |v|) - Real.log (2 + |v|)) +
        (3 - u * (2 - Real.log Real.pi) - (1 / 2) * Real.log (2 * Real.pi)) := by
    rw [hlog22, hlog2pi, hau]
    push_cast
    ring
  linarith [hA, hB, hid]

theorem gammaR_vertical_sharp_upper (σ t : ℝ) (hσ : 1 ≤ σ) (hσ' : σ ≤ 16) :
    ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      Real.exp (((σ - 1) / 2) * Real.log (2 + |t|) + 2 - (Real.pi / 4) * |t|) := by
  set a : ℝ := σ / 2 with ha
  set v : ℝ := t / 2 with hv
  have ha1 : 1 / 2 ≤ a := by rw [ha]; linarith
  have ha8 : a ≤ 8 := by rw [ha]; linarith
  have hσpos : 0 < σ := by linarith
  have hpos : 0 < ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
    rw [norm_gammaR_vertical_eq σ t]
    apply mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    rw [norm_pos_iff]
    apply Complex.Gamma_ne_zero_of_re_pos
    simp [ha, hv]
    linarith
  have hvabs : (Real.pi / 2) * |v| = (Real.pi / 4) * |t| := by
    rw [hv, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
  have habs2 : (2 : ℝ) + 2 * |v| = 2 + |t| := by
    rw [hv, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
  have hlogR : Real.log ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * (t : ℂ))‖
      = -a * Real.log Real.pi + Real.log ‖Complex.Gamma ((a : ℂ) + Complex.I * (v : ℂ))‖ := by
    have h := log_norm_gammaR_eq σ t hσpos
    have e1 : (σ / 2 : ℝ) = a := ha.symm
    have e2 : (t / 2 : ℝ) = v := hv.symm
    rw [e1, e2] at h
    exact h
  have hσ1 : (σ - 1) / 2 = a - 1 / 2 := by rw [ha]; ring
  have h2v : Real.log (2 + 2 * |v|) = Real.log (2 + |t|) := by rw [habs2]
  have key : Real.log ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * (t : ℂ))‖
      ≤ ((σ - 1) / 2) * Real.log (2 + |t|) + 2 - (Real.pi / 4) * |t| := by
    rw [hlogR, hσ1, ← h2v, ← hvabs]
    by_cases ha2 : a ≤ 2
    · have hL := base_bound a v ha1 ha2
      have hcore := core_ineq a a v 0 (by ring) ha1 ha2
      simp only [Nat.cast_zero, zero_mul, add_zero] at hcore
      linarith
    · push_neg at ha2
      let m : ℕ := Nat.floor a
      let n : ℕ := m - 1
      let u : ℝ := a - n
      have hm_le : (m : ℝ) ≤ a := by
        have h0 : (0 : ℝ) ≤ a := by linarith
        exact Nat.floor_le h0
      have hm_lt : a < (m : ℝ) + 1 := Nat.lt_floor_add_one a
      have hm2 : 2 ≤ m := by
        apply Nat.le_floor
        exact_mod_cast (le_of_lt ha2 : (2 : ℝ) ≤ a)
      have hncast : (n : ℝ) = (m : ℝ) - 1 := by
        dsimp [n]
        rw [Nat.cast_sub (by omega : 1 ≤ m)]
        norm_num
      have hu_ge1 : 1 ≤ u := by dsimp [u]; rw [hncast]; linarith
      have hu_le2 : u ≤ 2 := by dsimp [u]; rw [hncast]; linarith
      have hu_half : 1 / 2 ≤ u := by linarith
      have hau : a = u + n := by dsimp [u]; ring
      have hn7 : n ≤ 7 := by
        have h7 : (n : ℝ) ≤ 7 := by
          have h := hau; push_cast at h; linarith
        exact_mod_cast h7
      have hu_ne : ((u + n : ℝ) : ℂ) = (a : ℂ) := by rw [← hau]
      have hbase := base_bound u v hu_half hu_le2
      have hshift := shift_log_bound u v n hu_ge1 hu_le2 hn7
      have hL : Real.log ‖Complex.Gamma ((a : ℂ) + Complex.I * (v : ℂ))‖
          ≤ (1 / 2) * Real.log (2 * Real.pi) - (Real.pi / 2) * |v| +
            (u - 1 / 2) * (Real.log (2 + |v|) + 2) + n * Real.log (1 + |v|) +
              n * Real.log (2 * Real.pi) := by
        rw [← hu_ne]
        linarith
      have hcore := core_ineq a u v n hau hu_half hu_le2
      linarith
  calc ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * (t : ℂ))‖
      = Real.exp (Real.log ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * (t : ℂ))‖) :=
        (Real.exp_log hpos).symm
    _ ≤ Real.exp (((σ - 1) / 2) * Real.log (2 + |t|) + 2 - (Real.pi / 4) * |t|) :=
        Real.exp_le_exp.mpr key

end Commons.Analysis.SpecialFunctions.Gamma
