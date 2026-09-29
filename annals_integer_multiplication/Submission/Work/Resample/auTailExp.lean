import Mathlib
import Submission.Work.Resample.auDefs

/-!
# Exponential tail estimate for the resampling weights (paper Lemma 4.9)

`Work.Resample.auTailExp` bounds the error of truncating the exponential series at
`auNstep p + 1 = 6p + 201` terms on the range `|t| ≤ p + 10` used by the fixed-point weight
recursion `auH`:

`|∑_{k ≤ 6p+200} t^k/k! - exp t| ≤ 2^{-(2p+160)}`.

The proof is the standard Taylor estimate for the exponential series (`Complex.exp_bound'`):
the remainder after `n` terms is at most `2‖t‖^n/n!` as soon as `‖t‖/(n+1) ≤ 1/2`.  Here
`n = 6p + 201` and `‖t‖ ≤ p + 10 ≤ (6p+202)/2`, so it suffices to have
`2|t|^n / n! ≤ 2(p+10)^{6p+201}/(6p+201)! ≤ 2^{-(2p+160)}`, i.e. the pure arithmetic
domination `2(p+10)^{6p+201}·2^{2p+160} ≤ (6p+201)!` (`auTailStirlingBound` below), which
follows from Stirling's lower bound `√(2πn)·(n/e)^n ≤ n!` since `n ≥ 6(p+10)` and `e ≤ 3`.
-/

namespace Work.Resample

/-- Arithmetic core of the exponential tail estimate: for `p ≥ 100`,
`2·(p+10)^{6p+201}·2^{2p+160} ≤ (6p+201)!`.

Via `Stirling.le_factorial_stirling`, `n = 6p+201` satisfies
`n! ≥ √(2πn)(n/e)^n ≥ (6(p+10)/e)^n ≥ (2(p+10))^n = 2^n(p+10)^n`, and
`2^n ≥ 2^{2p+161} = 2·2^{2p+160}` because `n ≥ 2p+161`. -/
theorem auTailStirlingBound (p : ℕ) (hp : 100 ≤ p) :
    ((p : ℝ) + 10) ^ (6 * p + 201) * 2 * (2 : ℝ) ^ (2 * p + 160)
      ≤ ((6 * p + 201).factorial : ℝ) := by
  have hp10 : (0:ℝ) < (p:ℝ) + 10 := by positivity
  have he3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
  have hncast : ((6*p+201 : ℕ) : ℝ) = 6*(p:ℝ)+201 := by push_cast; ring
  -- `2(p+10) ≤ n/e`, i.e. `2(p+10)·e ≤ n`
  have hb : (2:ℝ) * ((p:ℝ)+10) ≤ ((6*p+201 : ℕ) : ℝ) / Real.exp 1 := by
    rw [le_div_iff₀ (Real.exp_pos 1), hncast]
    nlinarith [he3, hp10]
  -- the square root factor is at least `1`
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt (2*Real.pi*((6*p+201:ℕ):ℝ)) := by
    rw [Real.one_le_sqrt]
    have hn1 : (1:ℝ) ≤ ((6*p+201:ℕ):ℝ) := by
      have : (1:ℕ) ≤ 6*p+201 := by omega
      exact_mod_cast this
    have hpi : (6:ℝ) < 2*Real.pi := by linarith [Real.pi_gt_three]
    exact le_of_lt (lt_of_lt_of_le (lt_trans (by norm_num : (1:ℝ) < 6) hpi)
      (le_mul_of_one_le_right (by positivity) hn1))
  have hpow : (2*((p:ℝ)+10))^(6*p+201) ≤ (((6*p+201:ℕ):ℝ)/Real.exp 1)^(6*p+201) :=
    pow_le_pow_left₀ (by positivity) hb _
  -- Stirling: `n! ≥ (2(p+10))^n = 2^n (p+10)^n`
  have hmain : (2:ℝ)^(6*p+201) * ((p:ℝ)+10)^(6*p+201) ≤ ((6*p+201).factorial : ℝ) := by
    have hstirl := Stirling.le_factorial_stirling (6*p+201)
    have h2 : (2*((p:ℝ)+10))^(6*p+201) ≤ ((6*p+201).factorial : ℝ) := by
      calc (2*((p:ℝ)+10))^(6*p+201)
          = 1 * (2*((p:ℝ)+10))^(6*p+201) := (one_mul _).symm
        _ ≤ Real.sqrt (2*Real.pi*((6*p+201:ℕ):ℝ))
              * (((6*p+201:ℕ):ℝ)/Real.exp 1)^(6*p+201) :=
            mul_le_mul hsqrt1 hpow (by positivity) (Real.sqrt_nonneg _)
        _ ≤ _ := hstirl
    rwa [mul_pow] at h2
  have h2p : 2 * (2:ℝ)^(2*p+160) = (2:ℝ)^(2*p+161) := by
    rw [show (2:ℝ)^(2*p+161) = (2:ℝ)^(2*p+160) * 2 by
      rw [show 2*p+161 = 2*p+160+1 by omega, pow_succ]]
    exact mul_comm _ _
  calc ((p:ℝ)+10)^(6*p+201) * 2 * (2:ℝ)^(2*p+160)
      = ((p:ℝ)+10)^(6*p+201) * (2 * (2:ℝ)^(2*p+160)) := by rw [mul_assoc]
    _ = ((p:ℝ)+10)^(6*p+201) * (2:ℝ)^(2*p+161) := by rw [h2p]
    _ ≤ ((p:ℝ)+10)^(6*p+201) * (2:ℝ)^(6*p+201) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    _ = (2:ℝ)^(6*p+201) * ((p:ℝ)+10)^(6*p+201) := mul_comm _ _
    _ ≤ ((6*p+201).factorial : ℝ) := hmain

theorem auTailExp (p : ℕ) (hp : 100 ≤ p) (t : ℝ) (ht : |t| ≤ (p:ℝ) + 10) :
    |∑ k ∈ Finset.range (auNstep p + 1), t ^ k / (k.factorial : ℝ) - Real.exp t| ≤ 1 / (2:ℝ)^(2*p+160) := by
  have hn : auNstep p + 1 = 6 * p + 201 := by simp only [auNstep, auPrec]; ring
  have hp0 : (0:ℝ) ≤ (p:ℝ) := by positivity
  have hpR : (100:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  -- The hypothesis of `Complex.exp_bound'`: `‖t‖ / (n+1) ≤ 1/2` with `n = auNstep p + 1`.
  have hx : ‖((t:ℂ))‖ / (((auNstep p + 1).succ : ℕ) : ℝ) ≤ 1 / 2 := by
    have h2 : (0:ℝ) < (((auNstep p + 1).succ : ℕ) : ℝ) := by positivity
    have hsucc : (((auNstep p + 1).succ : ℕ) : ℝ) = 6*(p:ℝ) + 202 := by
      rw [hn]; push_cast; ring
    rw [div_le_iff₀ h2, hsucc, Complex.norm_real, Real.norm_eq_abs]
    linarith [ht, hpR, hp0]
  have hb := Complex.exp_bound' (x := ((t:ℂ))) (n := auNstep p + 1) hx
  -- transfer the complex partial sum to the real one
  have hsum : (∑ m ∈ Finset.range (auNstep p + 1), (t:ℂ)^m / (m.factorial:ℂ))
      = ((∑ m ∈ Finset.range (auNstep p + 1), t^m / (m.factorial:ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
  have hcast : ‖Complex.exp (t:ℂ) - ∑ m ∈ Finset.range (auNstep p + 1), (t:ℂ)^m / (m.factorial:ℂ)‖
      = |Real.exp t - ∑ m ∈ Finset.range (auNstep p + 1), t^m / (m.factorial:ℝ)| := by
    have h1 : Complex.exp (t:ℂ) - ∑ m ∈ Finset.range (auNstep p + 1), (t:ℂ)^m / (m.factorial:ℂ)
        = ((Real.exp t - ∑ m ∈ Finset.range (auNstep p + 1), t^m / (m.factorial:ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub, Complex.ofReal_exp, hsum]
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
  -- the remainig numerical bound
  have hfacpos : (0:ℝ) < ((6*p+201).factorial : ℝ) := by positivity
  have h2pos : (0:ℝ) < (2:ℝ)^(2*p+160) := by positivity
  have hbound : ‖((t:ℂ))‖^(auNstep p + 1) / ((auNstep p + 1).factorial : ℝ) * 2
      ≤ 1 / (2:ℝ)^(2*p+160) := by
    rw [hn, Complex.norm_real, Real.norm_eq_abs]
    have hstep1 : |t|^(6*p+201) / ((6*p+201).factorial:ℝ) * 2
        ≤ ((p:ℝ)+10)^(6*p+201) / ((6*p+201).factorial:ℝ) * 2 :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg t) ht _) (le_of_lt hfacpos))
        (by norm_num)
    have hstep2 : ((p:ℝ)+10)^(6*p+201) / ((6*p+201).factorial:ℝ) * 2
        = ((p:ℝ)+10)^(6*p+201) * 2 / ((6*p+201).factorial:ℝ) := by
      rw [div_mul_eq_mul_div]
    have harith := auTailStirlingBound p hp
    have hkey : ((p:ℝ)+10)^(6*p+201) * 2 ≤ (1 / (2:ℝ)^(2*p+160)) * ((6*p+201).factorial:ℝ) := by
      rw [one_div, inv_mul_eq_div]
      exact (le_div_iff₀ h2pos).mpr harith
    have hstep3 : ((p:ℝ)+10)^(6*p+201) * 2 / ((6*p+201).factorial:ℝ) ≤ 1 / (2:ℝ)^(2*p+160) := by
      rw [div_le_iff₀ hfacpos]
      exact hkey
    exact le_trans (le_trans hstep1 (le_of_eq hstep2)) hstep3
  calc |∑ k ∈ Finset.range (auNstep p + 1), t ^ k / (k.factorial : ℝ) - Real.exp t|
      = |Real.exp t - ∑ k ∈ Finset.range (auNstep p + 1), t ^ k / (k.factorial : ℝ)| := abs_sub_comm _ _
    _ = ‖Complex.exp (t:ℂ) - ∑ m ∈ Finset.range (auNstep p + 1), (t:ℂ)^m / (m.factorial:ℂ)‖ := hcast.symm
    _ ≤ ‖((t:ℂ))‖^(auNstep p + 1) / ((auNstep p + 1).factorial : ℝ) * 2 := hb
    _ ≤ 1 / (2:ℝ)^(2*p+160) := hbound

end Work.Resample
