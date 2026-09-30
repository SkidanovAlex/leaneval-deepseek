import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

/-- The product form of the "finitely many primes" count bound:
`(x^{1/4}/ε + 1)^4 · (log(exp(x^{1/8}/ε · 384 log x)/exp(384 log x)) + 1)^2 ≤ x^{5/2} (log x)^2`
for all sufficiently large `x`, uniformly in `0 < ε ≤ 1`. -/
theorem fp_prod (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ L : ℝ, ∀ x : ℝ, L ≤ x →
      (x ^ ((1 : ℝ) / 4) / ε + 1) ^ 4 *
        (Real.log (Real.exp (x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x)) /
          Real.exp (384 * Real.log x)) + 1) ^ 2
        ≤ x ^ ((5 : ℝ) / 2) * (Real.log x) ^ 2 := by
  refine ⟨max (Real.exp 1) (16 * 385^2 / ε^6), ?_⟩
  intro x hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxL : 16 * 385^2 / ε^6 ≤ x := le_trans (le_max_right _ _) hx
  have hexp1_gt1 : (1 : ℝ) < Real.exp 1 := by
    rw [Real.one_lt_exp_iff]; norm_num
  have hx1 : 1 ≤ x := le_trans (le_of_lt hexp1_gt1) hxe
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlog1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h
  have hlog0 : 0 ≤ Real.log x := by linarith
  -- simplify the logarithmic factor
  have hsimp :
      Real.log (Real.exp (x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x)) /
        Real.exp (384 * Real.log x))
        = x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x) - 384 * Real.log x := by
    rw [← Real.exp_sub, Real.log_exp]
  rw [hsimp]
  -- bound the first factor
  have hA : (x ^ ((1 : ℝ) / 4) / ε + 1) ^ 4 ≤ 16 * x / ε^4 := by
    have hd1 : 1 ≤ x ^ ((1 : ℝ) / 4) / ε := by
      rw [le_div_iff₀ hε]
      have hr1 : 1 ≤ x ^ ((1 : ℝ) / 4) := Real.one_le_rpow hx1 (by norm_num)
      linarith
    have hpow : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
    have hA' : x ^ ((1 : ℝ) / 4) / ε + 1 ≤ 2 * (x ^ ((1 : ℝ) / 4) / ε) := by linarith
    have hle : (x ^ ((1 : ℝ) / 4) / ε + 1) ^ 4 ≤ (2 * (x ^ ((1 : ℝ) / 4) / ε)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hA' 4
    have h2 : (2 * (x ^ ((1 : ℝ) / 4) / ε)) ^ 4 = 16 * x / ε^4 := by
      rw [mul_pow, div_pow]
      norm_num
      rw [hpow]; ring
    rw [h2] at hle; exact hle
  -- bound the second factor
  have hB : (x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x) - 384 * Real.log x + 1)^2
      ≤ 385^2 * x ^ ((1 : ℝ) / 4) * (Real.log x)^2 / ε^2 := by
    have hT1 : 1 ≤ x ^ ((1 : ℝ) / 8) / ε := by
      rw [le_div_iff₀ hε]
      have hr8 : 1 ≤ x ^ ((1 : ℝ) / 8) := Real.one_le_rpow hx1 (by norm_num)
      linarith
    have hTl : 1 ≤ x ^ ((1 : ℝ) / 8) / ε * Real.log x := by nlinarith [hT1, hlog1]
    have hpow : (x ^ ((1 : ℝ) / 8)) ^ 2 = x ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
    have hB2 : x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x) - 384 * Real.log x + 1
        ≤ 385 * (x ^ ((1 : ℝ) / 8) / ε) * Real.log x := by
      nlinarith [hTl, hlog0]
    have hBsq : (x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x) - 384 * Real.log x + 1)^2
        ≤ (385 * (x ^ ((1 : ℝ) / 8) / ε) * Real.log x)^2 :=
      pow_le_pow_left₀ (by nlinarith [hT1, hlog1]) hB2 2
    have h3 : (385 * (x ^ ((1 : ℝ) / 8) / ε) * Real.log x)^2
        = 385^2 * x ^ ((1 : ℝ) / 4) * (Real.log x)^2 / ε^2 := by
      rw [mul_pow, mul_pow, div_pow, hpow]; ring
    rw [h3] at hBsq; exact hBsq
  -- combine
  have hcombine :
      (x ^ ((1 : ℝ) / 4) / ε + 1) ^ 4 *
        (x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x) - 384 * Real.log x + 1)^2
      ≤ (16 * x / ε^4) * (385^2 * x ^ ((1 : ℝ) / 4) * (Real.log x)^2 / ε^2) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have heq : (16 * x / ε^4) * (385^2 * x ^ ((1 : ℝ) / 4) * (Real.log x)^2 / ε^2)
      = (16 * 385^2 / ε^6) * (x * x ^ ((1 : ℝ) / 4)) * (Real.log x)^2 := by
    field_simp
  have hxx : x * x ^ ((1 : ℝ) / 4) = x ^ ((5 : ℝ) / 4) := by
    nth_rewrite 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hxpos]; norm_num
  have hC5 : 16 * 385^2 / ε^6 ≤ x ^ ((5 : ℝ) / 4) := by
    have h : x ^ (1 : ℝ) ≤ x ^ ((5 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at h; linarith
  have hxx52 : x ^ ((5 : ℝ) / 4) * x ^ ((5 : ℝ) / 4) = x ^ ((5 : ℝ) / 2) := by
    rw [← Real.rpow_add hxpos]; norm_num
  have hprod : (16 * 385^2 / ε^6) * (x * x ^ ((1 : ℝ) / 4)) * (Real.log x)^2
      ≤ x ^ ((5 : ℝ) / 2) * (Real.log x)^2 := by
    rw [hxx, ← hxx52]
    have h1 : 16 * 385^2 / ε^6 * x ^ ((5 : ℝ) / 4) ≤ x ^ ((5 : ℝ) / 4) * x ^ ((5 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hC5 (Real.rpow_nonneg hxpos.le _)
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  calc
    (x ^ ((1 : ℝ) / 4) / ε + 1) ^ 4 *
        (x ^ ((1 : ℝ) / 8) / ε * (384 * Real.log x) - 384 * Real.log x + 1)^2
        ≤ (16 * x / ε^4) * (385^2 * x ^ ((1 : ℝ) / 4) * (Real.log x)^2 / ε^2) := hcombine
    _ = (16 * 385^2 / ε^6) * (x * x ^ ((1 : ℝ) / 4)) * (Real.log x)^2 := heq
    _ ≤ x ^ ((5 : ℝ) / 2) * (Real.log x)^2 := hprod

end Work.BMF.mr_core
