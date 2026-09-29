import Mathlib

namespace Work.TMC14Core

open Polynomial Complex

/-- The roots-of-unity product formula: for a primitive `N`-th root of unity `ω`,
`∏_{t<N} (1 - c * ω^t) = 1 - c^N`.  Derived from the factorisation
`X^N - c^N = ∏_{t<N} (X - ω^t c)` by evaluating at `X = 1`. -/
theorem prodOneSubPow (N : ℕ) (hN : 0 < N) (c ω : ℂ) (hω : IsPrimitiveRoot ω N) :
    ∏ t ∈ Finset.range N, (1 - c * ω ^ t) = 1 - c ^ N := by
  have h := X_pow_sub_C_eq_prod hω hN (show c ^ N = c ^ N from rfl)
  have h2 := congrArg (Polynomial.eval (1 : ℂ)) h
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod, one_pow] at h2
  rw [h2]
  exact Finset.prod_congr rfl (fun t _ => by ring)

/-- `2 sin x = -i (e^{ix} - e^{-ix})` over the complex numbers. -/
theorem twoSinComplex2 (x : ℝ) :
    (2 * Real.sin x : ℂ) =
      (-Complex.I) * (Complex.exp (↑x * Complex.I) - Complex.exp (-(↑x * Complex.I))) := by
  have hsub : Complex.exp (↑x * Complex.I) - Complex.exp (-(↑x * Complex.I)) =
      2 * Complex.I * (Real.sin x : ℂ) := by
    have h2 : -(↑x * Complex.I) = (↑(-x) : ℂ) * Complex.I := by push_cast; ring
    rw [h2, Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hsub]
  push_cast
  rw [show (-Complex.I) * (2 * Complex.I * Complex.sin (↑x : ℂ)) = 2 * Complex.sin (↑x : ℂ) by
    rw [show (-Complex.I) * (2 * Complex.I * Complex.sin (↑x : ℂ)) =
        2 * ((-Complex.I) * Complex.I) * Complex.sin (↑x : ℂ) by ring,
      show (-Complex.I) * Complex.I = (1 : ℂ) by rw [neg_mul, Complex.I_mul_I, neg_neg],
      mul_one]]

/-- `2 sin x = -i (e^{2ix} - 1) e^{-ix}` over the complex numbers. -/
theorem twoSinComplex (x : ℝ) :
    (2 * Real.sin x : ℂ) =
      (-Complex.I) * (Complex.exp (2 * ↑x * Complex.I) - 1) * Complex.exp (-(↑x * Complex.I)) := by
  rw [twoSinComplex2 x]
  have hA : Complex.exp (2 * ↑x * Complex.I) =
      Complex.exp (↑x * Complex.I) * Complex.exp (↑x * Complex.I) := by
    rw [show (2 : ℂ) * ↑x * Complex.I = ↑x * Complex.I + ↑x * Complex.I by ring,
      Complex.exp_add]
  rw [hA, Complex.exp_neg]
  have hne : Complex.exp (↑x * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- `∑_{t<N} (y + t π/N) = N y + π (N-1)/2`. -/
theorem sumTheta (N : ℕ) (hN : 1 ≤ N) (y : ℝ) :
    ∑ t ∈ Finset.range N, (y + t * Real.pi / N) =
      (N : ℝ) * y + Real.pi * ((N : ℝ) - 1) / 2 := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hsum : ∑ t ∈ Finset.range N, (↑t : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
    have h1 : (((∑ t ∈ Finset.range N, t) * 2 : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) := by
      rw [Finset.sum_range_id_mul_two, Nat.cast_mul, Nat.cast_sub hN]
      push_cast
      ring
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
    have h2 : (∑ t ∈ Finset.range N, (↑t : ℝ)) = ((∑ t ∈ Finset.range N, t : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    rw [h2, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← Nat.cast_mul]
    exact h1
  have hsplit : ∑ t ∈ Finset.range N, (↑t * Real.pi / (N : ℝ)) =
      (∑ t ∈ Finset.range N, (↑t : ℝ)) * (Real.pi / (N : ℝ)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsplit, hsum]
  field_simp

/-- The sine multiplication formula: `∏_{t<N} 2 sin(y + tπ/N) = 2 sin(Ny)`. -/
theorem prodTwoSin (N : ℕ) (hN : 1 ≤ N) (y : ℝ) :
    ∏ t ∈ Finset.range N, (2 * Real.sin (y + t * Real.pi / N)) = 2 * Real.sin (N * y) := by
  have hN0 : 0 < N := by omega
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNr
  have key : ∏ t ∈ Finset.range N, (2 * (Real.sin (y + t * Real.pi / N) : ℂ)) =
      (2 * Real.sin (N * y) : ℂ) := by
    set z : ℂ := Complex.exp (↑y * Complex.I) with hz
    set ω : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑N) with hωdef
    have hω : IsPrimitiveRoot ω N := by
      rw [hωdef]; exact Complex.isPrimitiveRoot_exp N (by omega)
    have hzw : ∀ t : ℕ,
        Complex.exp (2 * ↑(y + t * Real.pi / N) * Complex.I) = z ^ 2 * ω ^ t := by
      intro t
      rw [hz, hωdef]
      rw [show Complex.exp (↑y * Complex.I) ^ 2 = Complex.exp (2 * ↑y * Complex.I) by
        rw [pow_two, ← Complex.exp_add]; congr 1; ring]
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
    have hprod1 : ∏ t ∈ Finset.range N, (2 * (Real.sin (y + t * Real.pi / N) : ℂ)) =
        ∏ t ∈ Finset.range N, ((-Complex.I) * (z ^ 2 * ω ^ t - 1) *
          Complex.exp (-(↑(y + t * Real.pi / N) * Complex.I))) := by
      refine Finset.prod_congr rfl (fun t _ => ?_)
      rw [twoSinComplex (y + t * Real.pi / N), hzw t]
    rw [hprod1]
    have hpb : ∏ t ∈ Finset.range N, (z ^ 2 * ω ^ t - 1) =
        (-1 : ℂ) ^ N * (1 - (z ^ 2) ^ N) := by
      have h := prodOneSubPow N hN0 (z ^ 2) ω hω
      trans ∏ t ∈ Finset.range N, ((-1 : ℂ) * (1 - z ^ 2 * ω ^ t))
      · exact Finset.prod_congr rfl (fun t _ => by ring)
      · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, h]
    have hpe : ∏ t ∈ Finset.range N, Complex.exp (-(↑(y + t * Real.pi / N) * Complex.I)) =
        Complex.exp (-(↑(∑ t ∈ Finset.range N, (y + t * Real.pi / N)) * Complex.I)) := by
      rw [← Complex.exp_sum]
      congr 1
      rw [Complex.ofReal_sum, Finset.sum_mul, Finset.sum_neg_distrib]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      hpb, hpe, sumTheta N hN y]
    -- final phase bookkeeping
    have hI : (-Complex.I) ^ N * (-1 : ℂ) ^ N = Complex.I ^ N := by
      rw [show (-Complex.I : ℂ) = -1 * Complex.I by ring, mul_pow]
      rw [show (-1 : ℂ) ^ N * Complex.I ^ N * (-1 : ℂ) ^ N =
          Complex.I ^ N * ((-1 : ℂ) ^ N) ^ 2 by ring]
      rw [show ((-1 : ℂ) ^ N) ^ 2 = 1 by
        rw [sq, ← pow_add, show N + N = 2 * N by ring, pow_mul]; norm_num, mul_one]
    rw [← mul_assoc, hI]
    have hz2N : (z ^ 2) ^ N = Complex.exp (2 * ↑(N * y) * Complex.I) := by
      rw [← pow_mul, hz, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hz2N]
    have hIp : Complex.I ^ N = Complex.exp (↑N * (↑Real.pi / 2 * Complex.I)) := by
      conv_lhs => rw [← Complex.exp_pi_div_two_mul_I]
      rw [← Complex.exp_nat_mul]
    rw [hIp]
    rw [show Complex.exp (↑N * (↑Real.pi / 2 * Complex.I)) *
          (1 - Complex.exp (2 * ↑(N * y) * Complex.I)) *
          Complex.exp (-(↑((N : ℝ) * y + Real.pi * ((N : ℝ) - 1) / 2) * Complex.I)) =
        (Complex.exp (↑N * (↑Real.pi / 2 * Complex.I)) *
          Complex.exp (-(↑((N : ℝ) * y + Real.pi * ((N : ℝ) - 1) / 2) * Complex.I))) *
          (1 - Complex.exp (2 * ↑(N * y) * Complex.I)) from by ring]
    rw [← Complex.exp_add]
    have hAC : ↑N * (↑Real.pi / 2 * Complex.I) +
          (-(↑((N : ℝ) * y + Real.pi * ((N : ℝ) - 1) / 2) * Complex.I)) =
        ↑Real.pi / 2 * Complex.I + (-(↑(N * y) * Complex.I)) := by
      push_cast
      ring
    rw [hAC, Complex.exp_add, Complex.exp_pi_div_two_mul_I, twoSinComplex2 (N * y)]
    have hE : Complex.exp (-(↑(N * y) * Complex.I)) * Complex.exp (2 * ↑(N * y) * Complex.I) =
        Complex.exp (↑(N * y) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [show Complex.I * Complex.exp (-(↑(N * y) * Complex.I)) *
          (1 - Complex.exp (2 * ↑(N * y) * Complex.I)) =
        Complex.I * Complex.exp (-(↑(N * y) * Complex.I)) -
          Complex.I * (Complex.exp (-(↑(N * y) * Complex.I)) *
            Complex.exp (2 * ↑(N * y) * Complex.I)) by ring]
    rw [hE]
    ring
  apply Complex.ofReal_inj.mp
  simp only [Complex.ofReal_prod, Complex.ofReal_mul, Complex.ofReal_ofNat]
  exact key

/-- The `t`-th factor of the quarter-angle cosine product is a shifted sine. -/
theorem cosQuarterEqSin (N t : ℕ) (hN : 1 ≤ N) :
    Real.cos (Real.pi * (4 * t + 1) / (4 * N))
      = Real.sin (Real.pi / 2 + Real.pi / (4 * N) + t * Real.pi / N) := by
  rw [← Real.sin_add_pi_div_two]
  congr 1
  have hNr : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `sin²(N (π/2 + π/(4N))) = 1/2`. -/
theorem sinSqShiftQuarter (N : ℕ) (hN : 1 ≤ N) :
    Real.sin ((N : ℝ) * (Real.pi / 2 + Real.pi / (4 * N))) ^ 2 = 1 / 2 := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hNy : (N : ℝ) * (Real.pi / 2 + Real.pi / (4 * N)) =
      (N : ℝ) * Real.pi / 2 + Real.pi / 4 := by
    field_simp
  rw [hNy]
  have hcos : Real.cos ((N : ℝ) * Real.pi + Real.pi / 2) = 0 := by
    rw [Real.cos_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  have key : 2 * Real.sin ((N : ℝ) * Real.pi / 2 + Real.pi / 4) ^ 2 =
      1 - Real.cos (2 * ((N : ℝ) * Real.pi / 2 + Real.pi / 4)) := by
    have h := Real.cos_two_mul ((N : ℝ) * Real.pi / 2 + Real.pi / 4)
    have hs := Real.sin_sq_add_cos_sq ((N : ℝ) * Real.pi / 2 + Real.pi / 4)
    nlinarith [h, hs]
  have h2 : 2 * ((N : ℝ) * Real.pi / 2 + Real.pi / 4) =
      (N : ℝ) * Real.pi + Real.pi / 2 := by ring
  rw [h2, hcos] at key
  linarith

theorem cosProdQuarterSq (N : ℕ) (hN : 1 ≤ N) :
    (∏ t ∈ Finset.range N, Real.cos (Real.pi * (4 * t + 1) / (4 * N))) ^ 2 = 2 / (4 : ℝ) ^ N := by
  have hstep : ∏ t ∈ Finset.range N, (2 * Real.cos (Real.pi * (4 * t + 1) / (4 * N))) =
      ∏ t ∈ Finset.range N,
        (2 * Real.sin (Real.pi / 2 + Real.pi / (4 * N) + t * Real.pi / N)) :=
    Finset.prod_congr rfl (fun t _ => by rw [cosQuarterEqSin N t hN])
  have hPS : ∏ t ∈ Finset.range N, (2 * Real.cos (Real.pi * (4 * t + 1) / (4 * N))) =
      2 * Real.sin ((N : ℝ) * (Real.pi / 2 + Real.pi / (4 * N))) := by
    rw [hstep]
    exact prodTwoSin N hN _
  have hsplit : ∏ t ∈ Finset.range N, (2 * Real.cos (Real.pi * (4 * t + 1) / (4 * N))) =
      (2 : ℝ) ^ N * ∏ t ∈ Finset.range N, Real.cos (Real.pi * (4 * t + 1) / (4 * N)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hP : ∏ t ∈ Finset.range N, Real.cos (Real.pi * (4 * t + 1) / (4 * N)) =
      (2 * Real.sin ((N : ℝ) * (Real.pi / 2 + Real.pi / (4 * N)))) / 2 ^ N := by
    have h2N : ((2 : ℝ) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [eq_div_iff h2N, mul_comm, ← hsplit]
    exact hPS
  rw [hP, div_pow]
  have hnum : (2 * Real.sin ((N : ℝ) * (Real.pi / 2 + Real.pi / (4 * N)))) ^ 2 = 2 := by
    rw [mul_pow, sinSqShiftQuarter N hN]
    norm_num
  have hden : (((2 : ℝ) ^ N)) ^ 2 = (4 : ℝ) ^ N := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  rw [hnum, hden]

end Work.TMC14Core
