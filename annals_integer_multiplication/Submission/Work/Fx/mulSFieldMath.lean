import Mathlib
import Submission.Work.Fx.FxCommon

namespace Work.Fx

open HvdH

/-! ## Arithmetic helpers for the round-to-zero product of two disc points

`inDisc p z` is `z.1 ^ 2 + z.2 ^ 2 ≤ 4 ^ p`, i.e. the fixed point `fxC p z = 2^{-p} (x + iy)` has
modulus `≤ 1`.  The three lemmas below are the arithmetic content of the error analysis:

* `tdivSqMulLe` : truncation toward zero never increases the square (`|a.tdiv N| ≤ |a|/N`);
* `absTmodLe`   : the truncation remainder satisfies `|a.tmod N| ≤ N - 1` for `0 < N`;
* `cfxSubMul`   : the algebraic identity for the difference between the rounded product and the
  exact product, whose numerator is `N Re uv - Re uv + i (N Im uv - Im uv)`. -/

/-- Truncating division by `N` never increases the square: `(a.tdiv N)^2 * N^2 ≤ a^2`. -/
theorem tdivSqMulLe (a N : ℤ) : (a.tdiv N)^2 * N^2 ≤ a^2 := by
  have h1 : ((a.tdiv N) * N).natAbs ≤ a.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_tdiv]
    exact Nat.div_mul_le_self _ _
  have h2 : (((a.tdiv N) * N).natAbs)^2 ≤ (a.natAbs)^2 := Nat.pow_le_pow_left h1 2
  have h3 : (((a.tdiv N) * N).natAbs : ℤ)^2 ≤ ((a.natAbs : ℤ))^2 := by exact_mod_cast h2
  rw [Int.natAbs_sq, Int.natAbs_sq] at h3
  have h4 : (a.tdiv N)^2 * N^2 = ((a.tdiv N) * N)^2 := by ring
  rw [h4]; exact h3

/-- The truncation remainder: `|a.tmod N| ≤ N - 1` for `0 < N`. -/
theorem absTmodLe (a N : ℤ) (hN : 0 < N) : |((a.tmod N : ℤ) : ℝ)| ≤ (N:ℝ) - 1 := by
  have h1 : a.tmod N ≤ N - 1 := by
    have := Int.tmod_lt_of_pos a hN; omega
  have h2 : -(N - 1) ≤ a.tmod N := by
    have := Int.lt_tmod_of_pos a hN; omega
  rw [abs_le]
  constructor <;> exact_mod_cast ‹_›

/-- The complex identity behind the error estimate: writing `a = x'x - y'y`, `b = y x' + y' x` and
`qa = a.tdiv N`, `qb = b.tdiv N`, the difference between the rounded product `(qa + i qb)/n` and
the exact product `((x + iy)/n) * ((x' + iy')/n)` has numerator `N qa - a + i (N qb - b)`. -/
theorem cfxSubMul {n q1 q2 x y x' y' : ℂ} (hn : n ≠ 0) :
    (q1 + q2*Complex.I)/n - ((x + y*Complex.I)/n) * ((x' + y'*Complex.I)/n)
      = ((n*q1 - (x'*x - y'*y) + (n*q2 - (y*x' + y'*x))*Complex.I) / n^2) := by
  field_simp
  ring_nf
  simp only [pow_two, Complex.I_mul_I]
  ring

theorem mulSFieldMath {p : ℕ} (x y x' y' : ℤ) (h1 : HvdH.inDisc p (x, y)) (h2 : HvdH.inDisc p (x', y')) :
    HvdH.inDisc p ((Int.tdiv (x' * x - y' * y) ((2 : ℤ) ^ p), Int.tdiv (y * x' + y' * x) ((2 : ℤ) ^ p))) ∧
    (2 : ℝ) ^ p * ‖HvdH.fxC p ((Int.tdiv (x' * x - y' * y) ((2 : ℤ) ^ p), Int.tdiv (y * x' + y' * x) ((2 : ℤ) ^ p)))
      - HvdH.fxC p (x, y) * HvdH.fxC p (x', y')‖ < 2 := by
  set N : ℤ := (2:ℤ)^p with hN
  set a : ℤ := x' * x - y' * y with ha
  set b : ℤ := y * x' + y' * x with hb
  have hNpos : (0:ℤ) < N := by rw [hN]; positivity
  have hNposR : (0:ℝ) < (2:ℝ)^p := by positivity
  have hx2 : x^2 + y^2 ≤ 4^p := by
    have hh := h1; simp only [inDisc] at hh; simpa using hh
  have hx'2 : x'^2 + y'^2 ≤ 4^p := by
    have hh := h2; simp only [inDisc] at hh; simpa using hh
  have hid : a^2 + b^2 = (x^2 + y^2) * (x'^2 + y'^2) := by
    rw [ha, hb]; ring
  have hprod : (x^2 + y^2) * (x'^2 + y'^2) ≤ 4^p * 4^p :=
    mul_le_mul hx2 hx'2 (by positivity) (by positivity)
  have hN2 : N^2 = 4^p := by rw [hN, ← pow_mul, mul_comm p 2, pow_mul]; norm_num
  constructor
  · simp only [inDisc]
    have hqa := tdivSqMulLe a N
    have hqb := tdivSqMulLe b N
    have h4 : 4^p * 4^p = 4^(2*p) := by rw [← pow_add]; ring_nf
    have hM : N^2 * ((a.tdiv N)^2 + (b.tdiv N)^2) ≤ N^2 * 4^p := by
      nlinarith [hqa, hqb, hid, hprod, hN2, h4]
    exact le_of_mul_le_mul_left hM (by rw [hN2]; positivity)
  · set e1 : ℤ := N * (a.tdiv N) - a with he1def
    set e2 : ℤ := N * (b.tdiv N) - b with he2def
    have hNcastC : ((N:ℤ) : ℂ) = (2:ℂ)^p := by rw [hN]; push_cast; ring
    have hc2 : (2:ℂ)^p ≠ 0 := pow_ne_zero _ (by norm_num)
    have hrc1 : fxC p (a.tdiv N, b.tdiv N) - fxC p (x, y) * fxC p (x', y')
        = ((2:ℂ)^p * ((a.tdiv N : ℤ) : ℂ) - ((x':ℂ)*(x:ℂ) - (y':ℂ)*(y:ℂ))
           + ((2:ℂ)^p * ((b.tdiv N : ℤ) : ℂ) - ((y:ℂ)*(x':ℂ) + (y':ℂ)*(x:ℂ)))*Complex.I)
          / ((2:ℂ)^p)^2 := by
      simp only [fxC]
      exact cfxSubMul hc2
    have hrc : fxC p (a.tdiv N, b.tdiv N) - fxC p (x, y) * fxC p (x', y')
        = ((e1 : ℂ) + (e2 : ℂ) * Complex.I) / ((2:ℂ)^p)^2 := by
      rw [hrc1]
      congr 1
      rw [he1def, he2def, ha, hb]
      push_cast
      rw [hNcastC]
    have hnorm : ‖fxC p (a.tdiv N, b.tdiv N) - fxC p (x, y) * fxC p (x', y')‖
        = ‖(e1 : ℂ) + (e2 : ℂ) * Complex.I‖ / ((2:ℝ)^p)^2 := by
      rw [hrc, norm_div]
      have h2 : ‖((2:ℂ)^p)^2‖ = ((2:ℝ)^p)^2 := by rw [norm_pow, norm_pow]; norm_num
      rw [h2]
    have hE : ‖(e1 : ℂ) + (e2 : ℂ) * Complex.I‖ ≤ |(e1:ℝ)| + |(e2:ℝ)| := by
      have := Complex.norm_le_abs_re_add_abs_im ((e1 : ℂ) + (e2 : ℂ) * Complex.I)
      simpa [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] using this
    have he1b : |(e1:ℝ)| ≤ (N:ℝ) - 1 := by
      have hone : e1 = -(a.tmod N) := by
        rw [he1def, Int.tmod_def]; ring
      simpa [hone] using absTmodLe a N hNpos
    have he2b : |(e2:ℝ)| ≤ (N:ℝ) - 1 := by
      have hone : e2 = -(b.tmod N) := by
        rw [he2def, Int.tmod_def]; ring
      simpa [hone] using absTmodLe b N hNpos
    have he12 : |(e1:ℝ)| + |(e2:ℝ)| < 2 * (2:ℝ)^p := by
      have hNcastR : ((N:ℤ) : ℝ) = (2:ℝ)^p := by rw [hN]; push_cast; ring
      linarith [he1b, he2b, hNcastR]
    have hmain : (2:ℝ)^p * ‖fxC p (a.tdiv N, b.tdiv N) - fxC p (x, y) * fxC p (x', y')‖
        ≤ (|(e1:ℝ)| + |(e2:ℝ)|) / (2:ℝ)^p := by
      rw [hnorm]
      have h2 : (2:ℝ)^p * (‖(e1 : ℂ) + (e2 : ℂ) * Complex.I‖ / ((2:ℝ)^p)^2)
          = ‖(e1 : ℂ) + (e2 : ℂ) * Complex.I‖ / (2:ℝ)^p := by
        field_simp
      rw [h2]
      exact div_le_div_of_nonneg_right hE (le_of_lt hNposR)
    have hstrict : (|(e1:ℝ)| + |(e2:ℝ)|) / (2:ℝ)^p < 2 := by
      have h := div_lt_div_of_pos_right he12 hNposR
      rwa [mul_div_assoc, div_self (ne_of_gt hNposR), mul_one] at h
    linarith


end Work.Fx
