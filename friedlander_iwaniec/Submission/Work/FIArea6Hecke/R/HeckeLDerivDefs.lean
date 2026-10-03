/-
# `Submission.Work.FIArea6Hecke.R.HeckeLDerivDefs`

Elementary local input for the `(3,4,1)` derivative inequality for the Hecke `L`-function of
`ℚ(i)` (`Work.FIArea6Hecke.R.HeckeLDerivRe341`).

The analytic content of the target is the classical trigonometric inequality
`3 + 4 cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`, applied *term by term* to the logarithmic derivatives
of the local Euler factors.  The lemmas here package that inequality in the form in which the
assembly uses it:

* `three_four_one_aux` — `3 + 4 Re u + Re (u²) ≥ 0` for `‖u‖ ≤ 1` (the `u = z^k` of the local
  factor, `z` a Satake parameter of modulus `≤ 1`);
* `local341` / `local341_nonneg` — the same inequality summed against the geometric series
  `Σ_j w^j`, `0 ≤ w < 1`: the value of `3·w/(1-w) + 4 Re(Zw/(1-Zw)) + Re(Z²w/(1-Z²w))` is
  `Σ_j w^j·(3 + 4 Re(Z^j) + Re(Z^{2j})) ≥ 0`.
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- The elementary trigonometric inequality: `3 + 4 Re u + Re (u²) ≥ 0` for `‖u‖ ≤ 1`.

Writing `u = a + bi` this is `2(a+1)² + (1 - a² - b²) ≥ 0`, using `a² + b² = ‖u‖² ≤ 1`. -/
lemma three_four_one_aux {u : ℂ} (hu : ‖u‖ ≤ 1) : 0 ≤ 3 + 4 * u.re + (u ^ 2).re := by
  have h2 : (u ^ 2).re = u.re ^ 2 - u.im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have hnorm : u.re ^ 2 + u.im ^ 2 ≤ 1 := by
    have h := Complex.sq_norm u
    rw [Complex.normSq_apply] at h
    nlinarith [hu, norm_nonneg u]
  rw [h2]
  nlinarith [sq_nonneg (u.re + 1)]

/-- For `a : ℂ`, `‖a‖ < 1`: `a/(1-a) = Σ_j a^{j+1}`. -/
lemma div_one_sub_eq_tsum_pow_succ {a : ℂ} (ha : ‖a‖ < 1) :
    a / (1 - a) = ∑' j : ℕ, a ^ (j + 1) := by
  have h1 : HasSum (fun j : ℕ => a ^ j) ((1 - a)⁻¹) := hasSum_geometric_of_norm_lt_one ha
  rw [div_eq_mul_inv, ← h1.tsum_eq, ← tsum_mul_left]
  exact tsum_congr (fun j => by rw [pow_succ]; ring)

/-- For `w : ℝ`, `‖w‖ < 1`: `w/(1-w) = Σ_j w^{j+1}`. -/
lemma real_div_one_sub_eq_tsum_pow_succ {w : ℝ} (hw : ‖w‖ < 1) :
    w / (1 - w) = ∑' j : ℕ, w ^ (j + 1) := by
  have h1 : HasSum (fun j : ℕ => w ^ j) ((1 - w)⁻¹) := hasSum_geometric_of_norm_lt_one hw
  rw [div_eq_mul_inv, ← h1.tsum_eq, ← tsum_mul_left]
  exact tsum_congr (fun j => by rw [pow_succ]; ring)

/-- The local `(3,4,1)` sum `3·w/(1-w) + 4 Re(Zw/(1-Zw)) + Re(Z²w/(1-Z²w))`, `0 ≤ w < 1`,
`‖Z‖ ≤ 1`.  Its expansion is `Σ_j w^j·(3 + 4 Re(Z^j) + Re(Z^{2j}))`. -/
def local341 (w : ℝ) (Z : ℂ) : ℝ :=
  3 * (w / (1 - w)) + 4 * ((Z * (w : ℂ)) / (1 - Z * (w : ℂ))).re
    + ((Z ^ 2 * (w : ℂ)) / (1 - Z ^ 2 * (w : ℂ))).re

/-- **The local `(3,4,1)` nonnegativity.**  For `0 ≤ w < 1` and `‖Z‖ ≤ 1`,
`3·w/(1-w) + 4 Re(Zw/(1-Zw)) + Re(Z²w/(1-Z²w)) ≥ 0`. -/
lemma local341_nonneg {w : ℝ} {Z : ℂ} (hw0 : 0 ≤ w) (hw1 : w < 1) (hZ : ‖Z‖ ≤ 1) :
    0 ≤ local341 w Z := by
  have hwabs : ‖w‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hw0]; exact hw1
  have hPnorm : ‖Z * (w : ℂ)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    nlinarith [hZ, norm_nonneg Z, hw0, hw1]
  have hQnorm : ‖Z ^ 2 * (w : ℂ)‖ < 1 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    have h2 : ‖Z‖ ^ 2 ≤ 1 := by nlinarith [hZ, norm_nonneg Z]
    nlinarith [h2, hw0, hw1]
  have e1 : w / (1 - w) = ∑' j : ℕ, w ^ (j + 1) := real_div_one_sub_eq_tsum_pow_succ hwabs
  have e2 : (Z * (w : ℂ)) / (1 - Z * (w : ℂ)) = ∑' j : ℕ, (Z * (w : ℂ)) ^ (j + 1) :=
    div_one_sub_eq_tsum_pow_succ hPnorm
  have e3 : (Z ^ 2 * (w : ℂ)) / (1 - Z ^ 2 * (w : ℂ)) = ∑' j : ℕ, (Z ^ 2 * (w : ℂ)) ^ (j + 1) :=
    div_one_sub_eq_tsum_pow_succ hQnorm
  have hs1 : Summable (fun j : ℕ => w ^ (j + 1)) :=
    (summable_geometric_of_norm_lt_one hwabs).comp_injective Nat.succ_injective
  have hs2 : Summable (fun j : ℕ => (Z * (w : ℂ)) ^ (j + 1)) :=
    (summable_geometric_of_norm_lt_one hPnorm).comp_injective Nat.succ_injective
  have hs3 : Summable (fun j : ℕ => (Z ^ 2 * (w : ℂ)) ^ (j + 1)) :=
    (summable_geometric_of_norm_lt_one hQnorm).comp_injective Nat.succ_injective
  have hs2r : Summable (fun j : ℕ => ((Z * (w : ℂ)) ^ (j + 1)).re) := by
    simpa [Function.comp_def, Complex.reCLM_apply] using Complex.reCLM.summable hs2
  have hs3r : Summable (fun j : ℕ => ((Z ^ 2 * (w : ℂ)) ^ (j + 1)).re) := by
    simpa [Function.comp_def, Complex.reCLM_apply] using Complex.reCLM.summable hs3
  rw [local341, e1, e2, e3, Complex.re_tsum hs2, Complex.re_tsum hs3]
  rw [← tsum_mul_left, ← tsum_mul_left]
  rw [← (hs1.mul_left 3).tsum_add (hs2r.mul_left 4)]
  rw [← ((hs1.mul_left 3).add (hs2r.mul_left 4)).tsum_add hs3r]
  refine tsum_nonneg (fun j => ?_)
  have hwj : (0 : ℝ) ≤ w ^ (j + 1) := pow_nonneg hw0 _
  have hZr : ‖Z ^ (j + 1)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg Z) hZ
  have hkey := three_four_one_aux hZr
  have hre1 : ((Z * (w : ℂ)) ^ (j + 1)).re = (Z ^ (j + 1)).re * w ^ (j + 1) := by
    have h1 : (Z * (w : ℂ)) ^ (j + 1) = Z ^ (j + 1) * ((w ^ (j + 1) : ℝ) : ℂ) := by
      rw [mul_pow, ← Complex.ofReal_pow]
    rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hre2 : ((Z ^ 2 * (w : ℂ)) ^ (j + 1)).re = ((Z ^ (j + 1)) ^ 2).re * w ^ (j + 1) := by
    have h1 : (Z ^ 2 * (w : ℂ)) ^ (j + 1)
        = (Z ^ (j + 1)) ^ 2 * ((w ^ (j + 1) : ℝ) : ℂ) := by
      rw [mul_pow, ← Complex.ofReal_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 2 (j + 1)]
    rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre1, hre2]
  have : 3 * w ^ (j + 1) + 4 * ((Z ^ (j + 1)).re * w ^ (j + 1))
      + ((Z ^ (j + 1)) ^ 2).re * w ^ (j + 1)
      = w ^ (j + 1) * (3 + 4 * (Z ^ (j + 1)).re + ((Z ^ (j + 1)) ^ 2).re) := by ring
  rw [this]
  exact mul_nonneg hwj hkey

/-! ## Calculus helpers for the local model functions `z ↦ (p:ℂ)^{-z}` -/

/-- The derivative of `z ↦ (p : ℂ)^{-z}`. -/
lemma hasDerivAt_natCast_cpow_neg (p : Nat.Primes) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (((p:ℕ):ℂ) ^ (-w)))
      (-(((Real.log ((p:ℕ):ℝ)) : ℂ) * (((p:ℕ):ℂ) ^ (-z)))) z := by
  have hc : (((p:ℕ):ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact p.prop.pos.ne'
  have hlog : Complex.log (((p:ℕ):ℂ)) = ((Real.log ((p:ℕ):ℝ) : ℂ)) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg _)]
  have h := (hasDerivAt_neg z).const_cpow (Or.inl hc)
  rw [hlog] at h
  convert h using 1
  ring

/-- The norm of `(p : ℂ)^{-z}`. -/
lemma norm_cpow_neg_nat (p : Nat.Primes) (z : ℂ) :
    ‖(((p:ℕ):ℂ) ^ (-z))‖ = ((p:ℕ):ℝ) ^ (-z.re) :=
  (Complex.norm_natCast_cpow_of_pos p.prop.pos (-z)).trans (by rw [Complex.neg_re])

/-- `‖(p:ℂ)^{-it}‖ = 1` for real `t`. -/
lemma norm_cpow_neg_I (p : Nat.Primes) (t : ℝ) :
    ‖(((p:ℕ):ℂ) ^ (-((t:ℂ) * Complex.I)))‖ = 1 := by
  rw [norm_cpow_neg_nat]
  have h0 : -((t:ℂ) * Complex.I).re = 0 := by simp
  rw [h0, Real.rpow_zero]

/-- `Re(w/(1-w)) = w/(1-w)` for real `w`. -/
lemma re_ratio (w : ℝ) : (((w:ℂ) / (1 - (w:ℂ))).re) = w/(1-w) := by
  rw [show (1:ℂ) - (w:ℂ) = ((1-w:ℝ):ℂ) by push_cast; ring, ← Complex.ofReal_div,
    Complex.ofReal_re]

end

end Work.FIArea6Hecke.R
