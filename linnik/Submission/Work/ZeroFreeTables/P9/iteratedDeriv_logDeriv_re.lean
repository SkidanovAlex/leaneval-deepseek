/-
# ZeroFreeTables/P9/iteratedDeriv_logDeriv_re

The real part of the `j`-th derivative of the logarithmic derivative of a Dirichlet
`L`-function, in terms of the logarithmic moments of the twisted von Mangoldt series:

`Re ((L'/L)^{(j)}(s)) = (-1)^{j+1} · Σ_n Λ(n) Re(χ(n) n^{-s}) (log n)^j`,  `Re s > 1`.

## Proof

Write `f = ↗χ * ↗Λ` for the coefficient sequence `n ↦ χ(n) Λ(n)`.  The Euler-product identity
`L(↗χ) = -deriv(L ↗χ) / L ↗χ` (`DirichletCharacter.LSeries_twist_vonMangoldt_eq`) together with
`LFunction χ = LSeries ↗χ`, `deriv (LFunction χ) = deriv (LSeries ↗χ)` on `Re s > 1` gives the
pointwise identity

`logDeriv (LFunction χ) z = - LSeries f z`   (`1 < z.re`).

Since the two sides agree on an open neighbourhood of `s`, their `j`-th derivatives agree, and
term-by-term differentiation of the Dirichlet series (`LSeries_iteratedDeriv`, whose abscissa
hypothesis holds because `abscissaOfAbsConv f ≤ 1`) gives

`(logDeriv (LFunction χ))^{(j)}(s) = -(-1)^j · LSeries (logMul^[j] f) s`.

Finally `logMul^[j] f` is the coefficient sequence `n ↦ (log n)^j · χ(n) Λ(n)`, so its `L`-series
is absolutely convergent at `s` (again because the abscissa is `≤ 1`) and taking real parts of
the `n`-th summand gives `Λ(n) (log n)^j Re(χ(n) n^{-s})`; hence the real part of the `L`-series
is exactly `vonMangoldtMoment χ s j`.  Multiplying by `-(-1)^j = (-1)^{j+1}` finishes the proof.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.SigmaP3LCoeffs

namespace Work.ZeroFreeTables.P9

open ArithmeticFunction DirichletCharacter Filter
open scoped LSeries.notation Topology

/-- The abscissa of absolute convergence of the twisted von Mangoldt series `Σ_n χ(n)Λ(n) n^{-z}`
is `≤ 1`. -/
private lemma abscissa_chi_mul_vonMangoldt_le_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    LSeries.abscissaOfAbsConv (↗χ * ↗Λ) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := (y : ℂ)) (by simpa using hy)

/-- On `Re s > 1` the logarithmic derivative of `L(·,χ)` is minus the Dirichlet series of `Λ·χ`. -/
private lemma logDeriv_LFunction_eq_neg_LSeries {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction χ) s = - LSeries (↗χ * ↗Λ) s := by
  have htw := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have hd := DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs
  have hL := DirichletCharacter.LFunction_eq_LSeries χ hs
  rw [logDeriv_apply, hd, hL, htw]
  ring

/-- The `m`-fold iterate of `LSeries.logMul` multiplies the `n`-th coefficient by `(log n)^m`. -/
private lemma logMul_iterate_apply' (f : ℕ → ℂ) (m : ℕ) :
    ∀ n, (LSeries.logMul^[m] f) n = (Complex.log (n : ℂ)) ^ m * f n := by
  intro n
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    show Complex.log ((n : ℕ) : ℂ) * (LSeries.logMul^[m] f) n
      = (Complex.log ((n : ℕ) : ℂ)) ^ (m + 1) * f n
    rw [ih]; ring

/-- Real part of the product of a (real) power of `-1` with a complex number. -/
private lemma neg_one_pow_mul_re (j : ℕ) (z : ℂ) :
    ((-1 : ℂ) ^ j * z).re = (-1 : ℝ) ^ j * z.re := by
  have hbase : (-1 : ℂ) = ((-1 : ℝ) : ℂ) := by norm_num
  have hpow : (-1 : ℂ) ^ j = (((-1 : ℝ) ^ j : ℝ) : ℂ) := by
    rw [hbase, Complex.ofReal_pow]
  rw [hpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The real part of the `L`-series of `log^j · (χ·Λ)` is the `j`-th von Mangoldt moment. -/
private lemma LSeries_logMul_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (LSeries (LSeries.logMul^[j] (↗χ * ↗Λ)) s).re = vonMangoldtMoment χ s j := by
  have hf0 : (↗χ * ↗Λ) 0 = 0 := by
    simp only [Pi.mul_apply, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero,
      Nat.cast_zero, Complex.ofReal_zero, mul_zero]
  have hf0' : (LSeries.logMul^[j] (↗χ * ↗Λ)) 0 = 0 := by
    rw [logMul_iterate_apply']; simp [hf0]
  have hs' : LSeries.abscissaOfAbsConv (LSeries.logMul^[j] (↗χ * ↗Λ)) < (s.re : EReal) := by
    rw [LSeries.absicssaOfAbsConv_logPowMul]
    exact lt_of_le_of_lt (abscissa_chi_mul_vonMangoldt_le_one χ) (EReal.coe_lt_coe_iff.mpr hs)
  have hsumm : LSeriesSummable (LSeries.logMul^[j] (↗χ * ↗Λ)) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re hs'
  rw [LSeries.eq_1, Complex.re_tsum hsumm]
  refine tsum_congr fun n => ?_
  have hlog : (Complex.log ((n : ℕ) : ℂ)) ^ j = (((Real.log n) ^ j : ℝ) : ℂ) := by
    have h1 : Complex.log ((n : ℕ) : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.natCast_log]
    rw [h1, Complex.ofReal_pow]
  rw [LSeries.term_def₀ hf0' s n, logMul_iterate_apply']
  simp only [Pi.mul_apply, chiTwistRe, hlog, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, zero_mul, mul_zero, sub_zero, add_zero]
  ring

theorem iteratedDeriv_logDeriv_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (j : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    (iteratedDeriv j (logDeriv (DirichletCharacter.LFunction χ)) s).re
      = (-1) ^ (j + 1) * vonMangoldtMoment χ s j := by
  have heq : logDeriv (DirichletCharacter.LFunction χ) =ᶠ[𝓝 s]
      fun z => - LSeries (↗χ * ↗Λ) z := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨{z : ℂ | 1 < z.re}, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs,
      fun z hz => logDeriv_LFunction_eq_neg_LSeries χ hz⟩
  have habs : LSeries.abscissaOfAbsConv (↗χ * ↗Λ) < (s.re : EReal) :=
    lt_of_le_of_lt (abscissa_chi_mul_vonMangoldt_le_one χ) (EReal.coe_lt_coe_iff.mpr hs)
  calc (iteratedDeriv j (logDeriv (DirichletCharacter.LFunction χ)) s).re
      = (iteratedDeriv j (fun z => - LSeries (↗χ * ↗Λ) z) s).re := by
          rw [heq.iteratedDeriv_eq]
    _ = (- iteratedDeriv j (LSeries (↗χ * ↗Λ)) s).re := by
          rw [iteratedDeriv_fun_neg]
    _ = (- ((-1 : ℂ) ^ j * LSeries (LSeries.logMul^[j] (↗χ * ↗Λ)) s)).re := by
          rw [LSeries_iteratedDeriv j habs]
    _ = - ((-1 : ℂ) ^ j * LSeries (LSeries.logMul^[j] (↗χ * ↗Λ)) s).re := by
          rw [Complex.neg_re]
    _ = - ((-1 : ℝ) ^ j * (LSeries (LSeries.logMul^[j] (↗χ * ↗Λ)) s).re) := by
          rw [neg_one_pow_mul_re]
    _ = - ((-1 : ℝ) ^ j * vonMangoldtMoment χ s j) := by
          rw [LSeries_logMul_re χ j hs]
    _ = (-1) ^ (j + 1) * vonMangoldtMoment χ s j := by
          rw [pow_succ]; ring

end Work.ZeroFreeTables.P9
