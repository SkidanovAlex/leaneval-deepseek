import Mathlib.NumberTheory.LSeries.Dirichlet
import Submission.Commons.NumberTheory.Zeta.logDeriv_sub_pole_analyticAt

noncomputable section

open Complex LSeries ArithmeticFunction
open scoped BigOperators

namespace Commons.NumberTheory.Zeta

/-!
# The real part of `−ζ′(s)/ζ(s)` as a von-Mangoldt cosine series

For `s = σ + i·t` with `σ > 1`,

`Re(−ζ′(s)/ζ(s)) = ∑_{n ≥ 0} Λ(n+1)·cos(t·log(n+1)) / (n+1)^σ`.

This is the real-part identity for the Dirichlet series of the von Mangoldt
function `Λ`, i.e. for the negative logarithmic derivative of `ζ` in the
half-plane of absolute convergence `Re s > 1`.  The analytic input is the
Mathlib identity
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`; everything
below is summation theory (commuting the real part with the absolutely
convergent series, shifting the index by one and computing the real part of
each term).
-/

/-- For real `x, y`, `Re exp(x + i·y) = e^x·cos y`. -/
private lemma re_exp_add_ofReal_mul_I (x y : ℝ) :
    (Complex.exp ((x : ℂ) + (y : ℂ) * Complex.I)).re = Real.exp x * Real.cos y := by
  have hx_re : (Complex.exp (x : ℂ)).re = Real.exp x := by
    rw [← Complex.ofReal_exp, Complex.ofReal_re]
  have hx_im : (Complex.exp (x : ℂ)).im = 0 := by
    rw [← Complex.ofReal_exp, Complex.ofReal_im]
  have hc_re : (Complex.cos (y : ℂ)).re = Real.cos y := by
    rw [← Complex.ofReal_cos, Complex.ofReal_re]
  have hc_im : (Complex.cos (y : ℂ)).im = 0 := by
    rw [← Complex.ofReal_cos, Complex.ofReal_im]
  have hs_re : (Complex.sin (y : ℂ)).re = Real.sin y := by
    rw [← Complex.ofReal_sin, Complex.ofReal_re]
  have hs_im : (Complex.sin (y : ℂ)).im = 0 := by
    rw [← Complex.ofReal_sin, Complex.ofReal_im]
  calc
    (Complex.exp ((x : ℂ) + (y : ℂ) * Complex.I)).re
        = (Complex.exp (x : ℂ) * (Complex.cos (y : ℂ) + Complex.sin (y : ℂ) * Complex.I)).re := by
          rw [Complex.exp_add, Complex.exp_mul_I]
    _ = (Complex.exp (x : ℂ)).re * (Complex.cos (y : ℂ) + Complex.sin (y : ℂ) * Complex.I).re
        - (Complex.exp (x : ℂ)).im * (Complex.cos (y : ℂ) + Complex.sin (y : ℂ) * Complex.I).im := by
          rw [Complex.mul_re]
    _ = Real.exp x * Real.cos y := by
      have hB_re : (Complex.cos (y : ℂ) + Complex.sin (y : ℂ) * Complex.I).re = Real.cos y := by
        simp [Complex.add_re, Complex.mul_re, hc_re, hs_re, hs_im]
      have hB_im : (Complex.cos (y : ℂ) + Complex.sin (y : ℂ) * Complex.I).im = Real.sin y := by
        simp [Complex.add_im, Complex.mul_im, hc_im, hs_re, hs_im]
      rw [hx_re, hx_im, hB_re, hB_im]
      ring

/-- For `0 < x` and `s = σ + i·t`: `Re ((x^s)⁻¹) = cos(t·log x) / x^σ`. -/
private lemma re_inv_cpow (x : ℝ) (hx : 0 < x) (σ : ℝ) (t : ℝ) :
    ((((x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I)))⁻¹).re) =
      Real.cos (t * Real.log x) / x ^ σ := by
  have hx0c : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  have hcw : (x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I)) =
      Complex.exp (((Real.log x : ℂ)) * (((σ : ℂ) + (t : ℂ) * Complex.I))) := by
    rw [Complex.cpow_def_of_ne_zero hx0c]
    congr 1
    rw [← Complex.ofReal_log (le_of_lt hx)]
  have hinv : (((x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I)))⁻¹) =
      Complex.exp (-(((Real.log x : ℂ)) * (((σ : ℂ) + (t : ℂ) * Complex.I)))) := by
    rw [hcw, ← Complex.exp_neg]
  have hdec : -((Real.log x : ℂ) * (((σ : ℂ) + (t : ℂ) * Complex.I))) =
      ((-(σ * Real.log x) : ℝ) : ℂ) + ((-(t * Real.log x) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  have h_exp : Real.exp (-(σ * Real.log x)) = (x ^ σ)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    rw [Real.rpow_def_of_pos hx σ]
    congr 1
    ring
  calc
    (((x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I)))⁻¹).re
        = (Complex.exp (-((Real.log x : ℂ) * (((σ : ℂ) + (t : ℂ) * Complex.I))))).re := by
            rw [hinv]
    _ = (Complex.exp (((-(σ * Real.log x) : ℝ) : ℂ) + ((-(t * Real.log x) : ℝ) : ℂ) * Complex.I)).re := by
            rw [hdec]
    _ = Real.exp (-(σ * Real.log x)) * Real.cos (-(t * Real.log x)) := by
            exact re_exp_add_ofReal_mul_I (-(σ * Real.log x)) (-(t * Real.log x))
    _ = (x ^ σ)⁻¹ * Real.cos (t * Real.log x) := by
            rw [h_exp, Real.cos_neg]
    _ = Real.cos (t * Real.log x) / x ^ σ := by
            rw [div_eq_mul_inv, mul_comm]

/-- Real part of the `(n+1)`-st term of the complex von-Mangoldt Dirichlet
series at `s = σ + i·t`. -/
private lemma mangoldt_term_re (n : ℕ) (σ : ℝ) (t : ℝ) :
    ((((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) /
      (((n + 1 : ℕ) : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I)))).re) =
      ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
        Real.cos (t * Real.log (((n + 1 : ℕ) : ℝ)))) /
        (((n + 1 : ℕ) : ℝ) ^ σ) := by
  let M : ℝ := ArithmeticFunction.vonMangoldt (n + 1)
  let x : ℝ := (n + 1 : ℕ)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  calc
    ((((M : ℝ) : ℂ) / ((x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I)))).re)
        = (((M : ℝ) : ℂ) * (((x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I)))⁻¹)).re := by
            rw [div_eq_mul_inv]
    _ = M * ((((x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I)))⁻¹).re) := by
            simp [Complex.mul_re]
    _ = M * (Real.cos (t * Real.log x) / x ^ σ) := by
            rw [re_inv_cpow x hx σ t]
    _ = (M * Real.cos (t * Real.log x)) / x ^ σ := by
            rw [mul_div_assoc]
    _ = ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
          Real.cos (t * Real.log (((n + 1 : ℕ) : ℝ)))) / (((n + 1 : ℕ) : ℝ) ^ σ) := by
            rfl

/-- The real part of the negative logarithmic derivative of `ζ` at
`σ + i·t` (`σ > 1`) equals the von-Mangoldt cosine series
`∑_{n ≥ 0} Λ(n+1) cos(t·log(n+1)) / (n+1)^σ`. -/
theorem mangoldt_series_re (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
      riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re =
      ∑' n : ℕ, (((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
        Real.cos (t * Real.log (((n + 1 : ℕ) : ℝ)))) /
          ((((n + 1 : ℕ) : ℝ) ^ σ))) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hS
  have hs1 : (1 : ℝ) < s.re := by
    rw [hS]
    simpa using hσ
  have hΛ0 : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs with h
    · exfalso
      exact not_isPrimePow_zero h
    · rfl
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  have hf0 : f 0 = 0 := by
    dsimp [f]
    exact_mod_cast hΛ0
  let a : ℕ → ℂ := fun n => f n / ((n : ℂ) ^ s)
  have ha0 : a 0 = 0 := by
    dsimp [a, f]
    rw [hΛ0]
    simp
  have hL : LSeries f s = (-deriv riemannZeta s / riemannZeta s) := by
    simpa [f] using
      (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs1)
  have hLSumm : Summable (LSeries.term f s) := by
    change Summable (LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s)
    simpa [LSeriesSummable] using
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs1)
  have hSummA : Summable a := by
    apply hLSumm.congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [a, hf0]
    · dsimp [a, f]
      rw [LSeries.term, if_neg hn]
  have htail : (∑' n : ℕ, a (n + 1)) = ∑' n : ℕ, a n := by
    have hsumadd := hSummA.sum_add_tsum_nat_add 1
    simpa [ha0] using hsumadd
  have hSummA' : Summable (fun n : ℕ => a (n + 1)) := by
    exact (summable_nat_add_iff 1).2 hSummA
  calc
    (-deriv riemannZeta s / riemannZeta s).re
        = (LSeries f s).re := by rw [hL]
    _ = (∑' n : ℕ, a n).re := by
          simpa [a] using (congrArg Complex.re (LSeries_def₀ hf0 s))
    _ = (∑' n : ℕ, a (n + 1)).re := by
          rw [htail]
    _ = ∑' n : ℕ, (a (n + 1)).re := by
          exact Complex.re_tsum hSummA'
    _ = ∑' n : ℕ, (((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
          Real.cos (t * Real.log (((n + 1 : ℕ) : ℝ)))) /
            ((((n + 1 : ℕ) : ℝ) ^ σ))) := by
          apply tsum_congr
          intro n
          dsimp [a, f]
          rw [hS]
          exact mangoldt_term_re n σ t

end Commons.NumberTheory.Zeta