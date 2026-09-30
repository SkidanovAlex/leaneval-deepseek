import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_fe
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.re_completedLogDeriv_two_tight

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-- **Tight one-sided bound at `Re s = -1`.**

For every primitive, non-trivial Dirichlet character `χ` mod `N` and every real `T`,

    -Re (Λ′/Λ)(χ)(-1 + iT) ≤ log N + (1/2)·log(2 + |T|) + 3/2.

Method.  The functional equation in logarithmic-derivative form
(`Commons.NumberTheory.DirichletCharacter.completedLogDeriv_fe`)

    logDeriv Λ(χ)(s) = -log N - logDeriv Λ(χ⁻¹)(1 - s)

at `s = -1 + iT` (with `1 - s = 2 - iT`) gives

    -Re logDeriv Λ(χ)(s) = log N + Re logDeriv Λ(χ⁻¹)(2 - iT).

The two non-vanishing hypotheses of the functional equation are discharged exactly as in
`Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_tight`: a zero at
`Re s = -1` would lie outside the critical strip (`zerosInStrip`), and at `Re s = 2 ≥ 1`
the non-trivial L-function does not vanish.  Finally the real part of the second summand is
bounded by the tight one-sided estimate on the line `Re s = 2`
(`Commons.NumberTheory.DirichletCharacter.re_completedLogDeriv_two_tight` applied to `χ⁻¹`
at `-T`), giving `≤ (1/2)·log(2+|T|) + 3/4`; adding `log N` and relaxing `3/4 ≤ 3/2`
finishes. -/
theorem completedLogDeriv_neg_one_re_tight {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) :
    -(logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + Complex.I * (T : ℂ))).re ≤
      Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |T|) + 3 / 2 := by
  set s : ℂ := (-1 : ℂ) + Complex.I * (T : ℂ) with hsdef
  have hsre : s.re = -1 := by
    simp [hsdef]
  -- χ⁻¹ is nontrivial
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = (χ⁻¹)⁻¹ := by simp
      _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
      _ = 1 := by simp
  -- `completedLFunction χ s ≠ 0`: a zero at Re s = -1 would lie outside the critical strip.
  have hΛ : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro hz
    have hstrip := zerosInStrip χ hχ hχprim s hz
    have hlt : (0 : ℝ) < (-1 : ℝ) := by simpa [hsre] using hstrip.1
    exact (not_lt_of_ge (by norm_num : (-1 : ℝ) ≤ 0)) hlt
  -- `completedLFunction χ⁻¹ (1 - s) ≠ 0`: Re (1 - s) = 2 ≥ 1, and nontrivial L-functions
  -- do not vanish on Re s ≥ 1 (quotient by the nonzero gamma factor).
  have hre1s : 1 ≤ (1 - s : ℂ).re := by
    rw [Complex.sub_re, hsre]
    norm_num
  have hw0 : (1 : ℂ) - s ≠ 0 := by
    intro hz
    have hle : (1 : ℝ) ≤ 0 := by
      simpa [hz] using hre1s
    norm_num at hle
  have hΛc : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0 := by
    intro hz
    have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ⁻¹)
      (1 - s) (Or.inl hw0)
    have hL : DirichletCharacter.LFunction (χ⁻¹) (1 - s) = 0 := by
      rw [hdiv, hz]
      simp
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ⁻¹) (Or.inl hχinv) hre1s) hL
  -- The functional equation in log-derivative form
  have hfe := completedLogDeriv_fe χ hχprim s hΛ hΛc
  -- Bound the real part of the second summand on the line `Re s = 2` at `-T`
  have hb2 : (logDeriv (DirichletCharacter.completedLFunction (χ⁻¹))
        ((2 : ℂ) + Complex.I * ((-T : ℝ) : ℂ))).re ≤
      (1 / 2) * Real.log (2 + |(-T : ℝ)|) + 3 / 4 := by
    exact re_completedLogDeriv_two_tight (χ := χ⁻¹) hχinv (-T)
  have harg : (2 : ℂ) + Complex.I * ((-T : ℝ) : ℂ) = (1 : ℂ) - s := by
    simp [hsdef]
    ring
  have hb2' : (logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) ((1 : ℂ) - s)).re ≤
      (1 / 2) * Real.log (2 + |T|) + 3 / 4 := by
    rw [← harg]
    simpa [abs_neg] using hb2
  -- The exact real-part identity coming from the functional equation
  have hkey : -(logDeriv (DirichletCharacter.completedLFunction χ) s).re =
      Real.log (N : ℝ) +
        (logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) ((1 : ℂ) - s)).re := by
    rw [hfe]
    simp only [Complex.neg_re, Complex.sub_re, Complex.ofReal_re]
    ring
  rw [hkey]
  linarith [hb2']

end Commons.NumberTheory.DirichletCharacter
