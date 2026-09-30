import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_fe
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_tight

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-- Tight pointwise bound for the logarithmic derivative of the completed Dirichlet
L-function on the vertical line `Re s = -1`:

`‖logDeriv (completedLFunction χ) (-1 + iT)‖ ≤ log N + (1/2)·log(2+|T|) + 3`

for all real `T` and every primitive, non-trivial Dirichlet character `χ` mod `N`.

Method.  The functional equation in logarithmic-derivative form
(`Commons.NumberTheory.DirichletCharacter.completedLogDeriv_fe`) gives

`logDeriv Λ(χ)(s) = -log N - logDeriv Λ(χ⁻¹)(1 - s)`,

so at `s = -1 + iT` we have `logDeriv Λ(χ)(-1+iT) = -log N - logDeriv Λ(χ⁻¹)(2 - iT)`.
Its two non-vanishing hypotheses are discharged as in
`Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_le`: at `s = -1+iT` a zero
of `Λ(χ)` would lie outside the critical strip (`zerosInStrip`), and at `2 - iT` (real part
`2 ≥ 1`) the completed L-function of the non-trivial character `χ⁻¹` does not vanish
(`Mathlib`'s `DirichletCharacter.LFunction_ne_zero_of_one_le_re` together with
`LFunction_eq_completed_div_gammaFactor`: the gamma factor is non-zero there).

Finally the second summand is bounded by the tight bound on the line `Re s = 2`
(`Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_tight` applied to `χ⁻¹` at
`-T`), `‖logDeriv Λ(χ⁻¹)(2 - iT)‖ ≤ (1/2)·log(2+|T|) + 3`, and the triangle inequality plus
`0 ≤ log N` finishes. -/
theorem completedLogDeriv_neg_one_tight {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) : ‖logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + Complex.I * (T : ℂ))‖ ≤ Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |T|) + 3 := by
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
  -- Bound the second summand using the tight Re = 2 bound at `-T`
  have hb2 : ‖logDeriv (DirichletCharacter.completedLFunction (χ⁻¹))
        ((2 : ℂ) + Complex.I * ((-T : ℝ) : ℂ))‖ ≤
      (1 / 2) * Real.log (2 + |(-T : ℝ)|) + 3 := by
    exact completedLogDeriv_two_tight (χ := χ⁻¹) hχinv (-T)
  have harg : (2 : ℂ) + Complex.I * ((-T : ℝ) : ℂ) = (1 : ℂ) - s := by
    simp [hsdef]
    ring
  have hb2' : ‖logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) ((1 : ℂ) - s)‖ ≤
      (1 / 2) * Real.log (2 + |T|) + 3 := by
    rw [harg] at hb2
    simpa [abs_neg] using hb2
  -- log N ≥ 0, hence ‖-((log N : ℝ) : ℂ)‖ = log N
  have hN1 : 1 ≤ (N : ℝ) := by
    have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hN1nat : 1 ≤ N := by omega
    exact_mod_cast hN1nat
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hnorm1 : ‖-((Real.log (N : ℝ) : ℂ))‖ ≤ Real.log (N : ℝ) := by
    rw [norm_neg, Complex.norm_of_nonneg hlogN_nonneg]
  -- triangle inequality
  have hmain : ‖logDeriv (DirichletCharacter.completedLFunction χ) s‖ ≤
      Real.log (N : ℝ) + ((1 / 2) * Real.log (2 + |T|) + 3) := by
    calc
      ‖logDeriv (DirichletCharacter.completedLFunction χ) s‖
          = ‖-((Real.log (N : ℝ) : ℂ)) -
                logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) ((1 : ℂ) - s)‖ := by
              rw [hfe]
      _ ≤ ‖-((Real.log (N : ℝ) : ℂ))‖ +
            ‖logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) ((1 : ℂ) - s)‖ := by
            simpa [sub_eq_add_neg, norm_neg] using
              (norm_add_le (-((Real.log (N : ℝ) : ℂ)))
                (-(logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) ((1 : ℂ) - s))))
      _ ≤ Real.log (N : ℝ) + ((1 / 2) * Real.log (2 + |T|) + 3) := by
            exact add_le_add hnorm1 hb2'
  simpa [hsdef, add_assoc] using hmain

end Commons.NumberTheory.DirichletCharacter
