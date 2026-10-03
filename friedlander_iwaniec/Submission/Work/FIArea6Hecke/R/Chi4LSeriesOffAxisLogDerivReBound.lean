import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_norm_le_of_one_lt_re
import Submission.Commons.NumberTheory.DirichletCharacter.chi4_primeRecips_sub_const_powLog

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea6Hecke.R

open Complex
open scoped LSeries.notation

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## `axisChi4` as the `ℕ`-restriction of the Dirichlet character `χ₄` modulo `4` -/

/-- `axisChi4` is the restriction to `ℕ` of the Dirichlet character `chi4` modulo `4`
(`Commons.NumberTheory.DirichletCharacter.chi4`, the explicit character with values
`0, 1, 0, -1`). -/
lemma axisChi4_eq_chi4_cast (n : ℕ) :
    axisChi4 n = Commons.NumberTheory.DirichletCharacter.chi4 (n : ZMod 4) := by
  rw [axisChi4, Commons.NumberTheory.DirichletCharacter.chi4_apply,
    Commons.NumberTheory.DirichletCharacter.chi4Fun_eq_zmod]

/-- The naive `L`-series of `axisChi4` is the `L`-series of the `ℕ`-restriction of `chi4`. -/
lemma LSeries_axisChi4_eq_LSeries_chi4 :
    LSeries axisChi4
      = LSeries (fun n : ℕ => Commons.NumberTheory.DirichletCharacter.chi4 (n : ZMod 4)) := by
  funext s
  exact LSeries_congr (fun {n} _ => axisChi4_eq_chi4_cast n) s

/-- On `re s > 1`, the quotient `L'/L` for the naive `L`-series of `axisChi4` agrees with the
one for the (entire) Dirichlet `L`-function of `chi4`. -/
lemma deriv_div_LSeries_axisChi4_eq {s : ℂ} (hs : 1 < s.re) :
    deriv (LSeries axisChi4) s / LSeries axisChi4 s
      = deriv (DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4) s
        / DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4 s := by
  rw [LSeries_axisChi4_eq_LSeries_chi4,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries
      (χ := Commons.NumberTheory.DirichletCharacter.chi4) hs,
    ← DirichletCharacter.LFunction_eq_LSeries
      (χ := Commons.NumberTheory.DirichletCharacter.chi4) hs]

/-- On `re s > 1`, the logarithmic derivative of the naive `L`-series of `axisChi4` agrees with
the logarithmic derivative of the Dirichlet `L`-function of `chi4`. -/
lemma logDeriv_LSeries_axisChi4_eq_LFunction_chi4 {s : ℂ} (hs : 1 < s.re) :
    logDeriv (LSeries axisChi4) s
      = logDeriv (DirichletCharacter.LFunction
          Commons.NumberTheory.DirichletCharacter.chi4) s := by
  simp only [logDeriv_apply]
  exact deriv_div_LSeries_axisChi4_eq hs

/-! ## The off-axis bound -/

/-- **The logarithmic derivative of the `L`-series of `χ₄` is `O(log(2+|τ|))` off the axis.**

Two regimes.

* For `1 < σ ≤ 5/4` we use the uniform lower bound for `Re(L'/L)` coming from the Hadamard
  partial-fraction expansion of the completed `L`-function
  (`LFunction_logDeriv_re_regular_uniform`): every zero lies in the critical strip
  `0 < Re ρ < 1`, so the divisor sum contributes non-negatively for `Re s > 1`, and only the
  archimedean factor `≍ (1/2) log(2+|τ|)` survives.
* For `5/4 ≤ σ ≤ 2` the crude von Mangoldt majorant
  `‖L'/L(σ+iτ)‖ ≤ Σ_n Λ(n) n^{-σ} = -ζ'/ζ(σ) ≤ 1/(σ-1) + C ≤ 4 + C` suffices
  (`logDeriv_LFunction_norm_le_of_one_lt_re`). -/
theorem Chi4LSeriesOffAxisLogDerivReBound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ τ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv (LSeries Work.FIArea6Hecke.R.axisChi4) ((σ : ℂ) + (τ : ℂ) * Complex.I)
        / LSeries Work.FIArea6Hecke.R.axisChi4 ((σ : ℂ) + (τ : ℂ) * Complex.I)).re
        ≤ C * (Real.log (2 + |τ|) + 1) := by
  obtain ⟨Cnorm, _hCnormpos, hnorm⟩ :=
    Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_norm_le_of_one_lt_re
  have hreg := Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_re_regular_uniform
    Commons.NumberTheory.DirichletCharacter.chi4
    Commons.NumberTheory.DirichletCharacter.chi4_ne_one'
    Commons.NumberTheory.DirichletCharacter.chi4_isPrimitive
  set C : ℝ := max 1 (max (8 * (Real.log ((4 : ℕ) : ℝ) + 1)) (4 + Cnorm + 1)) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_left 1 _)
  refine ⟨C, hCpos, ?_⟩
  intro σ τ hσ1 hσ2
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hone : (1 : ℝ) < s.re := by rw [hsre]; exact hσ1
  have hs' : s = (σ : ℂ) + Complex.I * (τ : ℂ) := by rw [hs]; ring
  have htrans : -deriv (LSeries axisChi4) s / LSeries axisChi4 s
      = -logDeriv (DirichletCharacter.LFunction
          Commons.NumberTheory.DirichletCharacter.chi4) s := by
    rw [neg_div, deriv_div_LSeries_axisChi4_eq hone, logDeriv_apply]
  rw [htrans]
  have hL0 : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
  have hL1 : 1 ≤ Real.log (2 + |τ|) + 1 := by linarith
  have h4 : 0 < Real.log ((4 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  rcases le_or_gt σ (5 / 4) with hle | hgt
  · -- regime `1 < σ ≤ 5/4`: the uniform regular bound
    have h2 : (-logDeriv (DirichletCharacter.LFunction
        Commons.NumberTheory.DirichletCharacter.chi4) s).re
        ≤ 8 * (Real.log ((4 : ℕ) : ℝ) + Real.log (2 + |τ|) + 1) := by
      have h := hreg σ τ hσ1 hle
      rw [hs']
      exact h
    have hCle : 8 * (Real.log ((4 : ℕ) : ℝ) + 1) ≤ C := by
      rw [hCdef]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h8 : 8 * (Real.log ((4 : ℕ) : ℝ) + Real.log (2 + |τ|) + 1)
        ≤ C * (Real.log (2 + |τ|) + 1) := by
      nlinarith [hL0, h4, hCle]
    linarith
  · -- regime `5/4 ≤ σ ≤ 2`: the crude von Mangoldt majorant
    have hσ54 : 5 / 4 ≤ σ := le_of_lt hgt
    have hnorm' : ‖logDeriv (DirichletCharacter.LFunction
        Commons.NumberTheory.DirichletCharacter.chi4) s‖
        ≤ 1 / (s.re - 1) + Cnorm :=
      hnorm 4 Commons.NumberTheory.DirichletCharacter.chi4 s hone
    have hrecip : 1 / (s.re - 1) ≤ 4 := by
      rw [hsre, div_le_iff₀ (by linarith : (0 : ℝ) < σ - 1)]
      linarith
    have hre : (-logDeriv (DirichletCharacter.LFunction
        Commons.NumberTheory.DirichletCharacter.chi4) s).re ≤ 4 + Cnorm := by
      rw [Complex.neg_re]
      have h1 : -(logDeriv (DirichletCharacter.LFunction
          Commons.NumberTheory.DirichletCharacter.chi4) s).re
          ≤ ‖logDeriv (DirichletCharacter.LFunction
              Commons.NumberTheory.DirichletCharacter.chi4) s‖ :=
        le_trans (neg_le_abs _) (Complex.abs_re_le_norm _)
      linarith
    have hCle : 4 + Cnorm + 1 ≤ C := by
      rw [hCdef]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hmul : C * 1 ≤ C * (Real.log (2 + |τ|) + 1) :=
      mul_le_mul_of_nonneg_left hL1 (le_of_lt hCpos)
    have hCm : C ≤ C * (Real.log (2 + |τ|) + 1) := by simpa using hmul
    linarith

end

end Work.FIArea6Hecke.R
