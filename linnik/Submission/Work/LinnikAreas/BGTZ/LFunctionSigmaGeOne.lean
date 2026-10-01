import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one

/-!
# `L(χ, σ + i t) ≪ log(2 + |t|)` for `χ ≠ 1` and `σ ≥ 1`

For a fixed modulus `q ≥ 2` and a non-principal Dirichlet character `χ` mod `q`, the
`L`-function is bounded by an absolute constant (depending on `q`) times `log(2 + |t|)`
on the vertical line `Re s = σ` for every `σ ≥ 1`, uniformly in `σ`.

The analytic content is the shared-library estimate
`Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one`,

  `‖L(χ,s)‖ ≤ log q + log(2 + |Im s|) + 6`   for `χ ≠ 1` and `Re s ≥ 1`,

(proved there from the absolute convergence of the Dirichlet series on `Re s > 1`,
partial summation with the trivial bound `|Σ_{n≤x} χ(n)| ≤ 2q` for `χ ≠ 1`, and
continuity down to `Re s = 1`).  Since the modulus is fixed, `log q` is a constant and
the additive error `6` is absorbed into the multiplicative `log(2 + |t|)` factor as soon
as `log(2 + |t|) ≥ 1`, which holds because `|t| ≥ 1` forces `2 + |t| ≥ 3 > e`.
-/

namespace Work.LinnikAreas.BGTZ

theorem LFunctionSigmaGeOne (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 3 → 1 ≤ |t| →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * Real.log (2 + |t|) := by
  refine ⟨Real.log (q : ℝ) + 7, ?_, ?_⟩
  · -- positivity of the constant: `log 2 ≤ log q` and `log 2 > 0`
    have h2q : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have h1 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : Real.log 2 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) h2q
    linarith
  · intro χ hχ σ t hσ1 _hσ3 ht1
    -- the shared-library bound at `s = σ + i t`
    have hs : 1 ≤ (((σ : ℂ) + (t : ℂ) * Complex.I).re) := by
      rw [show ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ by simp]
      exact hσ1
    have hlib := Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one χ hχ
      ((σ : ℂ) + (t : ℂ) * Complex.I) hs
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [him] at hlib
    -- `log(2 + |t|) ≥ 1` because `2 + |t| ≥ 3 > e`
    have hlog3 : (1 : ℝ) ≤ Real.log (2 + |t|) := by
      have ht3 : (3 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) ht3
      have h2 : (1 : ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
        exact Real.exp_one_lt_three
      linarith
    -- `log q + 6 ≥ 0` because `q ≥ 2`
    have hlogq6 : (0 : ℝ) ≤ Real.log (q : ℝ) + 6 := by
      have h2q : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have h1 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have h2 : Real.log 2 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) h2q
      linarith
    -- absorb the additive constants into the multiplicative logarithm
    have hkey : 0 ≤ (Real.log (q : ℝ) + 6) * (Real.log (2 + |t|) - 1) :=
      mul_nonneg hlogq6 (by linarith)
    calc ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Real.log (q : ℝ) + Real.log (2 + |t|) + 6 := hlib
      _ ≤ (Real.log (q : ℝ) + 7) * Real.log (2 + |t|) := by nlinarith [hkey]

end Work.LinnikAreas.BGTZ
