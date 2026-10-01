import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
import Submission.Work.LinnikAreas.eighth_line_arith

/-!
# The quarter-strip bound for primitive Dirichlet `L`-functions

For a primitive non-principal character `ψ` of modulus `N`, every `σ` with `5/8 ≤ σ ≤ 1`
and every real `T`,

`‖L(ψ, σ + i T)‖ ≤ C · N^{1/4} · (1 + |T|)^{1/4}`

with an absolute constant `C`.

This is the `σ = 5/8` bound of `Work.LinnikAreas.LFunction_eighth_line` extended to the whole
strip `5/8 ≤ σ ≤ 1`.  The analytic input is again the explicit convexity
(Phragmén–Lindelöf) bound `Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs`

`log ‖L(ψ, σ + iT)‖ ≤ ((1-σ)/2)·(log N + log(2+|T|)) + log(log(N(2+|T|)) + 2) + 6`

for `0 ≤ σ ≤ 1`.  Since `log N + log(2+|T|) ≥ 0`, the right-hand side is decreasing in `σ`,
so on `σ ≥ 5/8` it is dominated by its value at `σ = 5/8`, i.e. by the exponent `3/16` of the
eighth line.  The arithmetic `Work.LinnikAreas.eighth_line_arith` then absorbs the logarithm
and the factor `2+|T| ≤ 2(1+|T|)` into the `1/16` of power slack.
-/

set_option autoImplicit false

namespace Work.LinnikAreas

theorem LFunction_quarter_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N),
      ψ ≠ 1 → ψ.IsPrimitive → ∀ σ T : ℝ, 5 / 8 ≤ σ → σ ≤ 1 →
      ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (T : ℂ) * Complex.I)‖
        ≤ C * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |T|) ^ ((1 : ℝ) / 4) := by
  obtain ⟨C₀, hC₀pos, harith⟩ := eighth_line_arith
  refine ⟨Real.exp 6 * C₀, by positivity, ?_⟩
  intro N _inst ψ hψ hprim σ T hσ58 hσ1
  have hN1nat : (1 : ℕ) ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1nat
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have hxpos : (0 : ℝ) < 2 + |T| := by have := abs_nonneg T; linarith
  have hnx1 : (1 : ℝ) ≤ (N : ℝ) * (2 + |T|) := by
    have h2 : (1 : ℝ) ≤ 2 + |T| := by have := abs_nonneg T; linarith
    nlinarith
  have hlogpos : 0 < Real.log ((N : ℝ) * (2 + |T|)) + 2 := by
    have := Real.log_nonneg hnx1; linarith
  -- the convexity bound of the shared library at the given `σ`
  have hcx := Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs ψ hψ hprim
      (σ := σ) (T := T) (by linarith) hσ1
  rw [mul_comm Complex.I (T : ℂ)] at hcx
  set A : ℝ := ((1 - (5 : ℝ) / 8) / 2) * (Real.log (N : ℝ) + Real.log (2 + |T|))
      + Real.log (Real.log ((N : ℝ) * (2 + |T|)) + 2) + 6 with hA
  -- the convexity exponent is decreasing in `σ`, so `σ ≥ 5/8` gives the `3/16` exponent
  have hSnn : (0 : ℝ) ≤ Real.log (N : ℝ) + Real.log (2 + |T|) := by
    have h1 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    have h2 : (0 : ℝ) ≤ Real.log (2 + |T|) :=
      Real.log_nonneg (by have := abs_nonneg T; linarith)
    linarith
  have hmono : ((1 - σ) / 2) * (Real.log (N : ℝ) + Real.log (2 + |T|))
      ≤ ((1 - (5 : ℝ) / 8) / 2) * (Real.log (N : ℝ) + Real.log (2 + |T|)) := by
    apply mul_le_mul_of_nonneg_right _ hSnn
    linarith
  have hLbound : Real.log ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ A := by
    rw [hA]
    linarith [hcx, hmono]
  have hnorm_le : ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ Real.exp A := by
    rcases eq_or_lt_of_le (norm_nonneg (DirichletCharacter.LFunction ψ
        ((σ : ℂ) + (T : ℂ) * Complex.I))) with h | h
    · rw [← h]; exact (Real.exp_pos A).le
    · rw [← Real.exp_log h]; exact Real.exp_le_exp.mpr hLbound
  have hA1 : ((1 - (5 : ℝ) / 8) / 2) * (Real.log (N : ℝ) + Real.log (2 + |T|))
      = Real.log (N : ℝ) * ((3 : ℝ) / 16) + Real.log (2 + |T|) * ((3 : ℝ) / 16) := by ring
  have hexp : Real.exp A = Real.exp 6 * ((N : ℝ) ^ ((3 : ℝ) / 16) * (2 + |T|) ^ ((3 : ℝ) / 16)
      * (Real.log ((N : ℝ) * (2 + |T|)) + 2)) := by
    rw [hA, Real.exp_add, Real.exp_add, hA1, Real.exp_add,
      ← Real.rpow_def_of_pos hNpos, ← Real.rpow_def_of_pos hxpos, Real.exp_log hlogpos]
    ring
  have hmain : ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ (Real.exp 6 * C₀) * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |T|) ^ ((1 : ℝ) / 4) := by
    calc ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (T : ℂ) * Complex.I)‖
        ≤ Real.exp A := hnorm_le
      _ = Real.exp 6 * ((N : ℝ) ^ ((3 : ℝ) / 16) * (2 + |T|) ^ ((3 : ℝ) / 16)
            * (Real.log ((N : ℝ) * (2 + |T|)) + 2)) := hexp
      _ ≤ Real.exp 6 * (C₀ * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |T|) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (harith N T hN1nat) (Real.exp_pos 6).le
      _ = (Real.exp 6 * C₀) * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |T|) ^ ((1 : ℝ) / 4) := by ring
  exact hmain

end Work.LinnikAreas
