import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
import Submission.Work.LinnikAreas.eighth_line_arith

/-!
# The `5/8` ("eighth") line bound for primitive Dirichlet `L`-functions

For a primitive non-principal character `ψ` of modulus `N` and every real `t`,

`‖L(ψ, 5/8 + i t)‖ ≤ C · N^{1/4} · (1 + |t|)^{1/4}`

with an absolute constant `C`.

The analytic content is the fully explicit convexity (Phragmén–Lindelöf) bound of the shared
library, `Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs`: for primitive
non-trivial `ψ` mod `N` and `0 ≤ σ ≤ 1`,

`log ‖L(ψ, σ + iT)‖ ≤ ((1-σ)/2)·(log N + log(2+|T|)) + log(log(N(2+|T|)) + 2) + 6`.

At `σ = 5/8` the exponent is `3/16`; exponentiating gives
`‖L‖ ≤ e^6 · N^{3/16} (2+|T|)^{3/16} (log(N(2+|T|)) + 2)`, and the arithmetic estimate
`Work.LinnikAreas.eighth_line_arith` absorbs the logarithm and the factor `2+|T| ≤ 2(1+|T|)`
into the `1/16` of power slack, producing the claim.
-/

set_option autoImplicit false

namespace Work.LinnikAreas

theorem LFunction_eighth_line :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N),
      ψ ≠ 1 → ψ.IsPrimitive → ∀ t : ℝ,
      ‖DirichletCharacter.LFunction ψ ((5 / 8 : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4) := by
  obtain ⟨C₀, hC₀pos, harith⟩ := eighth_line_arith
  refine ⟨Real.exp 6 * C₀, by positivity, ?_⟩
  intro N _inst ψ hψ hprim t
  have hN1nat : (1 : ℕ) ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1nat
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have hxpos : (0 : ℝ) < 2 + |t| := by have := abs_nonneg t; linarith
  have hnx1 : (1 : ℝ) ≤ (N : ℝ) * (2 + |t|) := by
    have h2 : (1 : ℝ) ≤ 2 + |t| := by have := abs_nonneg t; linarith
    nlinarith
  have hlogpos : 0 < Real.log ((N : ℝ) * (2 + |t|)) + 2 := by
    have := Real.log_nonneg hnx1; linarith
  -- the convexity bound of the shared library at `σ = 5/8`
  have hcx := Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs ψ hψ hprim
      (σ := (5 : ℝ) / 8) (T := t) (by norm_num) (by norm_num)
  rw [mul_comm Complex.I (t : ℂ)] at hcx
  set A : ℝ := ((1 - (5 : ℝ) / 8) / 2) * (Real.log (N : ℝ) + Real.log (2 + |t|))
      + Real.log (Real.log ((N : ℝ) * (2 + |t|)) + 2) + 6 with hA
  -- `A` is the convexity exponent; `set` has already replaced it in `hcx`
  have hLbound : Real.log ‖DirichletCharacter.LFunction ψ
      ((((5 : ℝ) / 8 : ℝ)) + (t : ℂ) * Complex.I : ℂ)‖ ≤ A := hcx
  have hnorm_le : ‖DirichletCharacter.LFunction ψ
      ((((5 : ℝ) / 8 : ℝ)) + (t : ℂ) * Complex.I : ℂ)‖ ≤ Real.exp A := by
    rcases eq_or_lt_of_le (norm_nonneg (DirichletCharacter.LFunction ψ
        ((((5 : ℝ) / 8 : ℝ)) + (t : ℂ) * Complex.I : ℂ))) with h | h
    · rw [← h]; exact (Real.exp_pos A).le
    · rw [← Real.exp_log h]; exact Real.exp_le_exp.mpr hLbound
  have hA1 : ((1 - (5 : ℝ) / 8) / 2) * (Real.log (N : ℝ) + Real.log (2 + |t|))
      = Real.log (N : ℝ) * ((3 : ℝ) / 16) + Real.log (2 + |t|) * ((3 : ℝ) / 16) := by ring
  have hexp : Real.exp A = Real.exp 6 * ((N : ℝ) ^ ((3 : ℝ) / 16) * (2 + |t|) ^ ((3 : ℝ) / 16)
      * (Real.log ((N : ℝ) * (2 + |t|)) + 2)) := by
    rw [hA, Real.exp_add, Real.exp_add, hA1, Real.exp_add,
      ← Real.rpow_def_of_pos hNpos, ← Real.rpow_def_of_pos hxpos, Real.exp_log hlogpos]
    ring
  have hmain : ‖DirichletCharacter.LFunction ψ
      ((((5 : ℝ) / 8 : ℝ)) + (t : ℂ) * Complex.I : ℂ)‖
      ≤ (Real.exp 6 * C₀) * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4) := by
    calc ‖DirichletCharacter.LFunction ψ
          ((((5 : ℝ) / 8 : ℝ)) + (t : ℂ) * Complex.I : ℂ)‖
        ≤ Real.exp A := hnorm_le
      _ = Real.exp 6 * ((N : ℝ) ^ ((3 : ℝ) / 16) * (2 + |t|) ^ ((3 : ℝ) / 16)
            * (Real.log ((N : ℝ) * (2 + |t|)) + 2)) := hexp
      _ ≤ Real.exp 6 * (C₀ * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (harith N t hN1nat) (Real.exp_pos 6).le
      _ = (Real.exp 6 * C₀) * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4) := by ring
  have hs : ((((5 : ℝ) / 8 : ℝ)) : ℂ) = (5 / 8 : ℂ) := by norm_num
  rw [hs] at hmain
  exact hmain

end Work.LinnikAreas
