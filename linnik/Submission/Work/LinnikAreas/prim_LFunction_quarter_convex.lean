import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs

/-!
# The `1/4`-convexity bound for primitive Dirichlet `L`-functions at `σ ≥ 1/2`

For a primitive non-principal character `χ` of modulus `N`, and every `σ` with `1/2 ≤ σ ≤ 1`
and every real `t`,

`‖L(χ, σ + i t)‖ ≤ C · N^{1/4} · (1 + |t|)^{1/4} · (log (N (2 + |t|)) + 2)`

with an absolute constant `C`.

The analytic input is the explicit convexity (Phragmén–Lindelöf) bound of the shared library,
`Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs`: for primitive
non-trivial `χ` mod `N` and `0 ≤ σ ≤ 1`,

`log ‖L(χ, σ + it)‖ ≤ ((1-σ)/2)·(log N + log(2+|t|)) + log(log(N(2+|t|)) + 2) + 6`.

Because `log N + log(2+|t|) ≥ 0`, the right-hand side is *decreasing* in `σ`; on `σ ≥ 1/2` it is
dominated by its value at `σ = 1/2`, where the exponent is exactly `1/4`. Exponentiating gives

`‖L‖ ≤ e^6 · N^{1/4} (2+|t|)^{1/4} (log(N(2+|t|)) + 2)`,

and the elementary estimate `2 + |t| ≤ 2 (1 + |t|)` together with
`Real.mul_rpow` turns `(2+|t|)^{1/4}` into `2^{1/4} (1+|t|)^{1/4}`, which is absorbed into `C`.
-/

set_option autoImplicit false

namespace Work.LinnikAreas

theorem prim_LFunction_quarter_convex :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4)
              * (Real.log ((N : ℝ) * (2 + |t|)) + 2) := by
  refine ⟨Real.exp 6 * 2 ^ ((1 : ℝ) / 4),
    mul_pos (Real.exp_pos 6) (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro N _inst χ hχ hprim σ t hσ hσ1
  have hN1nat : (1 : ℕ) ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1nat
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have hxpos : (0 : ℝ) < 2 + |t| := by have := abs_nonneg t; linarith
  have h1tpos : (0 : ℝ) < 1 + |t| := by have := abs_nonneg t; linarith
  have hNt1 : (1 : ℝ) ≤ (N : ℝ) * (2 + |t|) := by
    have h2 : (1 : ℝ) ≤ 2 + |t| := by have := abs_nonneg t; linarith
    nlinarith
  have hlogpos : 0 < Real.log ((N : ℝ) * (2 + |t|)) + 2 := by
    have := Real.log_nonneg hNt1; linarith
  have hSnn : (0 : ℝ) ≤ Real.log (N : ℝ) + Real.log (2 + |t|) := by
    have h1 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    have h2 : (0 : ℝ) ≤ Real.log (2 + |t|) :=
      Real.log_nonneg (by have := abs_nonneg t; linarith)
    linarith
  -- the convexity bound of the shared library at the given `σ`
  have hcx := Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs χ hχ hprim
      (σ := σ) (T := t) (by linarith) hσ1
  rw [mul_comm Complex.I (t : ℂ)] at hcx
  -- the exponent is decreasing in `σ`, so `σ ≥ 1/2` gives the `1/4` exponent
  have hmono : ((1 - σ) / 2) * (Real.log (N : ℝ) + Real.log (2 + |t|))
      ≤ ((1 : ℝ) / 4) * (Real.log (N : ℝ) + Real.log (2 + |t|)) := by
    apply mul_le_mul_of_nonneg_right _ hSnn
    linarith
  set A : ℝ := ((1 : ℝ) / 4) * (Real.log (N : ℝ) + Real.log (2 + |t|))
      + Real.log (Real.log ((N : ℝ) * (2 + |t|)) + 2) + 6 with hA
  have hLbound : Real.log ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ A := by
    rw [hA]; linarith [hcx, hmono]
  have hnorm_le : ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.exp A := by
    rcases eq_or_lt_of_le (norm_nonneg (DirichletCharacter.LFunction χ
        ((σ : ℂ) + (t : ℂ) * Complex.I))) with h | h
    · rw [← h]; exact (Real.exp_pos A).le
    · rw [← Real.exp_log h]; exact Real.exp_le_exp.mpr hLbound
  have hA1 : ((1 : ℝ) / 4) * (Real.log (N : ℝ) + Real.log (2 + |t|))
      = Real.log (N : ℝ) * ((1 : ℝ) / 4) + Real.log (2 + |t|) * ((1 : ℝ) / 4) := by ring
  have hexp : Real.exp A = Real.exp 6 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (2 + |t|) ^ ((1 : ℝ) / 4)
      * (Real.log ((N : ℝ) * (2 + |t|)) + 2)) := by
    rw [hA, Real.exp_add, Real.exp_add, hA1, Real.exp_add,
      ← Real.rpow_def_of_pos hNpos, ← Real.rpow_def_of_pos hxpos, Real.exp_log hlogpos]
    ring
  -- `2 + |t| ≤ 2 (1 + |t|)` and `Real.mul_rpow` absorb the shift by `2`
  have hyq : (2 + |t|) ^ ((1 : ℝ) / 4) ≤ 2 ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4) := by
    have hle : 2 + |t| ≤ 2 * (1 + |t|) := by have := abs_nonneg t; linarith
    have h := Real.rpow_le_rpow hxpos.le hle (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) h1tpos.le] at h
  have hmain : ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (Real.exp 6 * 2 ^ ((1 : ℝ) / 4)) * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4)
          * (Real.log ((N : ℝ) * (2 + |t|)) + 2) := by
    calc ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Real.exp A := hnorm_le
      _ = Real.exp 6 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (2 + |t|) ^ ((1 : ℝ) / 4)
            * (Real.log ((N : ℝ) * (2 + |t|)) + 2)) := hexp
      _ ≤ Real.exp 6 * ((N : ℝ) ^ ((1 : ℝ) / 4)
            * (2 ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4))
            * (Real.log ((N : ℝ) * (2 + |t|)) + 2)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 6).le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hyq (Real.rpow_nonneg hNpos.le _)) hlogpos.le
      _ = (Real.exp 6 * 2 ^ ((1 : ℝ) / 4)) * (N : ℝ) ^ ((1 : ℝ) / 4)
            * (1 + |t|) ^ ((1 : ℝ) / 4)
            * (Real.log ((N : ℝ) * (2 + |t|)) + 2) := by ring
  exact hmain

end Work.LinnikAreas
