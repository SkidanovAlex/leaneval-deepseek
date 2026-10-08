/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Shared vocabulary for counting subgroups of prime order in `PSL(2,q)`

This file fixes the notation used by the files of `Submission/Work/L2F/Props/Count/`:

* `companion t = !![0, -1; 1, t]`, the companion matrix of `X² - tX + 1`;
* `quad t = X² - tX + 1`;
* `Rootless t` : `quad t` has no root in `F` (equivalently, `companion t` has no eigenvalue);
* `HasEigenvector M` : `M` has an eigenvector in `F²`.
-/
import Mathlib
import Submission.Work.L2F.Defs

open scoped MatrixGroups
open Matrix Polynomial

namespace Work.L2F.Count

variable (F : Type*) [Field F]

/-- The companion matrix `!![0, -1; 1, t]` of the polynomial `X² - tX + 1`. -/
def companion (t : F) : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, t]

/-- The polynomial `X² - tX + 1`, the characteristic polynomial of an element of `SL(2,F)` of
trace `t`. -/
noncomputable def quad (t : F) : Polynomial F := Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1

/-- `X² - tX + 1` has no root in `F`. -/
def Rootless (t : F) : Prop := ∀ a : F, a ^ 2 - t * a + 1 ≠ 0

/-- `M` has an eigenvector over `F`. -/
def HasEigenvector (M : Matrix (Fin 2) (Fin 2) F) : Prop :=
  ∃ v : Fin 2 → F, v ≠ 0 ∧ ∃ μ : F, M *ᵥ v = μ • v

/-- The `0`/`1` indicator of a proposition, as a natural number.  (A `Prop`-indexed version of
`if p then 1 else 0` whose `Decidable` instance is fixed to the classical one, so that it can be
used in statements without a `Decidable` hypothesis.) -/
noncomputable def indicator (p : Prop) : ℕ := @ite ℕ p (Classical.propDecidable p) 1 0

theorem indicator_eq_one {p : Prop} (h : p) : indicator p = 1 := by
  rw [indicator, ite_eq_left h]

theorem indicator_eq_zero {p : Prop} (h : ¬p) : indicator p = 0 := by
  rw [indicator, ite_eq_right h]

theorem indicator_pos {p : Prop} (h : p) : 0 < indicator p := by
  rw [indicator_eq_one h]; norm_num

theorem indicator_eq_one_iff {p : Prop} : indicator p = 1 ↔ p := by
  constructor
  · intro h
    by_contra hp
    rw [indicator_eq_zero hp] at h
    exact one_ne_zero h.symm
  · exact indicator_eq_one

theorem indicator_eq_zero_iff {p : Prop} : indicator p = 0 ↔ ¬p := by
  constructor
  · intro h hp
    rw [indicator_eq_one hp] at h
    exact one_ne_zero h
  · exact indicator_eq_zero

variable {F}

@[simp] theorem companion_apply_00 (t : F) : companion F t 0 0 = 0 := rfl
@[simp] theorem companion_apply_01 (t : F) : companion F t 0 1 = -1 := rfl
@[simp] theorem companion_apply_10 (t : F) : companion F t 1 0 = 1 := rfl
@[simp] theorem companion_apply_11 (t : F) : companion F t 1 1 = t := rfl

theorem companion_ne_one (t : F) : companion F t ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simpa [companion] using this

theorem companion_det (t : F) : (companion F t).det = 1 := by
  rw [companion, Matrix.det_fin_two_of]
  ring

theorem companion_trace (t : F) : (companion F t).trace = t := by
  rw [companion, Matrix.trace_fin_two]
  simp

/-- Cayley–Hamilton for the companion matrix: `C * C = t • C - 1`. -/
theorem companion_sq (t : F) : companion F t * companion F t = t • companion F t - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem eval_quad (t x : F) : (quad F t).eval x = x ^ 2 - t * x + 1 := by
  simp [quad]

theorem companion_charpoly (t : F) : (companion F t).charpoly = quad F t := by
  rw [Matrix.charpoly_fin_two, quad, companion_trace, companion_det]
  simp

theorem quad_isRoot_iff (t a : F) : (quad F t).IsRoot a ↔ a ^ 2 - t * a + 1 = 0 := by
  rw [Polynomial.IsRoot, eval_quad]

theorem rootless_iff (t : F) : Rootless F t ↔ ∀ a : F, ¬ (quad F t).IsRoot a := by
  simp only [Rootless, quad_isRoot_iff]

theorem rootless_ne_two {t : F} (h : Rootless F t) : t ≠ 2 := by
  intro ht
  refine h 1 ?_
  rw [ht]
  ring

end Work.L2F.Count
