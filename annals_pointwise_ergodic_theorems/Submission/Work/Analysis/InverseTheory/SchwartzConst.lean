/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.InverseTheory.Basic

/-!
# The explicit constant of Lemma `calc`

Lemma `calc` of §6 of Krause–Mirek–Tao bounds the error in the smooth approximation of an interval
indicator by

`K(ψ) · (ε^10 + ⟨ε(x-a)⟩^{-10} + ⟨ε(x-b)⟩^{-10})`,

with a constant `K(ψ)` depending only on `ψ ∈ 𝓢(ℝ, ℂ)` (the paper writes `≲_ψ`).  This module
fixes an explicit, manifestly large enough such constant: `calcConst ψ` is the `100`-th power of
the sum of the four Schwartz seminorms of `ψ` and `𝓕ψ` that control their decay to order `12`,
plus `2`.

The constant is deliberately crude; the only properties used are `2 ≤ calcConst ψ` and that it
dominates `2 ^ 84 * D ^ 2`, where `D` is the seminorm sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators FourierTransform

namespace Work.Analysis.InverseTheory

/-- The sum of the four Schwartz seminorms that control `ψ` and `𝓕ψ` to order `12`:
`‖ψ‖_∞`, `‖‖·‖^12 ψ‖_∞`, `‖𝓕ψ‖_∞` and `‖‖·‖^12 𝓕ψ‖_∞` (written with `|·|` so that
nonnegativity is trivial). -/
noncomputable def schwartzSeminormSum (ψ : SchwartzR) : ℝ :=
  |SchwartzMap.seminorm ℝ 0 0 ψ| + |SchwartzMap.seminorm ℝ 12 0 ψ|
    + |SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ)| + |SchwartzMap.seminorm ℝ 12 0 (𝓕 ψ)|

/-- The explicit constant of Lemma `calc`: `(schwartzSeminormSum ψ + 2) ^ 100`. -/
noncomputable def calcConst (ψ : SchwartzR) : ℝ := (schwartzSeminormSum ψ + 2) ^ 100

theorem schwartzSeminormSum_nonneg (ψ : SchwartzR) : 0 ≤ schwartzSeminormSum ψ := by
  rw [schwartzSeminormSum]; positivity

theorem one_le_schwartzSeminormSum_add_two (ψ : SchwartzR) : 1 ≤ schwartzSeminormSum ψ + 2 := by
  linarith [schwartzSeminormSum_nonneg ψ]

theorem two_le_calcConst (ψ : SchwartzR) : 2 ≤ calcConst ψ := by
  rw [calcConst]
  calc (2 : ℝ) ≤ schwartzSeminormSum ψ + 2 := by linarith [schwartzSeminormSum_nonneg ψ]
    _ ≤ (schwartzSeminormSum ψ + 2) ^ 100 :=
        le_self_pow₀ (one_le_schwartzSeminormSum_add_two ψ) (by norm_num)

theorem calcConst_pos (ψ : SchwartzR) : 0 < calcConst ψ :=
  lt_of_lt_of_le (by norm_num) (two_le_calcConst ψ)

end Work.Analysis.InverseTheory
