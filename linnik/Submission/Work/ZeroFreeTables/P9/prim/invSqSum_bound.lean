/-
# ZeroFreeTables/P9/prim/invSqSum_bound

The `masterP3`-shaped form of the inverse-square zero-sum bound.  The substantive estimate
`invSqSum N χ s ≤ C (log N + log(2+‖s‖) + 2)` already exists sorry-free in the repository
(`Work.ZeroFreeTables.lam0w.invSqSum_uniform`, and the `‖s‖ ≤ 11` version
`Work.ZeroFreeTables.XY.invSqSum_bound_xy`).  What the §9 assembly needs is the version
*indexed by the scale* `L`: with `log N ≤ L`, `1 ≤ L` and `‖s‖ ≤ L + 5` (which holds on the
`1 + a/L`-line, `|Im s| ≤ 4`, once `L ≥ a`),

`invSqSum N χ s ≤ C · (L + 2)`,

so the `(α/L)²`- and `(α/L)³`-weighted error terms in `SigmaP3L_le_nearP3sum_add` are
`O(α²/L)` and go below `α·e` for large `L`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.lam0w.Bounds

open DirichletCharacter

namespace Work.ZeroFreeTables.P9.prim

/-- **Scaled inverse-square zero-sum bound.**  With `1 ≤ L`, `log N ≤ L` and `‖s‖ ≤ L + 5`,
`invSqSum N χ s ≤ C (L + 2)` for a universal constant `C`. -/
theorem invSqSum_uniform_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) {s : ℂ} {L : ℝ}, 1 ≤ L → Real.log (N : ℝ) ≤ L → ‖s‖ ≤ L + 5 →
      Work.ZeroFreeTables.P9.invSqSum N χ s ≤ C * (L + 2) := by
  obtain ⟨C, hCpos, hC⟩ := Work.ZeroFreeTables.lam0w.invSqSum_uniform
  refine ⟨6 * C, by positivity, ?_⟩
  intro N _ χ hχ hprim s L hL hlogN hs
  have h1 := hC χ hχ hprim s
  have hlog2 : Real.log (2 + ‖s‖) ≤ L + 6 := by
    have hpos : (0 : ℝ) < 2 + ‖s‖ := by positivity
    calc Real.log (2 + ‖s‖) ≤ (2 + ‖s‖) - 1 := Real.log_le_sub_one_of_pos hpos
      _ ≤ (2 + (L + 5)) - 1 := by linarith
      _ = L + 6 := by ring
  calc Work.ZeroFreeTables.P9.invSqSum N χ s
      ≤ C * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := h1
    _ ≤ C * (L + (L + 6) + 2) := mul_le_mul_of_nonneg_left (by linarith) hCpos.le
    _ ≤ 6 * C * (L + 2) := by nlinarith [hCpos, hL]

end Work.ZeroFreeTables.P9.prim
