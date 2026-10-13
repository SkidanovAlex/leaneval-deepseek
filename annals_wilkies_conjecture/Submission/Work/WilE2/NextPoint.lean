/-
  Work.WilE2 — auxiliary point: the next zero of the function after `u j`.

  For a `T`-periodic function `φ` whose zeros in `[0, T)` are enumerated by a strictly increasing
  `u : Fin p → ℝ`, the zero immediately following `u j` in the cyclic order is `u (cycSucc hp j)`,
  except at the last index where the next zero is the first zero of the following period,
  `u 0 + T`.  `nextPt` packages both cases.
-/
import Mathlib
import Submission.Work.WilE2.Rolle

set_option autoImplicit false

namespace Work.WilE2

open Set

/-- The zero of `φ` immediately following `u j` in the cyclic order: `u (cycSucc hp j)`, shifted by
`T` when `cycSucc` wraps around to the first index. -/
def nextPt {p : ℕ} (hp : 0 < p) (T : ℝ) (u : Fin p → ℝ) (j : Fin p) : ℝ :=
  u (cycSucc hp j) + if (j : ℕ) + 1 < p then 0 else T

theorem nextPt_of_lt {p : ℕ} (hp : 0 < p) (T : ℝ) (u : Fin p → ℝ) (j : Fin p)
    (h : (j : ℕ) + 1 < p) :
    nextPt hp T u j = u ⟨(j : ℕ) + 1, h⟩ := by
  have hc : cycSucc hp j = ⟨(j : ℕ) + 1, h⟩ := Fin.ext (cycSucc_of_lt hp j h)
  rw [nextPt, hc]
  simp [h]

theorem nextPt_of_not_lt {p : ℕ} (hp : 0 < p) (T : ℝ) (u : Fin p → ℝ) (j : Fin p)
    (h : ¬ (j : ℕ) + 1 < p) :
    nextPt hp T u j = u ⟨0, hp⟩ + T := by
  rw [nextPt, cycSucc_of_not_lt hp j h]
  simp [h]

end Work.WilE2
