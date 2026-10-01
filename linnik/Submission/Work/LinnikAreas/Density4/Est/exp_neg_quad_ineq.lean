import Mathlib

namespace Work.LinnikAreas.Density4.Est

/--
For `0 ≤ v ≤ u`:
  `e^{-u} (u² - v²) ≤ 2(1+v) e^{-v} - 2(1+u) e^{-u}`.

Equivalently, `t ↦ e^{-t} ((t+1)² + 1 - v²)` is non-increasing on `[v, ∞)`,
whose derivative is `e^{-t}(v² - t²) ≤ 0` there. Formally we reduce to the
quadratic Taylor bound `e^{w} ≥ 1 + w + w²/2` (`Real.quadratic_le_exp_of_nonneg`)
for `w = u - v ≥ 0`.
-/
theorem exp_neg_quad_ineq {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) :
    Real.exp (-u) * (u ^ 2 - v ^ 2) ≤ 2 * (1 + v) * Real.exp (-v) - 2 * (1 + u) * Real.exp (-u) := by
  have hw : 0 ≤ u - v := by linarith
  have hc : 1 ≤ 1 + v := by linarith
  have hquad := Real.quadratic_le_exp_of_nonneg hw
  have h1 : (u - v) ^ 2 / 2 ≤ Real.exp (u - v) - 1 - (u - v) := by linarith
  have h2 : (1 + v) * ((u - v) ^ 2 / 2) ≤ (1 + v) * (Real.exp (u - v) - 1 - (u - v)) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have key1 : (u - v) ^ 2 ≤ 2 * (1 + v) * (Real.exp (u - v) - 1 - (u - v)) := by
    nlinarith [h2, hc, sq_nonneg (u - v)]
  have key2 : (u - v) ^ 2 + 2 * (1 + v) * ((u - v) + 1) ≤ 2 * (1 + v) * Real.exp (u - v) := by
    nlinarith [key1]
  have hid : (u ^ 2 - v ^ 2) + 2 * (1 + u) = (u - v) ^ 2 + 2 * (1 + v) * ((u - v) + 1) := by ring
  have key3 : (u ^ 2 - v ^ 2) + 2 * (1 + u) ≤ 2 * (1 + v) * Real.exp (u - v) := by
    rw [hid]; exact key2
  have hmul := mul_le_mul_of_nonneg_left key3 (Real.exp_pos (-u)).le
  have hexp : Real.exp (-u) * Real.exp (u - v) = Real.exp (-v) := by
    rw [← Real.exp_add]; congr 1; ring
  have hRHS : Real.exp (-u) * (2 * (1 + v) * Real.exp (u - v)) = 2 * (1 + v) * Real.exp (-v) := by
    calc Real.exp (-u) * (2 * (1 + v) * Real.exp (u - v))
        = 2 * (1 + v) * (Real.exp (-u) * Real.exp (u - v)) := by ring
      _ = 2 * (1 + v) * Real.exp (-v) := by rw [hexp]
  have h4 : Real.exp (-u) * ((u ^ 2 - v ^ 2) + 2 * (1 + u)) ≤ 2 * (1 + v) * Real.exp (-v) := hRHS ▸ hmul
  have hLHS : Real.exp (-u) * ((u ^ 2 - v ^ 2) + 2 * (1 + u)) =
      Real.exp (-u) * (u ^ 2 - v ^ 2) + 2 * (1 + u) * Real.exp (-u) := by ring
  have hgoal : Real.exp (-u) * (u ^ 2 - v ^ 2) + 2 * (1 + u) * Real.exp (-u) ≤ 2 * (1 + v) * Real.exp (-v) :=
    hLHS ▸ h4
  linarith [hgoal]

end Work.LinnikAreas.Density4.Est
