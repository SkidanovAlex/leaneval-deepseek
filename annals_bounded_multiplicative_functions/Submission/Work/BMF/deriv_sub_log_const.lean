import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Changing the coefficient of `log` in `P - (T/2π)log - G` by `(T - A)/(2π)` changes the
derivative by exactly `-(T - A)/(2π) * (1/t)`. -/
theorem deriv_sub_log_const (P G : Polynomial ℝ) (A T t : ℝ) (ht : 0 < t) :
    deriv (fun s => P.eval s - T / (2 * Real.pi) * Real.log s - G.eval s) t =
    deriv (fun s => P.eval s - A / (2 * Real.pi) * Real.log s - G.eval s) t
      - (T - A) / (2 * Real.pi) * (1 / t) := by
  have hlog : HasDerivAt (fun s : ℝ => Real.log s) (1 / t) t := by
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt ht)
  have hdT : HasDerivAt (fun s => P.eval s - T / (2 * Real.pi) * Real.log s - G.eval s)
      (P.derivative.eval t - T / (2 * Real.pi) * (1 / t) - G.derivative.eval t) t := by
    have h := ((P.hasDerivAt t).sub (hlog.const_mul (T / (2 * Real.pi)))).sub (G.hasDerivAt t)
    convert h using 1
  have hdA : HasDerivAt (fun s => P.eval s - A / (2 * Real.pi) * Real.log s - G.eval s)
      (P.derivative.eval t - A / (2 * Real.pi) * (1 / t) - G.derivative.eval t) t := by
    have h := ((P.hasDerivAt t).sub (hlog.const_mul (A / (2 * Real.pi)))).sub (G.hasDerivAt t)
    convert h using 1
  rw [hdT.deriv, hdA.deriv]
  have ht' : t ≠ 0 := ne_of_gt ht
  field_simp
  ring

end Work.BMF
