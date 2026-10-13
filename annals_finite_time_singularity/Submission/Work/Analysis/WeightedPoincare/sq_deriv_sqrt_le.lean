import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Analysis.WeightedPoincare

theorem sq_deriv_sqrt_le {P Pd P1 : ℝ → ℝ} {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (hd : HasDerivAt P (Pd t) t) (hPnn : 0 ≤ P t) (hP1nn : 0 ≤ P1 t)
    (hbnd : (t * Pd t) ^ 2 ≤ 4 * P t * P1 t) :
    deriv (fun s => Real.sqrt (P s + ε)) t ^ 2 ≤ P1 t / t ^ 4 * t ^ 2 := by
  -- `P t + ε > 0`, so the square root is differentiable with derivative
  -- `Pd t / (2 * √(P t + ε))`.
  have hPtε : 0 < P t + ε := by linarith
  have hderiv : deriv (fun s => Real.sqrt (P s + ε)) t = Pd t / (2 * Real.sqrt (P t + ε)) :=
    ((hd.add_const ε).sqrt (ne_of_gt hPtε)).deriv
  rw [hderiv]
  -- `P1 t / t ^ 4 * t ^ 2 = P1 t / t ^ 2` since `t ≠ 0`.
  have hright : P1 t / t ^ 4 * t ^ 2 = P1 t / t ^ 2 := by
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hright, div_pow, mul_pow, Real.sq_sqrt hPtε.le]
  norm_num
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- It remains to show `(Pd t)^2 * t^2 ≤ P1 t * (4 * (P t + ε))`, which follows from
  -- the hypothesis `(t * Pd t)^2 ≤ 4 * P t * P1 t` and `0 ≤ P1 t`.
  have key : (Pd t) ^ 2 * t ^ 2 ≤ 4 * (P t + ε) * P1 t := by
    have h1 : 4 * P t * P1 t ≤ 4 * (P t + ε) * P1 t := by nlinarith [hε, hP1nn]
    nlinarith [hbnd, h1]
  linarith [key]

end Work.Analysis.WeightedPoincare
