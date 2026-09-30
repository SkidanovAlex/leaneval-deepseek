import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Complex

/-- For `m` outside the closed ball `closedBall a |R|`, the function
`z ↦ log ‖z - m‖` is harmonic in a neighborhood of that closed ball
(the logarithm of the modulus of the analytic function `z ↦ z - m`,
which is non-vanishing on the ball). -/
theorem harmonicOnNhd_log_norm_sub {a m : ℂ} {R : ℝ} (hR : 0 < R)
    (hm : m ∉ Metric.closedBall a |R|) :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ => Real.log ‖z - m‖)
      (Metric.closedBall a |R|) := by
  intro x hx
  apply AnalyticAt.harmonicAt_log_norm (f := fun z : ℂ => z - m) (z := x)
  · fun_prop
  · intro hsub
    exact hm (by simpa [sub_eq_zero.mp hsub] using hx)

end Commons.Analysis.Complex