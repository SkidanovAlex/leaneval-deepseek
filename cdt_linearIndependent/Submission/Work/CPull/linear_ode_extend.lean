import Mathlib
import Submission.Work.OdeCont.ode_continuation

/-!
# Scalar linear ODE continuation on the punctured unit disc

`Work.CPull.linear_ode_extend` : a solution `V` of the scalar linear ODE `V' = a(z)V + b(z)`,
known to be holomorphic on a disc `ball 0 r` (`0 < r < 1`) and solving the equation on the
punctured disc `0 < ‖z‖ < r`, extends holomorphically to the whole unit disc.  The coefficients
`a, b` need only be holomorphic on the punctured unit disc `0 < ‖z‖ < 1` (they may be singular
at `0`); the analyticity of `V` at `0` is part of the hypotheses.

The proof is a direct instantiation of the vector-valued continuation theorem
`Work.OdeCont.ode_continuation` (`Submission.CDTPlan.OdeContinuation`) at `k = 1`, with the
`1 × 1` matrix `A z 0 0 = a z` and the vector `b z 0 = b z`; the inner radius is `r/2`, so
that `a, b` are holomorphic on the annulus `r/2 < ‖z‖ < 1` required by the interface.
-/

namespace Work.CPull

theorem linear_ode_extend {a b V : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (ha : DifferentiableOn ℂ a {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1})
    (hb : DifferentiableOn ℂ b {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1})
    (hV : DifferentiableOn ℂ V (Metric.ball (0 : ℂ) r))
    (hode : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r → HasDerivAt V (a z * V z + b z) z) :
    ∃ Y : ℂ → ℂ, DifferentiableOn ℂ Y (Metric.ball (0 : ℂ) 1) ∧
      Set.EqOn Y V (Metric.ball (0 : ℂ) r) := by
  classical
  -- The annulus on which the vector-valued continuation theorem is applied.
  obtain ⟨Y, hYdiff, hYeq⟩ := Work.OdeCont.ode_continuation 1
    (fun z _ _ => a z) (fun z _ => b z) (r / 2) r (fun z _ => V z)
    (by linarith) (by linarith) (le_of_lt hr1)
    (differentiableOn_pi.mpr (fun _ => differentiableOn_pi.mpr (fun _ =>
      ha.mono (fun z hz => ⟨lt_trans (by linarith : (0:ℝ) < r / 2) hz.1, hz.2⟩))))
    (differentiableOn_pi.mpr (fun _ =>
      hb.mono (fun z hz => ⟨lt_trans (by linarith : (0:ℝ) < r / 2) hz.1, hz.2⟩)))
    (differentiableOn_pi.mpr (fun _ => by simpa using hV))
    (fun z h1 h2 => by
      rw [hasDerivAt_pi]
      intro _
      simpa [Fin.sum_univ_one] using hode z (lt_trans (by linarith : (0:ℝ) < r / 2) h1) h2)
  exact ⟨fun z => Y z 0, (differentiableOn_pi.mp hYdiff) 0,
    fun z hz => congrFun (hYeq hz) 0⟩

end Work.CPull
