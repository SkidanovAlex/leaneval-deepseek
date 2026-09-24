import Mathlib
import Submission.Work.Mori.Defs
import Submission.HolomorphicLog

namespace Work.Mori

/-- **A holomorphic function of constant modulus is constant.**  On a connected complex
one-manifold, `HolomorphicOnX U univ` together with `∀ x, ‖U x‖ = c` forces `U` to be constant.

Route: at every point, in a chart, the local representation of `U` is a complex-differentiable
function on a ball of constant modulus; Mathlib's maximum-modulus principle on a ball,
`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` (with `IsMaxOn (norm ∘ f) _ x` supplied by the
constant-modulus hypothesis), shows that `U` is eventually equal to `U x` near `x`.  Hence `U` is
locally constant, and a locally constant function on a connected space is constant
(`IsLocallyConstant.apply_eq_of_isPreconnected`).  (`Submission.HolomorphicOnXAt_iff_chart` is the
bridge to the chart representation.)  Note: `Submission.HolomorphicOnX.exists_eq_const_of_norm_eq`
(`Submission/HolomorphicLog.lean`) is a strictly more general statement already in the library, so
this is a one-line corollary of it. -/
theorem eq_const_of_holomorphicOnX_norm_eq {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : X → ℂ} (hU : Submission.HolomorphicOnX U Set.univ) {c : ℝ} (hc : ∀ x, ‖U x‖ = c)
    (x₀ : X) : ∀ x, U x = U x₀ :=
  Submission.HolomorphicOnX.exists_eq_const_of_norm_eq hU x₀ fun x => by rw [hc x, hc x₀]

end Work.Mori
