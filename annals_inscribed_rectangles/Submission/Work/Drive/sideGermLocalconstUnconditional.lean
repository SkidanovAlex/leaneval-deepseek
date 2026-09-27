import Mathlib
import Submission.Work.Drive.sideGermLocalconstOfPlaneChart
import Submission.Work.Drive.sideGerm_good_exists
import Submission.Work.Drive.chartIsSmooth

/-!
# The germ route's local constancy, **unconditional** (the `hdisj` obligation gone, the Sard in)

`Work.Drive.sideGerm_localconst_of_planeChart` reduced the germ route's local constancy to the Sard
existence `hA`.  `Work.Drive.sideGerm_good_exists` (`Submission/Work/Drive/sideGerm_good_exists.lean`) is
now **proved** (via `sgGoodPair_of_small`, sorry-free, axiom-clean, and already consumed downstream), so
the last hypothesis can be discharged: the theorem below has **no hypothesis beyond the chart data**
(`IsPlaneChart γ hγne Q`, `hγne`, `hγinj`, `hΞ`, `hc`, `hcbot`, `w ∈ Zc γ`) — in particular *no*
`hdisj : Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q)`, which is not obtainable from
`w ∈ Zc γ` and the chart's clauses.

This is the germ route's `hn4` (local constancy of the side value in the angle), and with it
`sideGerm_spec` no longer needs any hypothesis that the route cannot supply.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-- **The germ side value is locally constant in the angle — unconditionally.** -/
theorem sideGerm_localconst_of_planeChart_unconditional {γ : Circle → ℝ × ℝ} {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hQ : IsPlaneChart γ hγne Q) (hΞ : ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    ∀ᶠ w' in 𝓝 w, sideGerm Ξ Q c w' = sideGerm Ξ Q c w :=
  sideGerm_localconst_of_planeChart Ξ Q c hγne hγinj hQ hΞ hc hcbot
    (fun w' => sideGerm_good_exists Ξ Q c hΞ (IsSmoothChart_of_isPlaneChart hQ) hc w') hw

end

end Work.Drive
