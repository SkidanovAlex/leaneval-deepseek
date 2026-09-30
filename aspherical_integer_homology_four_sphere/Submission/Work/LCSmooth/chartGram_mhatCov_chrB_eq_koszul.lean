import Mathlib
import Submission.Work.Final.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LCSmooth

/-- **The Koszul identity in charts for the connection of `M̂`, with no hypotheses.**

`M̂` is the assembled Ratcliffe–Tschantz space of `Work.Space.RTData`, whose connection is
`Work.Final.mhatCov (rt := rt) = Work.LeviCivita.lcConn (I := I4) (M := rt.Mhat)`.  Since that
connection is metric compatible and torsion free (`Work.LeviCivita.lcConn_compat`,
`Work.LeviCivita.lcConn_torsion`), the general chart Koszul identity
`Work.LeviCivita.chartGram_chrB_eq_koszul` specialises to the hypothesis-free statement below:
the chart Christoffel symbol of `M̂` is determined by the derivatives of the chart metric.

Proof: `Work.LeviCivita.chartGram_chrB_eq_koszul (I := I4) (Work.LeviCivita.lcConn_compat …)
(Work.LeviCivita.lcConn_torsion …) x₀ p hp a b c`, noting that `Work.Final.mhatCov (rt := rt)` is
by definition that `lcConn`.  Imports: `Mathlib` + `Submission.Work.Final.All`. -/
theorem chartGram_mhatCov_chrB_eq_koszul [rt : Work.Space.RTData]
    (x₀ p : rt.Mhat) (hp : p ∈ (chartAt Work.Space.E4 x₀).source) (a b c : Work.Space.E4) :
    Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀ p
        (Submission.ChartCurv.chrB (Work.Final.mhatCov (rt := rt)) x₀ p a b) c =
      (1/2) * (Work.Curvature.chartDg (I := Work.Space.I4) x₀ p b a c
        + Work.Curvature.chartDg (I := Work.Space.I4) x₀ p a b c
        - Work.Curvature.chartDg (I := Work.Space.I4) x₀ p c a b) := by
  have h := Work.LeviCivita.chartGram_chrB_eq_koszul (I := Work.Space.I4) (M := rt.Mhat)
    (Work.LeviCivita.lcConn_compat (I := Work.Space.I4) (M := rt.Mhat))
    (Work.LeviCivita.lcConn_torsion (I := Work.Space.I4) (M := rt.Mhat)) x₀ p hp a b c
  simpa [Work.Final.mhatCov] using h

end Work.LCSmooth
