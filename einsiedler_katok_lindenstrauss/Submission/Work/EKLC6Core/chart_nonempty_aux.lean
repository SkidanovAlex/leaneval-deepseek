import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.thin_boundary_ae
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLC6Route.exists_chart

namespace Work.EKLC6Core

/-- `Work.EKLC6Core.chart_nonempty_aux` is the `EKLC6Core`-namespace restatement of the
chart-existence lemma `L2a` of `EKLComp/C6GEOM_ROUTE_LEAD.md` §3.1: every probability
measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and every `t : Fin 3 → ℝ` admits a `G⁰G⁺(t)`-chart
`Work.EKLC6Route.Chart μ t` (a point `z₀`, radii `r, ρ, δ` with `δ ≤ 1/100` and
`4000 r, 4000 ρ ≤ δ`, Borel coordinate maps `uc, θ` with `Chart.coord`, uniform injectivity
`Chart.inj` on `V δ`, positive measure `Chart.pos`, and the `µ`-thin `U`-shell bound
`Chart.thin`).

The full mathematical content is established in `Submission/Work/EKLC6Route/exists_chart.lean`
as `Work.EKLC6Route.exists_chart`; this lemma is the bridge to the `Work.EKLC6Core`
namespace, from which the chart/window component (`EKLC6Route.Main`) of the EKL argument
is assembled. -/
theorem chart_nonempty_aux {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) :
    Nonempty (Work.EKLC6Route.Chart μ t) :=
  Work.EKLC6Route.exists_chart (μ := μ) t

end Work.EKLC6Core
