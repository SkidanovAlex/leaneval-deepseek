import Mathlib
import Submission.Work.Final.Framework

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The chart Christoffel symbol equals the Koszul Christoffel symbol of the model metric

Let `M` be a Riemannian manifold of the project's framework (`ChartedRiem`), with a smooth,
torsion-free, metric-compatible connection `C.cov` (`ChartedRiemConn`).  Let `G : E4 → E4 → E4 → ℝ`
be a model metric field which agrees with the chart expression of the metric near the chart image
of `p`, in the sense of the hypothesis `hmodel`.  Then the chart Christoffel symbol
`Submission.ChartCurv.chrB C.cov x₀ p a b` of the connection coincides with
`Work.Curvature.koszulChr G ((extChartAt I4 x₀) p) a b`, the Christoffel symbol computed from the
model field `G` by the Koszul formula.

The proof is the standard one.

* `Work.LeviCivita.chartGram_chrB_eq_koszul` (the Koszul identity in charts) says that `chrB`
  solves the Koszul equation against the chart metric:
  `chartGram x₀ p (chrB cov x₀ p a b) c = ½ (D b a c + D a b c − D c a b)`, where `D = chartDg` is
  the chart derivative of the metric component.
* `Work.Curvature.chartDg_eq_dG` converts each `chartDg` into the model derivative `dG` of `G`,
  using `hmodel`.
* Since `hmodel` is an *eventual* statement at the point `(extChartAt I4 x₀) p`, and every
  neighbourhood of that point contains it, `hmodel` also pins down the value of `G` there:
  `G ((extChartAt I4 x₀) p) = chartGram x₀ p` as bilinear forms.  (This is where the fact that
  `(extChartAt I4 x₀).symm ((extChartAt I4 x₀) p) = p`, which uses `hp`, enters.)
* Hence `chrB cov x₀ p a b` solves the Koszul equation for `G` at that point, and
  `Work.Curvature.koszulChr_eq_of_forall` (which is uniqueness of the solution, from `hlin` and
  `hpos`) identifies it with `koszulChr G`.
-/

namespace Work.Final

theorem chrB_eq_koszulChr
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace Work.Space.E4 M]
    [Work.Final.ChartedRiem M] [C : Work.Final.ChartedRiemConn M]
    (x₀ p : M) (hp : p ∈ (chartAt Work.Space.E4 x₀).source) {G : Work.Curvature.MetricField}
    (hmodel : Filter.Eventually (fun q => ∀ a b : Work.Curvature.E4,
        Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀
          ((extChartAt Work.Space.I4 x₀).symm q) a b = G q a b)
      (nhds ((extChartAt Work.Space.I4 x₀) p)))
    (hlin : ∀ x y c : Work.Curvature.E4,
      G ((extChartAt Work.Space.I4 x₀) p) (x - y) c
        = G ((extChartAt Work.Space.I4 x₀) p) x c
          - G ((extChartAt Work.Space.I4 x₀) p) y c)
    (hpos : ∀ v : Work.Curvature.E4, v ≠ 0 → 0 < G ((extChartAt Work.Space.I4 x₀) p) v v)
    (a b : Work.Curvature.E4) :
    Submission.ChartCurv.chrB C.cov x₀ p a b
      = Work.Curvature.koszulChr G ((extChartAt Work.Space.I4 x₀) p) a b := by
  -- the chart at `x₀` is a chart at `p` as well
  have hsymm : (extChartAt Work.Space.I4 x₀).symm ((extChartAt Work.Space.I4 x₀) p) = p :=
    (extChartAt Work.Space.I4 x₀).left_inv (by simpa only [extChartAt_source] using hp)
  -- the model field agrees with the chart metric *at* the point, not only near it
  have hG : ∀ a b : Work.Curvature.E4,
      Submission.ChartConnection.chartGram (I := Work.Space.I4) x₀ p a b
        = G ((extChartAt Work.Space.I4 x₀) p) a b := by
    intro a b
    have h := (Filter.Eventually.self_of_nhds hmodel) a b
    rwa [hsymm] at h
  -- the chart derivative of the metric is the model derivative of `G`
  have hDg : ∀ d a c : Work.Curvature.E4,
      Work.Curvature.chartDg (I := Work.Space.I4) x₀ p d a c
        = Work.Curvature.dG G ((extChartAt Work.Space.I4 x₀) p) d a c := by
    intro d a c
    exact Work.Curvature.chartDg_eq_dG (I := Work.Space.I4) x₀ p d a c
      (hmodel.mono fun q hq => hq a c)
  -- the Koszul identity in charts for `chrB`
  have hkos := Work.LeviCivita.chartGram_chrB_eq_koszul (I := Work.Space.I4) (M := M)
      C.compat C.torsion x₀ p hp a b
  -- `chrB` solves the Koszul equation for the model field `G`
  have hz : ∀ c : Work.Curvature.E4,
      G ((extChartAt Work.Space.I4 x₀) p) (Submission.ChartCurv.chrB C.cov x₀ p a b) c
        = Work.Curvature.koszulRHS G ((extChartAt Work.Space.I4 x₀) p) a b c := by
    intro c
    rw [← hG (Submission.ChartCurv.chrB C.cov x₀ p a b) c, hkos c,
      hDg b a c, hDg a b c, hDg c a b, Work.Curvature.koszulRHS]
    norm_num
  exact (Work.Curvature.koszulChr_eq_of_forall hlin hpos hz).symm

end Work.Final
