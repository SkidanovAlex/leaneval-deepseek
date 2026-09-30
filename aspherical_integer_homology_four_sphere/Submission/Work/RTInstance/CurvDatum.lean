/-
# The model curvature datum of `Work.Final.FinalInputs`

`Work.Final.curvLe_of_models` (delivered by the area `Final`) produces the curvature bound
`∀ K > 0, RauchK.CurvLe lcConn K` from the datum

```
hmodels : ∀ x, ∃ G ∈ D.models.models, SecNonposAt G ((extChartAt I4 x) x) ∧
  ∀ᶠ q in 𝓝 ((extChartAt I4 x) x), ∀ a b, chartGram x ((extChartAt I4 x).symm q) a b = G q a b
```

for the atlas `D.models` of `M̂`.  The area `Space` already proves the *second* conjunct
(`Work.Space.ModelAtlas.chartGram_is_model`, from the isometry of the transitions); this file turns
the *first* one -- the non-positivity of the model at the chart image -- into the class
`Work.RTInstance.RTDataNonpos` and derives `hmodels`, hence the field `curvLe` of
`Work.Final.FinalInputs`.

For the atlas of `M̂` the class is discharged by `Work.RTInstance.ChartLayer.secNonposAt`: the model
of a chart is the (total modification of the) upper half space / filling / core metric of its layer,
and the chart image lies in the region of the layer (`ChartLayer.ok`).
-/
import Mathlib
import Submission.Work.RTInstance.PreAtlas

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace
open Bundle

namespace Work.RTInstance

/-- **The pointwise curvature hypothesis on a `Work.Space.RTData`**: the model of every chart has
non-positive sectional curvature at the image of every point of its source. -/
class RTDataNonpos (D : Work.Space.RTData) : Prop where
  /-- The model of a chart is non-positively curved at the image of a point of its source. -/
  out : ∀ i : Fin D.models.n, ∀ ⦃x : D.Mhat⦄, x ∈ (D.models.chart i).source →
    Curvature.SecNonposAt (D.models.field i) (D.models.chart i x)

/-- **The model curvature datum of `Work.Final.FinalInputs.curvLe_field`.** -/
theorem RTDataNonpos.hmodels [D : Work.Space.RTData] (h : RTDataNonpos D) (x : D.Mhat) :
    ∃ G ∈ D.models.models, Curvature.SecNonposAt G ((extChartAt I4 x) x) ∧
      ∀ᶠ q in 𝓝 ((extChartAt I4 x) x), ∀ a b : E4,
        Submission.ChartConnection.chartGram (I := I4) x ((extChartAt I4 x).symm q) a b
          = G q a b := by
  have hx : (extChartAt I4 x) x = (D.models.chart (D.models.indexOf x)) x := by
    rw [show (extChartAt I4 x) x = chartAt E4 x x by
      simp [extChartAt_coe, modelWithCornersSelf_coe]]
    rfl
  refine ⟨D.models.field (D.models.indexOf x), ⟨_, rfl⟩, ?_, ?_⟩
  · rw [hx]
    exact h.out _ (Work.Space.FinAtlas.indexOf_mem D.instFinAtlas x)
  · rw [hx]
    have hbase := Work.Space.ModelAtlas.chartGram_eq_model (A := D.models) x
    have hs : ∀ q : E4, (extChartAt I4 x).symm q = (chartAt E4 x).symm q := by
      intro q; simp [extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
    have hcont : ContinuousAt (chartAt E4 x).symm (chartAt E4 x x) :=
      ContinuousOn.continuousAt ((chartAt E4 x).continuousOn_invFun)
        ((chartAt E4 x).open_target.mem_nhds (mem_chart_target E4 x))
    have hxa : (chartAt E4 x).symm (chartAt E4 x x) = x :=
      (chartAt E4 x).left_inv (mem_chart_source E4 x)
    obtain ⟨U, hU, hUsub⟩ := (eventually_iff_exists_mem).mp hbase
    filter_upwards [hcont.eventually (hxa ▸ hU),
      (chartAt E4 x).open_target.mem_nhds (mem_chart_target E4 x)] with q hq hqT
    intro a b
    rw [hs q]
    rw [hUsub ((chartAt E4 x).symm q) hq a b, (chartAt E4 x).right_inv hqT]
    rfl

end Work.RTInstance
