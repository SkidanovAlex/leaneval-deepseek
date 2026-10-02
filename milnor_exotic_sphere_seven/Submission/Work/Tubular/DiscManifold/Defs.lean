import Mathlib
import Submission.Work.SignatureBordism.BallBoundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option warn.classDefReducibility false

/-!
# Charted spaces obtained from a homeomorphism or from a change of model
-/

open scoped Manifold ContDiff Topology

namespace Work.Tubular

noncomputable section

/-- **The charted space obtained by pushing forward along a homeomorphism.** -/
def chartedSpaceOfHomeomorph {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    (c : ChartedSpace H M) {M' : Type*} [TopologicalSpace M'] (e : M ≃ₜ M') : ChartedSpace H M' where
  atlas := c.atlas.image (fun f => OpenPartialHomeomorph.trans e.symm.toOpenPartialHomeomorph f)
  chartAt y := OpenPartialHomeomorph.trans e.symm.toOpenPartialHomeomorph (c.chartAt (e.symm y))
  mem_chart_source y := by
    rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    exact ⟨trivial, c.mem_chart_source (e.symm y)⟩
  chart_mem_atlas y := Set.mem_image_of_mem _ (c.chart_mem_atlas (e.symm y))

/-- **The charted space obtained by composing the charts with a homeomorphism of model spaces.** -/
def chartedSpaceOfModelHomeo {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
    {M : Type*} [TopologicalSpace M] (c : ChartedSpace H' M) (Φ : H ≃ₜ H') : ChartedSpace H M where
  atlas := c.atlas.image (fun e => OpenPartialHomeomorph.trans e Φ.symm.toOpenPartialHomeomorph)
  chartAt x := OpenPartialHomeomorph.trans (c.chartAt x) Φ.symm.toOpenPartialHomeomorph
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    exact ⟨c.mem_chart_source x, trivial⟩
  chart_mem_atlas x := Set.mem_image_of_mem _ (c.chart_mem_atlas x)

/-! ## The closed unit ball, read on the model space -/

/-- The point of the closed unit ball `D^{n+1}` with a given model vector `v`, with the junk value
`0` outside the ball.  This is the total function used to state the smoothness of the ball's charts
when they are read on the model space (`Work.Tubular.contDiffOn_chartAt_discPt`). -/
def discPt (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) : ↥(Work.SignatureBordism.Ball n) := by
  classical
  exact if h : v ∈ Work.SignatureBordism.Ball n then ⟨v, h⟩ else 0

@[simp] theorem discPt_of_mem (n : ℕ) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (h : v ∈ Work.SignatureBordism.Ball n) : discPt n v = ⟨v, h⟩ := by
  rw [discPt]; exact dif_pos h

end

end Work.Tubular
