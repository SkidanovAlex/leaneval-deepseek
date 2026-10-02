import Mathlib
import Submission.Work.Tubular.OnePointModel
import Submission.Work.Tubular.TubeBasic
import Submission.Work.Tubular.Local
import Submission.Work.Tubular.Rank
import Submission.Work.Tubular.Compact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

namespace Work.ThomBordism

/-- **The data of the metric-free Pontryagin–Thom collapse of a tube chart.**

Given a tube chart `C` of an embedding `E : V ↪ ℝ^{8+k}` (with `k ≥ 1`, so the normal bundle has
positive rank and the sphere bundle of the normal bundle is non-empty), there are

* a point `q` of the normal sphere bundle (the basepoint of the Thom space),
* a box radius `R ≥ 0` such that the whole tube `C.U` lies in the open box `(-R, R)^{8+k}`, and
* a continuous map `g : (ℝ^{8+k})⁺ → ν⁺` which on the open tube is the radial blow-up of the normal
  foot `y ↦ normalBlowUp E ε (C.inv y)` and which is `∞` off the open tube.

This is the metric-free Pontryagin–Thom collapse as consumed by the Gauss/classifying map
(`Work.Tubular.collapseToOnePoint`, `Work.Tubular.alphaV`), with the sphere-bundle point, the box
radius and the compactness input produced explicitly. -/
theorem tubeChart_collapseToOnePoint_data {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    ∃ (q : Work.Tubular.NormalSphSub E ε) (R : ℝ) (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E))),
      (∀ y, y ∈ C.openTube → g (OnePoint.some y)
        = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) ∧
      (∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty) := by
  classical
  haveI : Nonempty V.pt := inferInstance
  haveI : CompactSpace (Work.Tubular.NormalDiscSub E ε) :=
    Work.Tubular.compactSpace_normalDiscSub E ε
  obtain ⟨q⟩ := Work.Tubular.nonempty_normalSphSub E C.eps_pos (by omega : 8 < 8 + k)
  have hU : IsCompact C.U := C.isCompact_U
  obtain ⟨g, hg2, hg, -⟩ := Work.Tubular.collapseToOnePoint E C q hU
  obtain ⟨R, hR, hbox⟩ := C.exists_box
  exact ⟨q, R, hR.le, hbox, g, hg2, hg⟩

end Work.ThomBordism
