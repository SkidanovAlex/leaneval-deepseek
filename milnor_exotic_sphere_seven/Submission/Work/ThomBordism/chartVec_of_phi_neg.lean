import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Region
import Submission.Work.ThomBordism.exists_chartData_pinned

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The region chart at a point with `Φ < 0`

At a point `m` of the region `{Φ ≤ 0}` at which `Φ m.1 < 0` the region contains a neighbourhood of
`m.1`, and the chart data chosen for the region at `m` is the *pinned* one of
`Work.ThomBordism.exists_chartData_pinned`: the model chart is the identity of the model space and
the ambient chart is the restriction of the preferred chart `chartAt _ m.1` to an open neighbourhood
`U` of `m.1` contained in the region.

Consequently the chart vector `S.chartVec m w`, which a priori is
`S.T m ((S.dom m).extend _ w)`, is literally `(chartAt _ m.1).extend _ w` on the source of the
ambient chart.  This is the `rfl`-level description of the region's charts at such a point, used to
compute the determinant of the transition functions (the ambient orientation input of the
orientation producer).

The result is read off the pin conjunct of `Work.ThomBordism.exists_chartData_pinned`, which
`Submission/Work/PTGeometric/WeakRegion/Region.lean` uses to define the chart data
(`RegionSetupWeak.chartData`).
-/

namespace Work.ThomBordism

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners

/-- **The pin of the chart data in the case `Φ m.1 < 0`.**  The ambient chart `S.dom m` is the
restriction of the preferred chart `chartAt _ m.1` to an open neighbourhood `U ∋ m.1` of which it is
a subset, and the model chart `S.T m` is the identity of the model space. -/
theorem dom_T_of_phi_neg (k : ℕ)
    (S : Work.PTGeometric.WeakRegion.RegionSetupWeak k)
    (m : Work.PTGeometric.WeakRegion.RegionSetupWeak.Region S) (hm : S.Φ m.1 < 0) :
    ∃ U : Set S.A, IsOpen U ∧ m.1 ∈ U ∧
      Work.PTGeometric.WeakRegion.RegionSetupWeak.dom S m =
        (chartAt (EuclideanHalfSpace (8 + k + 1)) m.1).restr U ∧
      (Work.PTGeometric.WeakRegion.RegionSetupWeak.dom S m).source ⊆ U ∧
      Work.PTGeometric.WeakRegion.RegionSetupWeak.T S m =
        Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH
          (EuclideanSpace ℝ (Fin (8 + k + 1))) := by
  have hspec := (Classical.choose_spec (Classical.choose_spec
      (Work.ThomBordism.exists_chartData_pinned k S m)))
  exact hspec.2.2.2.2.2.2.2.2.2 hm

theorem chartVec_of_phi_neg (k : ℕ)
    (S : Work.PTGeometric.WeakRegion.RegionSetupWeak k)
    (m : Work.PTGeometric.WeakRegion.RegionSetupWeak.Region S) (hm : S.Φ m.1 < 0) :
    Work.PTGeometric.WeakRegion.RegionSetupWeak.T S m =
        Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH
          (EuclideanSpace ℝ (Fin (8 + k + 1))) ∧
      (∀ w ∈ (Work.PTGeometric.WeakRegion.RegionSetupWeak.dom S m).source,
        Work.PTGeometric.WeakRegion.RegionSetupWeak.chartVec S m w =
          (chartAt (EuclideanHalfSpace (8 + k + 1)) m.1).extend
            (modelWithCornersEuclideanHalfSpace (8 + k + 1)) w) := by
  obtain ⟨U, hUopen, hmU, hdom, hdomsub, hT⟩ := dom_T_of_phi_neg k S m hm
  refine ⟨hT, ?_⟩
  intro w hw
  show S.T m (S.domExt m w) =
    (chartAt (EuclideanHalfSpace (8 + k + 1)) m.1).extend
      (modelWithCornersEuclideanHalfSpace (8 + k + 1)) w
  rw [hT]
  show (Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH
          (EuclideanSpace ℝ (Fin (8 + k + 1)))) (S.domExt m w) =
    (chartAt (EuclideanHalfSpace (8 + k + 1)) m.1).extend
      (modelWithCornersEuclideanHalfSpace (8 + k + 1)) w
  rw [Work.PTGeometric.WeakRegion.RegionSetupWeak.idPH_apply]
  rw [Work.PTGeometric.WeakRegion.RegionSetupWeak.domExt, hdom]
  rfl

end Work.ThomBordism
