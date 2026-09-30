import Mathlib
import Submission.Work.Final.Basic
import Submission.Work.Final.MhatCover
import Submission.Work.Final.mvRightX_zero_surjective
import Submission.Work.Final.secNonpos_of_chartModels
import Submission.Work.Final.Framework

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Final

open scoped Manifold ContDiff Bundle Topology ENNReal

theorem curvLe_of_models [rt : Work.Space.RTData]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (Work.Final.mhatCov (rt := rt)) Work.Final.smoothGrade]
    (hmodels : ∀ x : rt.Mhat, ∃ G ∈ rt.models.models,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      Filter.Eventually (fun q => ∀ a b : Work.Space.E4,
          Submission.ChartConnection.chartGram (I := Work.Space.I4) x
            ((extChartAt Work.Space.I4 x).symm q) a b = G q a b)
        (nhds ((extChartAt Work.Space.I4 x) x))) :
    ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K := by
  intro K hK
  refine Work.RiemLib.CurvLe_of_nonpos ?_ hK
  intro x u v hu hv huv
  obtain ⟨G, _hGmem, hsec, hmod⟩ := hmodels x
  letI : Work.Final.ChartedRiem rt.Mhat := Work.Final.instChartedRiemMhat
  letI C : Work.Final.ChartedRiemConn rt.Mhat :=
    { cov := Work.Final.mhatCov (rt := rt)
      compat := Work.LeviCivita.lcConn_compat
      torsion := Work.LeviCivita.lcConn_torsion }
  exact Work.Final.secNonpos_of_chartModels (C := C) x hsec hmod u v hu hv huv

end Work.Final
