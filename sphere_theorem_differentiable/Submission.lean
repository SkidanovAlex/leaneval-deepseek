import ChallengeDeps
import Submission.Helpers
import Submission.Work.Diff.Glue.main_of_contracts
import Submission.Work.Diff.C.classical_end_v2
import Submission.Work.Diff.L.flow_end_conn
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.STE.short_time_existence
import Submission.Work.Diff.EXT.extension
import Submission.Work.Diff.MP.hamilton_mp
import Submission.Work.Diff.Evol.curv_evolution
import Submission.Work.Diff.Evol.curv_variation
import Submission.Work.Diff.Evol.lap_parallel
import Submission.Work.Diff.Alg.quarter_to_pic2
import Submission.Work.Diff.Alg.pinching_set_exists
import Submission.Work.Diff.GE.gradient_estimate
import Submission.Work.Diff.GE.evol_rm_normsq
import Submission.Work.Diff.GE.evol_drm_normsq
import Submission.Work.Diff.GE.evol_scal
import Submission.Work.Diff.GE.norms_smooth
import Submission.Work.Diff.GE.bianchi_kato
import Submission.Work.Diff.Alg.pinching_algebra
import Submission.Work.Diff.GE.scalar_max_principle
import Submission.Work.Diff.Dim2.dim2_sphere
import Submission.Work.Diff.ODE.flow_smooth
import Submission.Work.Diff.ODE.flow_smooth_icc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission

theorem differentiable_sphere_theorem [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (_htor : cov.torsion = 0) (_hmet : IsMetricCompatible cov)
    (_hpinch : QuarterPinched cov) :
    Nonempty
      (M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯
        (sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1)) := by
  rcases hdim.eq_or_lt with h2 | h3
  · -- dimension 2: smooth Reeb (no Ricci flow)
    exact Work.Diff.Dim2.dim2_sphere h2.symm cov _htor _hmet _hpinch Work.Diff.ODE.flow_smooth
  · -- dimension ≥ 3: Ricci flow to (1+η)-pinching, then the classical high-pinching end
    have hn : 3 ≤ Module.finrank ℝ E := h3
    have hLC := Work.Diff.T.lc_smooth (I := I) (M := M)
    have hLV := Work.Diff.T.lc_variation (I := I) (M := M) hLC
    have hSTE := Work.Diff.STE.short_time_existence (I := I) (M := M) hLC hLV
    have hCV := Work.Diff.Evol.curv_variation (I := I) (M := M) hLC hLV
    have hCE := Work.Diff.Evol.curv_evolution (I := I) (M := M) hLC hLV hCV
    have hLP := Work.Diff.Evol.lap_parallel (I := I) (M := M) hLC
    have hPP := Work.Diff.MP.hamilton_mp (I := I) (M := M) hLC hLV hCE hLP
    have hEXT := Work.Diff.EXT.extension (I := I) (M := M) hLC hLV hSTE hPP
    have hSMP := Work.Diff.GE.scalar_max_principle (I := I) (M := M) hLC
    have hGE := Work.Diff.GE.gradient_estimate (I := I) (M := M) hn
      (Work.Diff.GE.evol_rm_normsq hLC hLV) (Work.Diff.GE.evol_drm_normsq hLC hLV)
      (Work.Diff.GE.evol_scal hLC hLV) (Work.Diff.GE.norms_smooth hLC)
      (Work.Diff.GE.bianchi_kato hn hLC) (Work.Diff.Alg.pinching_algebra _ hn) hSMP
    exact Work.Diff.Glue.main_of_contracts
      (Work.Diff.C.classical_end_v2 hdim)
      (Work.Diff.L.flow_end_conn hdim cov _htor _hmet _hpinch hLC hLV hSTE hEXT hPP
        (Work.Diff.Alg.quarter_to_pic2 _) (Work.Diff.Alg.pinching_set_exists _ hdim) hGE hSMP)

end Submission
