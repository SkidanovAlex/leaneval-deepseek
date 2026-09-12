import ChallengeDeps
import Submission.FinalAssembly
import Submission.InterfacesA
import Submission.DirectionB
import Submission.DirBCompact

/-!
# Final assembly of the Hopf–Rinow theorem

The three geometric interfaces are proved in sibling modules:
* `Submission.InterfacesA.geoRightExt` / `.geoLeftExt` (direction A, under `[CompleteSpace M]`);
* `Submission.DirectionB.geoBallsCompact` (direction B);
and `Submission.FinalAssembly.hopf_rinow_core` reduces the challenge equivalence to them.
-/

open scoped Manifold ENNReal ContDiff Topology
open EMetric
open Bundle

namespace Submission

open LeanEval.Geometry

/-- The full Hopf–Rinow theorem, assembled from the three geometric interfaces. -/
theorem hopf_rinow_sketch {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [LocallyCompactSpace M] [ConnectedSpace M] :
    IsGeodesicallyComplete M ↔ CompleteSpace M := by
  exact FinalAssembly.hopf_rinow_core (M := M)
    (fun hc => by letI : CompleteSpace M := hc; exact geoRightExt I M)
    (fun hc => by letI : CompleteSpace M := hc; exact geoLeftExt I M)
    (fun hgc p R hR => DirectionB.geoBallsCompact I M hgc p R hR)

end Submission
