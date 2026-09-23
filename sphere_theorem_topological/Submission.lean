import ChallengeDeps
import Submission.Helpers
import Submission.Curvature
import Submission.Geodesic
import Submission.Variation
import Submission.ChartConnection
import Submission.Gauss
import Submission.Length
import Submission.Distance
import Submission.EDist
import Submission.ChartBounds
import Submission.GeodesicSpeed
import Submission.CurvatureVec
import Submission.Minimal
import Submission.Jacobi
import Submission.ChartCurv
import Submission.SecondVariation
import Submission.IndexForm
import Submission.ChartCurvCont
import Submission.IndexForm2
import Submission.GeodesicChart
import Submission.Pinch
import Submission.CurveField
import Submission.GeodesicExtend
import Submission.GeodesicGlobal
import Submission.GeodesicGlobal2
import Submission.BonnetMyers
import Submission.BonnetMyers2
import Submission.JacobiGen
import Submission.BonnetMyers3
import Submission.SecondVar2
import Submission.Minimising
import Submission.GapEstimate
import Submission.GlobalExp
import Submission.CornerCut
import Submission.HopfRinow
import Submission.HopfRinow2
import Submission.CurveCov
import Submission.JacobiOrth
import Submission.Roadmap
import Submission.JetGap
import Submission.ChartPieces
import Submission.GlobalBM
import Submission.PinchUpper
import Submission.Rauch
import Submission.ConjPoint
import Submission.RauchLocal
import Submission.RauchGlobal
import Submission.IndexLemma
import Submission.RauchCompare
import Submission.RauchCompareK
import Submission.ConjRadius
import Submission.JacobiVec
import Submission.JacobiTensor
import Submission.ShapeOperator
import Submission.RauchUpper
import Submission.HingeCompare
import Submission.FlowJacobi
import Submission.ExpBound
import Submission.RauchGen
import Submission.ExpBound2
import Submission.GeoBack
import Submission.FirstVariation
import Submission.HingeAsymptotic
import Submission.SphereCoord
import Submission.ModelBound
import Submission.ModelPath
import Submission.HingeLocal
import Submission.HingeGlobal
import Submission.HingeKey
import Submission.HingeKey2
import Submission.HingeGExp
import Submission.GExpFlow
import Submission.JacobiGauss
import Submission.ChartFlowVar
import Submission.ChartFlowModel
import Submission.HingeUniform
import Submission.GExpRay
import Submission.HingePiece
import Submission.HingeClosed
import Submission.GSBall
import Submission.GSConcave
import Submission.GSCritical
import Submission.GSConcaveSeg
import Submission.GSConcaveGen
import Submission.GSStep1
import Submission.GSFar
import Submission.GSNoCrit
import Submission.GSDisk
import Submission.GSField
import Submission.GSGlobal
import Submission.GSGlobal2
import Submission.GapEstimate2
import Submission.JetGapSq
import Submission.JetGapLin
import Submission.GSFlow
import Submission.GSMono
import Submission.GSLevel
import Submission.GSCross
import Submission.GSSlab
import Submission.GSHalfDisk
import Submission.GSChartBall
import Submission.GSHalf
import Submission.GSCapMono
import Submission.GSCap
import Submission.GSRestricted
import Submission.SphereSmallDiam
import Submission.PinchUniform
import Submission.MetricScale
import Submission.Klingenberg
import Submission.InjRadius
import Submission.ClosedGeodesic
import Submission.CutWitness
import Submission.CutPoint
import Submission.CutStep
import Submission.GExpGlob
import Submission.GExpRay2
import Submission.GExpTwoSided
import Submission.GExpRayIdent
import Submission.GExpBoundary
import Submission.CutStep2
import Submission.GExpVelocity
import Submission.GExpRayVelocity
import Submission.GExpFlowVelocity
import Submission.ChartFlowHom
import Submission.ChartFlowJoint
import Submission.ChartFlowRoundTrip
import Submission.CutTime
import Submission.LensSync
import Submission.CutStep3
import Submission.LocalDiffeo
import Submission.KlingenbergLoop
import Submission.CutKlingenberg
import Submission.InjRadiusCut
import Submission.KlingenbergStep
import Submission.RauchK
import Submission.InjSup
import Submission.GeoLimit
import Submission.GExpJoint
import Submission.UniformInj
import Submission.GExpRayZero
import Submission.LensLoop
import Submission.LocalInj
import Submission.KlingenbergLemma
import Submission.GExpSmooth
import Submission.GExpLocalInj
import Submission.VariationJacobi
import Submission.JacobiLinear
import Submission.RayChart
import Submission.RayJacobi
import Submission.RayConj
import Submission.InjHalf
import Submission.XuStep
import Submission.BrokenLength
import Submission.CornerStrict
import Submission.InjDiam
import Submission.GExpTranslate
import Submission.InjBall
import Submission.Shorten
import Submission.KlingenbergCore
import Submission.SegmentDomain
import Submission.KlingenbergTransfer
import Submission.ConjCut
import Submission.IndexCorner
import Submission.IndexCorner2
import Submission.SingularConj
import Submission.GeoChartCurve
import Submission.RayJacobiTensor
import Submission.ChartIndep
import Submission.CoeffSmooth
import Submission.CoeffSmooth2
import Submission.IndexMin
import Submission.IndexIntrinsic
import Submission.IndexIntrinsic2
import Submission.IndexIntrinsic3
import Submission.JacobiSystemInit
import Submission.SecondVarGeo
import Submission.EnergyBound
import Submission.JacobiBump
import Submission.GExpPieceData
import Submission.JacobiCover
import Submission.JacobiCoords
import Submission.JacobiAtSystem
import Submission.ChartCoordsTrans
import Submission.JacobiGlobal
import Submission.BumpField
import Submission.SecondVarGlobal
import Submission.IntrinsicVariation
import Submission.JacobiCoordsEq
import Submission.IndexFTC
import Submission.SmoothFieldCover
import Submission.IndexScale
import Submission.EnergyCover
import Submission.EnergyPhase
import Submission.EnergyRay
import Submission.EnergyRayCover
import Submission.EnergyRayGlobal
import Submission.EnergyRaySmooth
import Submission.IndexBackUnique
import Submission.ConjEnergy
import Submission.GeodesicLoop
import Submission.KlingenbergXu
import Submission.XuLift
import Submission.XuMain
import Submission.XuTrap
import Submission.XuReduction
import Submission.ParallelField
import Submission.ParallelGlobal
import Submission.EnergyShorten
import Submission.ParallelRoom
import Submission.ParallelShorten
import Submission.FundSol
import Submission.OrientSign
import Submission.HolDet
import Submission.HolSynge
import Submission.SyngeInput
import Submission.HolCover
import Submission.SyngeField
import Submission.EnergyGeo
import Submission.EnergyGeoCover
import Submission.EnergyGeoGlobal
import Submission.EnergyGeoSmooth
import Submission.EnergyGeoShorten
import Submission.SyngeShorten
import Submission.ParallelBridge
import Submission.SyngeFieldR
import Submission.SyngePackage
import Submission.CurveCover
import Submission.SyngeWindow
import Submission.LiftLemma
import Submission.LiftUniform
import Submission.LiftGlobal
import Submission.KlingenbergEven
import Submission.ChartStateTrans
import Submission.GExpJointPt
import Submission.KlingenbergAttain
import Submission.KlingenbergFit
import Submission.Work.Final.Sphere

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

theorem sphere_theorem [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) :
    Nonempty
      (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1) :=
  -- Klingenberg's diameter estimate `Submission.Klingenberg.KlingenbergBound cov` — the single
  -- classical input to which the whole theorem had been reduced (`Submission/Roadmap.lean` §67) —
  -- is now a theorem: `Work.Final.klingenbergBound_proved` (`Submission/Work/Final/Final.lean`).
  -- It is assembled from the two parity halves of Klingenberg's length bound for geodesic loops,
  -- `Work.EvenBound.diameter_gt_half_pi_even` (Synge's argument) and
  -- `Work.OddBound.diameter_gt_half_pi_odd_of_lt` (a finite-dimensional minimax over polygon
  -- space), via the uniform-curvature step `Work.CurvBound.exists_uniform_curvature_bound` and
  -- the one-dimensional degeneracy `Work.Final.false_of_finrank_one`; the parity split is
  -- `Submission.KlingenbergAssembly.closed_bound_of_parity`.  With it, the theorem is
  -- `Submission.Klingenberg.sphere_theorem_of_klingenberg`.
  Work.Final.sphere_theorem_proved hdim cov htor hmet hpinch

end Submission
