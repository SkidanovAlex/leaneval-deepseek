import ChallengeDeps
import Submission.NBody.SmallN
import Submission.NBody.MarchalFinal
import Submission.NBody.PairKernel
import Submission.NBody.Potential
import Submission.NBody.Force
import Submission.NBody.Shift
import Submission.NBody.Energy
import Submission.NBody.Asymptotic
import Submission.NBody.Virial
import Submission.NBody.Jacobi
import Submission.NBody.Flow
import Submission.NBody.EnergyAsymptotic
import Submission.NBody.LocalExistence
import Submission.NBody.Continuation
import Submission.NBody.Bridge
import Submission.NBody.Scaling
import Submission.NBody.Extension
import Submission.NBody.ForceDecay
import Submission.NBody.Chazy
import Submission.NBody.ChazyTube
import Submission.NBody.Action
import Submission.NBody.MassNorm
import Submission.NBody.Tonelli
import Submission.NBody.Minimizer
import Submission.NBody.EulerLagrange
import Submission.NBody.FirstVariation
import Submission.NBody.WeakToStrong
import Submission.NBody.ActionTau
import Submission.NBody.Dominated
import Submission.NBody.Horofunction
import Submission.NBody.HolderEstimate
import Submission.NBody.Calibrating
import Submission.NBody.SameBallEstimate
import Submission.NBody.NonSuperhyperbolic
import Submission.NBody.LaxOleinik
import Submission.NBody.MadernaEstimate
import Submission.NBody.CalibratingCurve
import Submission.NBody.Assembly
import Submission.NBody.Marchal
import Submission.NBody.EnergyLevel
import Submission.NBody.ChazyShape
import Submission.NBody.ChazyContinuity
import Submission.NBody.MinimizerEndpoint
import Submission.NBody.LimitShape
import Submission.NBody.Approximation
import Submission.NBody.Identification
import Submission.NBody.CollisionFreeLimit
import Submission.NBody.ConeArgument
import Submission.NBody.LimitShapeNonzero
import Submission.NBody.FinalAssembly
import Submission.NBody.LYZGeometry
import Submission.NBody.LYZCone
import Submission.NBody.LYZLength
import Submission.NBody.LYZPsi
import Submission.NBody.LYZIntegral
import Submission.NBody.LYZBound
import Submission.NBody.LYZObs
import Submission.NBody.LYZSetup
import Submission.NBody.LYZObsApply
import Submission.NBody.LYZSub
import Submission.NBody.LYZPhaseA
import Submission.NBody.LYZNoColl
import Submission.NBody.LYZPhaseB
import Submission.NBody.LYZUnif
import Submission.NBody.LYZEnergy
import Submission.NBody.LYZIoc
import Submission.NBody.EnergyAe
import Submission.NBody.SpernerBound
import Submission.NBody.MarchalCluster
import Submission.NBody.MarchalLagrangeJacobi
import Submission.NBody.MarchalForce
import Submission.NBody.MarchalSundman
import Submission.NBody.MarchalSundmanApply
import Submission.NBody.MarchalSperner
import Submission.NBody.MarchalRelEnergy
import Submission.NBody.MarchalClusterPlumbing
import Submission.NBody.MarchalClusterAsymptotic
import Submission.NBody.MarchalClusterBound
import Submission.NBody.MarchalClusterAccel
import Submission.NBody.MarchalClusterMomentum
import Submission.NBody.MarchalClusterFull
import Submission.NBody.MarchalThirdDeriv
import Submission.NBody.MarchalThirdDeriv2
import Submission.NBody.MarchalThirdDerivAsymptotic
import Submission.NBody.MarchalClusterAsymptotic2
import Submission.NBody.MarchalClusterAsymptotic3
import Submission.NBody.MarchalClusterShape
import Submission.NBody.MarchalClusterShapeIdentity
import Submission.NBody.MarchalClusterShapeLimit
import Submission.NBody.MarchalClusterInertiaBound
import Submission.NBody.MarchalClusterShapeSecondDeriv
import Submission.NBody.MarchalJoltBound
import Submission.NBody.MarchalClusterShapeThirdDeriv
import Submission.NBody.MarchalClusterCoord
import Submission.NBody.MarchalClusterShapeAsymptotic
import Submission.NBody.ClusterCentralConfig
import Submission.NBody.ClusterGradSplit
import Submission.NBody.ClusterShapePotential
import Submission.NBody.MarchalClusterForceRest
import Submission.NBody.MarchalClusterCentConf
import Submission.NBody.MarchalClusterSrcBlowup
import Submission.NBody.MarchalClusterBlowUp
import Submission.NBody.MarchalClusterBlowUpDeriv
import Submission.NBody.MarchalClusterBlowUpPotential
import Submission.NBody.MarchalStandardVariation
import Submission.NBody.MarchalPairRatio
import Submission.NBody.MarchalDerivBound
import Submission.NBody.MarchalBump
import Submission.NBody.MarchalBumpEstimates
import Submission.NBody.MarchalBumpPotential
import Submission.NBody.MarchalBumpSign
import Submission.NBody.MarchalBumpGeometric
import Submission.NBody.MarchalBumpTransfer
import Submission.NBody.MarchalBumpRest
import Submission.NBody.MarchalBumpIntegrable
import Submission.NBody.MarchalBumpKinetic
import Submission.NBody.MarchalBumpAssembly
import Submission.NBody.MarchalBumpTwoSided
import Submission.NBody.MarchalBumpScalar
import Submission.NBody.MarchalBumpAction
import Submission.NBody.MarchalOutsideVelocity
import Submission.NBody.MarchalGeometricData
import Submission.NBody.MarchalBumpF5
import Submission.NBody.MarchalCircleAvg
import Submission.NBody.MarchalCircleTransfer
import Submission.NBody.MarchalTransferLimit
import Submission.NBody.MarchalTransferData
import Submission.NBody.MarchalModelKinetic
import Submission.NBody.MarchalModelNegative
import Submission.NBody.MarchalModelPotential
import Submission.NBody.MarchalModelInstantiate
import Submission.NBody.MarchalStdVarGeometry
import Submission.NBody.MarchalModelSplit
import Submission.NBody.MarchalModelTwoSided
import Submission.NBody.MarchalGoodDirection
import Submission.NBody.MarchalModelTwoSidedApply
import Submission.NBody.MarchalBumpedCollision
import Submission.NBody.MarchalSeqShape
import Submission.NBody.MarchalSeqBlowUp
import Submission.NBody.MarchalSeqDeriv
import Submission.NBody.MarchalSeqData
import Submission.NBody.MarchalSeqTransfer
import Submission.NBody.MarchalSeqWindow
import Submission.NBody.MarchalSeqLeft
import Submission.NBody.MarchalCollClass
import Submission.NBody.MarchalMultiInertia
import Submission.NBody.MarchalSundmanGeneral
import Submission.NBody.MarchalMultiOstrogradsky
import Submission.NBody.MarchalMultiEnergy
import Submission.NBody.MarchalMultiJolt
import Submission.NBody.MarchalMultiEnergyBound
import Submission.NBody.MarchalMultiBound
import Submission.NBody.MarchalCollPartition
import Submission.NBody.MarchalLocMinExistence
import Submission.NBody.MarchalLocMinIsolated
import Submission.NBody.MarchalCollisionSolutionData
import Submission.NBody.MarchalMultiKineticBound
import Submission.NBody.MarchalMultiOutsideKinetic
import Submission.NBody.MarchalMultiSetup
import Submission.NBody.MarchalSolutionThirdDeriv
import Submission.NBody.MarchalKineticBoundAtCollision
import Submission.NBody.MarchalIsolatedCollision
import Submission.NBody.MarchalIsolatedOfLocalMin
import Submission.NBody.MarchalEnergyBoundAtCollision
import Submission.NBody.MarchalMultiEnergyBoundAtCollision
import Submission.NBody.MarchalMultiIsolated
import Submission.NBody.MarchalReflectMinimizer
import Submission.NBody.MarchalIsolatedClass
import Submission.NBody.MarchalIsolatedMulti
import Submission.NBody.MarchalSeqShapeUniform
import Submission.NBody.MarchalEndgameData
import Submission.NBody.MarchalShapeNondegenerate
import Submission.NBody.MarchalEnergyLowerBound
import Submission.NBody.MarchalClassAsymptotic
import Submission.NBody.MarchalSelfScaledVelocity
import Submission.NBody.MarchalCollisionAsymptotics
import Submission.NBody.LYZRatio
import Submission.NBody.LYZLimit
import Submission.NBody.LYZAssembly

open ViscositySolutions
open Filter Gradient Real Set

set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}
local notation "ℝᴺ" => Fin N → ℝ
local notation "Eᴺ" => EuclideanSpace E (Fin N)

namespace Submission

/-
# Theorem 1.1 of Maderna--Venturelli, *Viscosity solutions and hyperbolic motions*,
Annals of Math. 192 (2020).

For the Newtonian `N`-body problem in a Euclidean space `E` of dimension at least two there
are hyperbolic motions `x : ℝ → Eᴺ` with `x(t) = √(2h) · t · a + o(t)` as `t → +∞`, for any
initial configuration `x₀ = x(0)`, any collision-free asymptotic configuration `a` with
`‖a‖_[m] = 1` and any energy constant `h > 0`.  Moreover `x` is a genuine solution of
Newton's equations for every `t > 0` and never suffers collisions there.

## Current formalisation status

The statement is quantified over every `N : ℕ`.  The proof below splits on `N`.

* `N ≤ 1` (`Submission.NBody.theorem_1_1_of_le_one`, fully proved in
  `Submission/NBody/SmallN.lean` and `.../FreeMotion.lean`):
  - `N = 0`: the hypothesis `‖a‖_[m] = 1` contradicts `‖a‖_[m] = 0` (empty sum);
  - `N = 1`: `U m = 0`, so the straight free trajectory `t ↦ x₀ + √(2h) t • a` is a solution,
    with `o t := x₀`.

* `2 ≤ N`: the deep existence theorem of the paper, formalised along the route of
  Liu--Yan--Zhou (arXiv:2112.07450) in `Submission/NBody/LYZ*.lean`.  The whole variational
  construction -- the dyadic length estimates (`LYZUnif`), the ratio and shape estimates
  (`LYZRatio`), the limiting curve (`LYZLimit`) and their assembly (`LYZAssembly`,
  `theorem_1_1_of_marchal`) -- is now *proved*, and Theorem 1.1 is reduced to the single deep
  input **Marchal's theorem** (`NBody.MarchalProperty`, an action-minimising trajectory of the
  Newtonian `N`-body problem has no interior collision; Marchal 2002, Chenciner, Ferrario--
  Terracini).  Marchal's theorem is proved in `Submission/NBody/MarchalFinal.lean`
  (`NBody.marchal_property`), by the isolated-collision endgame of `MarchalEndgameFinal`.
-/
theorem theorem_1_1 (hE : 2 ≤ Module.finrank ℝ E) (m : ℝᴺ) (hm : ∀ i, 0 < m i)
    (x₀ a : Eᴺ) (a_nc : WithoutCollisions a) (a_norm : ‖a‖_[m] = 1) (h : ℝ) (h_pos : h > 0) :
    ∃ x : ℝ → Eᴺ, ∃ o : ℝ → Eᴺ, (o =o[atTop] fun t ↦ t) ∧ x 0 = x₀ ∧
      IsNBodySolution m x ∧ (∀ t > 0, WithoutCollisions (x t)) ∧
        ∀ t ≥ 0, x t = (sqrt (2 * h) * t) • a + o t := by
  by_cases hN : N ≤ 1
  · exact NBody.theorem_1_1_of_le_one hE hN m hm x₀ a a_nc a_norm h h_pos
  · -- `2 ≤ N`: everything except Marchal's theorem is proved in `Submission/NBody/LYZAssembly`.
    haveI : Nontrivial E :=
      Module.finrank_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hE)
    have hM : NBody.MarchalProperty (E := E) m h := by
      -- Marchal's theorem: an action-minimising trajectory has no interior collision.
      letI : MeasurableSpace E := borel E
      haveI : BorelSpace E := ⟨rfl⟩
      exact NBody.marchal_property hE m hm h_pos
    exact NBody.theorem_1_1_of_marchal hE (by omega : 2 ≤ N) m hm x₀ a a_nc a_norm h h_pos hM

end Submission
