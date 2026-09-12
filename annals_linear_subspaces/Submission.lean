import ChallengeDeps
import Submission.Helpers
import Submission.GeometryOfNumbers.SuccessiveMinima
import Submission.GeometryOfNumbers.MinkowskiFirst
import Submission.Work.Lattice.SlopeLambda
import Submission.Work.Extraction.Supply
import Submission.Work.Extraction.SupplyBound
import Submission.Work.Extraction.StageCount
import Submission.Work.Extraction.Constants
import Submission.Work.Extraction.AccountingFix
import Submission.Work.Extraction.Accumulate
import Submission.Work.Extraction.LambdaPred
import Submission.Work.Lattice.PolygonUniformBound
import Submission.Work.Extraction.Capacity
import Submission.Work.Extraction.LevelBound
import Submission.Work.Dani.OrthoRep
import Submission.Work.Dani.Part2
import Submission.Work.Dani.StarPairAssembly
import Submission.Work.Lattice.MaxNormFlow
import Submission.Work.Lattice.MaxNormPosition
import Submission.Work.Lattice.Prop5Block
import Submission.Work.Lattice.Prop5Assembly
import Submission.Work.Lattice.PositionRank
import Submission.Work.Lattice.FlowShrink
import Submission.Work.Lattice.GoodTime
import Submission.Work.Lattice.Accounting
import Submission.Work.Lattice.PolygonLipschitz
import Submission.Work.Lattice.RightDerivGlue
import Submission.Work.Lattice.FlowDataBound
import Submission.Work.Lattice.FlowDataBoundImage
import Submission.Work.Lattice.FlowDataMax
import Submission.Work.Lattice.FlowDataShift
import Submission.Work.Lattice.PrefixAccounting
import Submission.Work.Lattice.ConcaveMajorant
import Submission.Work.Lattice.PositionData
import Submission.Work.Lattice.FlowRateUniform
import Submission.Work.Lattice.AccountingOneSided
import Submission.Work.Lattice.CnormLevel
import Submission.Work.Lattice.CnormIntegral
import Submission.Work.Lattice.CnormDataBdd
import Submission.Work.Lattice.MaxNormPolygon
import Submission.Work.Lattice.MaxNormEndpoints
import Submission.Work.Lattice.MaxNormAccounting
import Submission.Work.Lattice.MaxEuclidData
import Submission.Work.Lattice.BatchExtraction
import Submission.Work.Lattice.MaxRankData
import Submission.Work.Lattice.MaxCovol
import Submission.Work.Lattice.MaxPhi
import Submission.Work.Lattice.MaxPhiPolygon
import Submission.Work.Lattice.MaxEuclidBridge
import Submission.Work.Lattice.MaxAttainment
import Submission.Work.Lattice.MaxPhiFlag
import Submission.Work.Lattice.Prop5Iteration
import Submission.Work.Lattice.ConcatWedge
import Submission.Work.Lattice.LevelDeriv
import Submission.Work.Lattice.ActiveBlock
import Submission.Work.Lattice.TangentCriterion
import Submission.Work.Lattice.FlowLatticeImage
import Submission.Work.Lattice.FlagMemberCriterion
import Submission.Work.Lattice.FlagInstantiation
import Submission.Work.Lattice.ActiveBlockEuclid
import Submission.Work.Lattice.MaxFlagMinima
import Submission.Work.Lattice.BatchAccumulation
import Submission.Work.Lattice.MaxPhiAccounting
import Submission.Work.Dani.LiftFamily
import Submission.Work.Lattice.SuccessiveMinimaBound
import Submission.Work.Dani.EscapeGlue
import Submission.Work.Dani.EscapeGlueEps
import Submission.Work.Dani.EscapeMetric
import Submission.Work.Dani.Conjunct2
import Submission.Work.Dani.ConeFromPlane
import Submission.Work.Dani.FlowToDirichlet
import Submission.Work.Dani.ApproxInterface
import Submission.Work.Extraction.Production

open LinearSubspaces
open ENNReal Real Module exteriorPower InnerProductGeometry
open scoped LinearAlgebra.Projectivization

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

namespace Submission

theorem theorem_1 (hd : 2 ≤ d) (l : ℕ) (hl0 : 0 < l) (hld : l < d) (k : ℕ) (hk1 : 1 ≤ k) (hkl : k ≤ l) :
    (∀ x : Submodule ℝ ℝᵈ, finrank ℝ x = l → diophantineExponent k x ≥ d / (k * (d - l))) ∧
    (∃ x : Submodule ℝ ℝᵈ, finrank ℝ x = l ∧ diophantineExponent k x = d / (k * (d - l))) := by
  refine Submission.ApproxInterface.theorem_1_of_flow_production (d := d) hd hl0 hld hk1 hkl
    (c₀ := Submission.Production.cK d l k)
    (C₀ := Submission.Production.C0K d l k (Submission.Production.Aconst d))
    (Submission.Production.cK_pos d l k hk1)
    (Submission.Production.C0K_pos d l k (Submission.Production.Aconst d)) ?_
  intro W hW T
  obtain ⟨t, htT, m, hmint, hmLI, hdom, hnorm⟩ :=
    Submission.ProductionAssembly.production (d := d) (ℓ := l) (k := k) hl0 hld hk1 hkl
      (Submission.DaniOrthoRep.orthRep (le_of_lt hld) W hW) T
  exact ⟨t, htT, m, hmint, hmLI, hdom, hnorm⟩

end Submission
