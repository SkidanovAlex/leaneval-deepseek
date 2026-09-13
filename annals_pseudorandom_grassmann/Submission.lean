import ChallengeDeps
import Submission.Helpers
import Submission.Grassmann.Structure
import Submission.Grassmann.Cardinality
import Submission.Grassmann.Expansion
import Submission.Grassmann.Counting
import Submission.Grassmann.Regularity
import Submission.Grassmann.GaussianBinomial
import Submission.Grassmann.Degree
import Submission.Grassmann.Scheme
import Submission.Grassmann.Fourier
import Submission.Grassmann.Spectrum
import Submission.Grassmann.Injective
import Submission.Grassmann.Duality
import Submission.Grassmann.Levels
import Submission.Grassmann.Transfer
import Submission.Grassmann.ExpansionBound
import Submission.Grassmann.LevelWeight
import Submission.Grassmann.LevelOne
import Submission.Grassmann.Assembly
import Submission.Grassmann.Hyperplane
import Submission.Grassmann.StructureDegree
import Submission.Grassmann.BilinearDegree
import Submission.Grassmann.Restriction
import Submission.Grassmann.Laplacian
import Submission.Grassmann.Dictator
import Submission.Grassmann.LevelDecomp
import Submission.Grassmann.HybridLaplacian
import Submission.Grassmann.DictatorDual
import Submission.Grassmann.XLaplacian
import Submission.Grassmann.EOp
import Submission.Grassmann.CombinatorialLaplacian
import Submission.Grassmann.Homogeneous
import Submission.Grassmann.TauOp
import Submission.Grassmann.Shortcode
import Submission.Grassmann.DualLaplacian
import Submission.Hypercube.Walsh
import Submission.Hypercube.Resample
import Submission.Hypercube.CondHyp
import Submission.Hypercube.Noise
import Submission.Hypercube.GlobalConv
import Submission.Grassmann.Influence
import Submission.Grassmann.InductiveStep
import Submission.Grassmann.RestrictionFourier
import Submission.Grassmann.LemLv
import Submission.Grassmann.InfluenceBound
import Submission.Grassmann.DerivativeComposition
import Submission.Grassmann.LemLvDual
import Submission.Grassmann.Prop56
import Submission.Grassmann.TransposeBS
import Submission.Grassmann.Prop56Main
import Submission.Grassmann.Concentration
import Submission.Grassmann.SpectralSSE
import Submission.Grassmann.SmallInfl
import Submission.Grassmann.HypBSglob
import Submission.Grassmann.ShiftAverage
import Submission.Grassmann.PairSum
import Submission.Grassmann.Hypercontractivity
import Submission.Grassmann.XNormSum
import Submission.Grassmann.Convolution
import Submission.Grassmann.FClassification
import Submission.Grassmann.BasicLaplacians
import Submission.Grassmann.F2Helper
import Submission.Grassmann.F2Helper2
import Submission.Grassmann.F2Helper3
import Submission.Grassmann.F1Helper
import Submission.Grassmann.HypInductiveStep
import Submission.Grassmann.HypHyperUC
import Submission.Grassmann.RestrictionTriple
import Submission.Grassmann.Coords
import Submission.Grassmann.RestrictProp
import Submission.Grassmann.BoundsComposition
import Submission.Grassmann.AfterRestricting
import Submission.Grassmann.SwitchingRoles
import Submission.Grassmann.DerivativeDegree
import Submission.Grassmann.D4Rewrite
import Submission.Grassmann.Transport
import Submission.Grassmann.DopXReform
import Submission.Grassmann.Reparam
import Submission.Grassmann.SwitchStep
import Submission.Grassmann.UpperBound
import Submission.Grassmann.Assembly2
import Submission.Grassmann.Assembly3
import Submission.Grassmann.Assembly4
import Submission.Grassmann.HybridLift
import Submission.Grassmann.RoleTransfer
import Submission.Grassmann.RestrictedCor
import Submission.Grassmann.SwCollapse
import Submission.Grassmann.SwRole
import Submission.Grassmann.FibreCount
import Submission.Grassmann.Reindex
import Submission.Grassmann.ReindexSum
import Submission.Grassmann.ReindexMain
import Submission.Grassmann.SwRoleUnfold
import Submission.Grassmann.ReindexFibre
import Submission.Grassmann.IHypStep
import Submission.Grassmann.BKSHom
import Submission.Grassmann.BKSNice
import Submission.Grassmann.BSAvg
import Submission.Grassmann.BSEnd

open PseudorandomGrassmann
open Module Finset Filter

set_option autoImplicit false
local notation "𝔽₂" => ZMod 2

namespace Submission

open Classical in
theorem theorem_1_12 (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    ∃ ε > 0, ∃ r, ∀ᶠ (ℓ : ℕ) (k : ℕ) in atTop, ∀ S : Finset (GrVertex k ℓ),
      (hS : S.Nonempty) → 2 * #S ≤ Fintype.card (GrVertex k ℓ) →
        Φ (Gr k ℓ) S hS ≤ α → ∃ (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)), A ≤ B ∧
          letI a := finrank 𝔽₂ A; letI b := k - finrank 𝔽₂ B
          a + b ≤ r ∧ #(S ∩ SubGr k ℓ A B) / #(SubGr k ℓ A B) ≥ (ε : ℝ) :=
  Submission.Grassmann.F2.theorem_1_12_of_main α hα (Submission.Grassmann.main_exp α hα)

end Submission
