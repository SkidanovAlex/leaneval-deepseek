/-
# The corrected rigidity theorems, assembled from the single-function statements

`Work.Rigidity.SingleRigidityP k ε c` is CKMRV's `lem:noPsolutions` stated for functions of
moderate growth (`f ∈ 𝒫 = Work.Kernels.InP`); the four instances at `k = 4, 12` and
`ε = ±1` are the actual content of the lemma.  Here the eigenfunction reduction
(`Work.Rigidity.homogeneousRigidityP_of_singleRigidityP`) turns them into the corrected
two-variable statements.

See `Submission/Work/Rigidity/Counterexample.lean` for why the `InP`-free variants
`Work.Rigidity.SingleRigidity` — and hence the target statements
`Work.FE.HomogeneousRigidity 8 0` and `Work.FE.HomogeneousRigidity 24 1` — are false.
-/
import Submission.Work.Rigidity.ModerateGrowth
import Submission.Work.Rigidity.AnnPlusWeightFourP
import Submission.Work.Rigidity.AnnMinusWeightFourP
import Submission.Work.Rigidity.AnnPlusWeightTwelveP
import Submission.Work.Rigidity.AnnMinusWeightTwelveP

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

/-- **The corrected `E₈` rigidity.**  `HomogeneousRigidityP 8 0`: a solution of the
homogeneous system with `g(τ,·), g̃(τ,·)` of moderate growth in `τ` and decay `o(1)` in the
strip is zero.  This is the paper's Section 8 uniqueness lemma at `d = 8, n₀ = 1`, with the
moderate-growth hypothesis that `Work.FE.HomogeneousRigidity` omits. -/
theorem homogeneousRigidityP_eight :
    HomogeneousRigidityP 8 0 :=
  homogeneousRigidityP_eight_of AnnPlusWeightFourP AnnMinusWeightFourP

/-- **The corrected Leech rigidity.**  `HomogeneousRigidityP 24 1`: a solution of the
homogeneous system with `g(τ,·), g̃(τ,·)` of moderate growth in `τ` and decay
`o(e^{-2π Im τ})` in the strip is zero.  This is the paper's Section 8 uniqueness lemma at
`d = 24, n₀ = 2`, with the moderate-growth hypothesis. -/
theorem homogeneousRigidityP_twentyfour :
    HomogeneousRigidityP 24 1 :=
  homogeneousRigidityP_twentyfour_of AnnPlusWeightTwelveP AnnMinusWeightTwelveP

end Work.Rigidity
