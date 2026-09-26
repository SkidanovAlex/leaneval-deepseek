/-
# The weight-four rigidity lemma at eigenvalue `+1`, with the moderate-growth hypothesis

Target: `Work.Rigidity.SingleRigidityP 4 (1 : ℂ) 0`, i.e. no nonzero `f ∈ 𝒫` annihilated by
`(T - I)²`, satisfying `f ∣[4] S = f` and decaying like `o(1)` along the strip
`-1 ≤ Re τ ≤ 1`.  This is CKMRV `lem:noPsolutions` at weight `4` (`d = 8`) in the `ε = +1`
(`𝓘₋`) case, with the paper's hypothesis `f ∈ 𝒫` made explicit.

## The argument

Let `u = fstDiff f = f(τ+1) - f τ` be the `T`-defect of `f` and `H = u ∣[4] S`, and put
`K = H + u/2` and `I = u² + uH + H² = K² + (3/4)u²` (see `AnnMinusAux`).

* `u` is `1`-periodic, lies in `𝒫`, and `u → 0` at the cusp;
* the trace identity `u + H + H∣[4]T = 0` holds (`FstDiffTraceFour`), whence `H → 0` at the
  cusp (`SlashSTdefTendstoZeroInP`);
* `I` is `SL(2,ℤ)`-invariant of weight `8`, holomorphic and bounded at the cusp, and it
  vanishes at the cusp (`WeightEightVanishes`); since the level-one space `M₈` is spanned by
  `E₄²` and `E₄ → 1`, this forces `I = 0` (`WeightEightVanishes`);
* `I = 0` writes as `(u - ωH)(u - ω²H) = 0` with `ω` a primitive cube root of unity, so one
  factor vanishes identically (`MulEqZeroEqZero`); the trace identity then forces `u = 0`
  (`FinalAlgebra`);
* finally `u = 0` makes `f` `1`-periodic, hence a level-one modular form of weight `4`
  vanishing at the cusp; since `M₄ = ℂE₄` and `E₄ → 1`, `f = 0` (`Endgame`).
-/
import Mathlib
import Submission.Work.Rigidity.ModerateGrowth
import Submission.Work.Rigidity.Diff
import Submission.Work.Rigidity.AnnMinusAux
import Submission.Work.Rigidity.WeightEightVanishes
import Submission.Work.Rigidity.FinalAlgebra
import Submission.Work.Rigidity.Endgame

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix Filter
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

/-- **The weight-four rigidity lemma at eigenvalue `1` with the moderate-growth hypothesis.**
No nonzero `f ∈ 𝒫` annihilated by `(T - I)²`, `S`-invariant at weight `4`, decays like `o(1)`
along the strip `-1 ≤ Re τ ≤ 1`. -/
theorem AnnMinusWeightFourP : Work.Rigidity.SingleRigidityP 4 (1 : ℂ) 0 := by
  intro f hP hT2 hS hdec
  exact Endgame hP hT2 hS hdec (FinalAlgebra hP hT2 hS (WeightEightVanishes hP hT2 hS hdec))

end Work.Rigidity
