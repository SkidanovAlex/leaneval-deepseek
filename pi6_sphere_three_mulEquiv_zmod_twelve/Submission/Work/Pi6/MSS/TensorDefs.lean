import Mathlib
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.Singular
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The tensor complex `K ⊗ M` with coefficients in a module

`Work.Pi6.MSS.tensorC 𝕜 K M` is the chain complex with `n`-th term `K_n ⊗ M` and differential
`d ⊗ id`, i.e. the complex `K` tensored with the complex concentrated in degree `0` at `M`.  It is
the target of the coefficient form of the `E¹` theorem: `E¹_{*,q} ≅ N_*(B;𝕜) ⊗ H_q(F;𝕜)`.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

noncomputable section

/-- The chain complex `K ⊗ M` (tensor product with the complex concentrated in degree `0`). -/
def tensorC (𝕜 : Type) [CommRing 𝕜] (K : ChainComplex (ModuleCat 𝕜) ℕ) (M : ModuleCat 𝕜) :
    ChainComplex (ModuleCat 𝕜) ℕ :=
  K ⊗ (HomologicalComplex.single (ModuleCat 𝕜) (ComplexShape.down ℕ) 0).obj M

/-- The normalized chain complex of the singular simplices of `B` with coefficients in `𝕜`. -/
abbrev normC (𝕜 : Type) [CommRing 𝕜] (B : Type) [TopologicalSpace B] :
    ChainComplex (ModuleCat 𝕜) ℕ :=
  (TopCat.toSSet.obj (TopCat.of B)).normalizedChainComplex (ModuleCat.of 𝕜 𝕜)

end

end Work.Pi6.MSS
