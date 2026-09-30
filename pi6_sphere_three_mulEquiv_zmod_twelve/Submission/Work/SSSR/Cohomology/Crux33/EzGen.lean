import Mathlib
import Submission.Work.SSSR.Cohomology.Crux33.ShuffleIndex
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial
namespace Work.SSSR.Cohomology.Crux33

noncomputable section

/-- **The Eilenberg–Zilber shuffle chain** of a `p`-simplex `σ` of `X` and a `q`-simplex `τ` of
`Y`, as an element of the `(p+q)`-chains of the tensor product `X ⊗ Y` of simplicial sets. -/
def ezGen (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    ((X ⊗ Y).chainComplex (ModuleCat.of R R)).X (p + q) :=
  ∑ S : PShuffle p q, shufSign S.1 • ((X ⊗ Y).ιChainComplex (R := ModuleCat.of R R)
    (X.map (aHom S.1 S.2).op σ, Y.map (bHom S.1 S.2).op τ)).hom 1

end

end Work.SSSR.Cohomology.Crux33
