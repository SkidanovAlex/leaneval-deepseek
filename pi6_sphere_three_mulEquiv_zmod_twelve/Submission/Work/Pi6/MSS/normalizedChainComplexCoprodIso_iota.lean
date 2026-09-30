import Mathlib
import Submission.Work.SSSR.serreE1CoefIso
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

theorem normalizedChainComplexCoprodIso_iota {R : Type} [CommRing R] [Nontrivial R]
    (X : SSet.{0}) (M : ModuleCat R) (d : ℕ) (x : X.nonDegenerate d) :
    CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.Sigma.ι (fun _ : X.nonDegenerate d => M) x)
        ((Work.SSSR.normalizedChainComplexCoprodIso X M d).hom)
      = X.ιNormalizedChainComplex (R := M) x.val := by
  rw [Work.SSSR.normalizedChainComplexCoprodIso]
  exact CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
    (P := CategoryTheory.Limits.coproductIsCoproduct (fun _ : X.nonDegenerate d => M))
    (Q := X.isColimitCofanNormalizedChainComplex M d) (CategoryTheory.Discrete.mk x)

end Work.Pi6.MSS
