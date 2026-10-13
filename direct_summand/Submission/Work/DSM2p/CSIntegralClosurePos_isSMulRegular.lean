import Mathlib
import Submission.Work.DSM2p.ConstructionPos
import Submission.Work.DSM2p.CSIntegralClosure_isSMulRegular
import Submission.Work.DSM2p.rootClosure_flat

namespace Work.DSM2p

/-- **`p`-torsion-freeness of the positive-degree `p`-integral closure `A'`.**

The argument is identical to `CSIntegralClosure_isSMulRegular`: `A'` is by definition a subring of
`Λ[1/ϖ] = RootAlgLocPos A p ϖ`, and `p` is a non-zero-divisor of the latter because `Λ` is a flat
`A`-algebra and localisation preserves non-zero-divisors. -/
theorem CSIntegralClosurePos_isSMulRegular (A : Type*) [CommRing A] (p : ℕ) (ϖ : A)
    (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (CSIntegralClosurePos A p ϖ) (p : CSIntegralClosurePos A p ϖ) := by
  -- `p` is a non-zero-divisor of `Λ = RootAlgPos A p`, which is flat over `A`.
  have hflat : Module.Flat A (RootAlgPos A p) := rootClosure_flat A p (MonicPolysPos A)
  have hΛ : IsSMulRegular (RootAlgPos A p) (p : RootAlgPos A p) :=
    natCast_isSMulRegular_of_flat A (RootAlgPos A p) p hp
  -- localising at `ϖ` preserves non-zero-divisors
  have hLoc : IsSMulRegular (RootAlgLocPos A p ϖ) (p : RootAlgLocPos A p ϖ) :=
    natCast_isSMulRegular_of_isLocalization (RootAlgPos A p) (RootAlgLocPos A p ϖ)
      (Submonoid.powers (algebraMap A (RootAlgPos A p) ϖ)) p hΛ
  -- and so does passing to the subring `A' = CSIntegralClosurePos A p ϖ`
  exact natCast_isSMulRegular_of_subring (RootAlgLocPos A p ϖ) (CSIntegralClosurePos A p ϖ) p hLoc

end Work.DSM2p
