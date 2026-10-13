import Mathlib
import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.rootClosure_flat
import Submission.Work.DSM2p.rootClosure_isSMulRegular
import Submission.Work.DSM2p.CSIntegralClosurePos_isSMulRegular

namespace Work.DSM2p

/-- **`p`-torsion-freeness of the one-polynomial `p`-integral closure `A'_F`.**

The argument is identical to `CSIntegralClosure_isSMulRegular` /
`CSIntegralClosurePos_isSMulRegular`: `A'_F = CSIntegralClosureOne A p ϖ F` is by definition a
subring of `Λ[1/ϖ] = Lam1Loc A p ϖ`, and `p` is a non-zero-divisor of the latter because
`Λ = Lam1 A p = rootClosure A p PUnit` is a flat `A`-algebra and localisation preserves
non-zero-divisors. -/
theorem CSIntegralClosureOne_isSMulRegular (A : Type*) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular ↥(CSIntegralClosureOne A p ϖ F) (p : ↥(CSIntegralClosureOne A p ϖ F)) := by
  -- `p` is a non-zero-divisor of `Λ = Lam1 A p`, which is a flat `A`-algebra.
  have hflat : Module.Flat A (Lam1 A p) := rootClosure_flat A p PUnit
  have hΛ : IsSMulRegular (Lam1 A p) (p : Lam1 A p) :=
    natCast_isSMulRegular_of_flat A (Lam1 A p) p hp
  -- localising at `ϖ` preserves non-zero-divisors
  have hLoc : IsSMulRegular (Lam1Loc A p ϖ) (p : Lam1Loc A p ϖ) :=
    natCast_isSMulRegular_of_isLocalization (Lam1 A p) (Lam1Loc A p ϖ)
      (Submonoid.powers (algebraMap A (Lam1 A p) ϖ)) p hΛ
  -- and so does passing to the subring `A'_F = CSIntegralClosureOne A p ϖ F`
  exact natCast_isSMulRegular_of_subring (Lam1Loc A p ϖ) (CSIntegralClosureOne A p ϖ F) p hLoc

end Work.DSM2p
