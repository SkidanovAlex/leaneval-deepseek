import Mathlib
import Submission.Work.QuadraticFields.gsM_isTotallyReal
import Submission.Work.QuadraticFields.CertificateReal

/-!
# The base field `gsF` of the certificate is totally real

The numerical certificate of `Submission/Work/QuadraticFields/CertificateReal.lean` uses the
**real** quadratic base field

  `F = gsF = ℚ(√(5·13·17·29·37·41·53)) ⊆ gsM = ℚ(√5, √13, √17, √29, √37, √41, √53)`,

and the hypothesis of the unramified-tower argument (`HilbertTowerWall`,
`GolodShafarevichArithmeticInput`) requires `F` to be totally real.

Total reality here is a *general* fact: **a subfield of a totally real field is totally real.**
If `K` is totally real, `F ≤ K` and `K` is algebraic over `F`, then for an infinite place `w`
of `F` there is an infinite place `W` of `K` with `W.comap (algebraMap F K) = w`
(`InfinitePlace.comap_surjective`), and `W` is real, so `w`, being the pullback of a real place
along a ring hom, is real.  Mathlib packages this as
`NumberField.IsTotallyReal.of_algebra` and the instance

  `instance [IsTotallyReal K] [CharZero K] (F : IntermediateField ℚ K) [Algebra.IsAlgebraic F K] :
      IsTotallyReal F`.

Since `gsM` is a number field (`[gsM : ℚ] = 2 ^ 7 = 128`), it is algebraic over `gsF`, so the
instance applies and completely disposes of the claim.  Nothing about the arithmetic of
`2576450045` is needed.

## Main results

* `Work.QuadraticFields.gsF_isTotallyReal`
-/

namespace Work.QuadraticFields

open NumberField

set_option autoImplicit false

noncomputable section

/-- **The quadratic base field `gsF` of the certificate is totally real.**

`gsF` is a subfield of `gsM`, which is totally real by
`Work.QuadraticFields.gsM_isTotallyReal`; a subfield of a totally real (algebraic) field is
totally real, which is Mathlib's `NumberField.IsTotallyReal.of_algebra` together with the
instance `IsTotallyReal F` for `F : IntermediateField ℚ K` with `K` totally real. -/
theorem gsF_isTotallyReal : NumberField.IsTotallyReal ↥gsF := by
  have hM : NumberField.IsTotallyReal gsM := gsM_isTotallyReal
  exact IsTotallyReal.of_algebra ↥gsF gsM

end

end Work.QuadraticFields
