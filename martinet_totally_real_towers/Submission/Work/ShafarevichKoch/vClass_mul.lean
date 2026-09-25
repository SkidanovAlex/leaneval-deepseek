import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ShafarevichKoch.SquareRoot

/-!
# `Work.ShafarevichKoch.vClass_mul`

`vClass` is multiplicative: the Kummer two-descent class
`vClass F x ∈ Cl(𝓞 F)` (the ideal class of a square root of the principal ideal `(x)`, for
`x ∈ V_∅ = VTwo F`) satisfies `vClass F (x * y) = vClass F x * vClass F y`.

The argument is the uniqueness of square roots in the group of fractional ideals
(`Work.ShafarevichKoch.squareRoot_unique`): the product of the chosen square roots of `(x)` and
`(y)` is a square root of `(x) * (y) = (x * y)`, hence it *is* the chosen square root of `(x * y)`,
and `ClassGroup.mk F` is a monoid homomorphism.
-/

namespace Work.ShafarevichKoch

theorem vClass_mul (F : Type*) [Field F] [NumberField F] (x y : Work.ShafarevichKoch.VTwo F) :
    Work.ShafarevichKoch.vClass F (x * y)
      = Work.ShafarevichKoch.vClass F x * Work.ShafarevichKoch.vClass F y := by
  -- the underlying unit of `x * y` is the product of the underlying units
  have hco : ((x * y : VTwo F) : Fˣ) = (x : Fˣ) * (y : Fˣ) := rfl
  -- the product of the chosen square roots is the chosen square root of `(x * y)`
  have hchoose : Classical.choose ((x * y).property :
        IsSquareFracIdeal F (FracIdealOf F ((x * y : VTwo F) : Fˣ)))
      = Classical.choose (x.property : IsSquareFracIdeal F (FracIdealOf F (x : Fˣ)))
        * Classical.choose (y.property : IsSquareFracIdeal F (FracIdealOf F (y : Fˣ))) := by
    apply squareRoot_unique F
    rw [vClass_spec F (x * y), hco, FracIdealOf_mul, mul_mul_mul_comm,
      vClass_spec F x, vClass_spec F y]
  rw [vClass, vClass, vClass, hchoose]
  exact map_mul (ClassGroup.mk F) _ _

end Work.ShafarevichKoch
