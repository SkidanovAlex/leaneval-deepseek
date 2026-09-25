import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ShafarevichKoch.SquareRoot

namespace Work.ShafarevichKoch

/-- The Kummer two-descent class `vClass F x` of `x ∈ V_∅` is the ideal class of *any* square
root `J` of the principal fractional ideal `(x)`.  This is the well-definedness of the descent
map `V_∅/Fˣ² → Cl(F)[2]`: the chosen square root of `(x)` and any other differ by a unit of
`𝓞 F`, hence have the same ideal class. -/
theorem vClass_eq_mk (F : Type*) [Field F] [NumberField F] {x : Work.ShafarevichKoch.VTwo F}
    {J : Work.ShafarevichKoch.IdealUnit F}
    (hJ : J * J = Work.ShafarevichKoch.FracIdealOf F x.1) :
    Work.ShafarevichKoch.vClass F x = ClassGroup.mk F J := by
  unfold vClass
  have h : Classical.choose (x.property : IsSquareFracIdeal F (FracIdealOf F x.1))
      * Classical.choose (x.property : IsSquareFracIdeal F (FracIdealOf F x.1)) = J * J := by
    rw [vClass_spec F x, hJ]
  rw [squareRoot_unique F h]

end Work.ShafarevichKoch
