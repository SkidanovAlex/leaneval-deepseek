import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Ramification
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

set_option linter.style.haveILetI false in
theorem orderOf_residueFrobenius {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    orderOf (Work.LocalFields.residueFrobenius v w) =
      Module.finrank (NumberField.RingOfIntegers K ⧸ v.asIdeal)
        (NumberField.RingOfIntegers L ⧸ w.asIdeal) := by
  letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Field (NumberField.RingOfIntegers L ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic _ _

end Work.LocalFields
