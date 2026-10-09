import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Ramification
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

theorem mk_frobenius_eq_frobeniusClass {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    QuotientGroup.mk (Work.LocalFields.frobenius v w) = Work.LocalFields.frobeniusClass v w := by
  rw [frobenius]
  exact Quotient.out_eq _

end Work.LocalFields
