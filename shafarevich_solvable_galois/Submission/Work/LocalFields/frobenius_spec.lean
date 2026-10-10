import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.LocalFields.mk_frobenius_eq_frobeniusClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

/-- The Frobenius element `frobenius v w` of the decomposition group lifts the Frobenius of the
residue field extension: its image under the ramification exact sequence
`D_w ⧸ I_w ≃* Gal(κ_w/κ_v)` is the `#κ_v`-power map. -/
theorem frobenius_spec {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    Work.LocalFields.ramificationExactSequence v w
        (QuotientGroup.mk (Work.LocalFields.frobenius v w))
      = Work.LocalFields.residueFrobenius v w := by
  rw [mk_frobenius_eq_frobeniusClass, frobeniusClass]
  exact MulEquiv.apply_symm_apply _ _

end Work.LocalFields
