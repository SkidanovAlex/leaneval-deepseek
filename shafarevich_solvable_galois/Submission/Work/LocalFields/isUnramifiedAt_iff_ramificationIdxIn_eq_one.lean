import Mathlib.NumberTheory.RamificationInertia.Galois
import Submission.Work.LocalFields.card_inertiaSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField

/-- **Unramifiedness is triviality of the ramification index.**

For a finite Galois extension `L/K` of number fields and a finite prime `w` of `L` lying over the
finite prime `v` of `K`, `w` is unramified over `K` (equivalently, its inertia subgroup `I_w` is
trivial) if and only if the ramification index `e(w/v) = #I_w` equals `1`.

This is the combination of the cardinality computation `#I_w = e(w/v)`
(`Work.LocalFields.card_inertiaSubgroup`) with the elementary group-theoretic fact
`H = ⊥ ↔ Nat.card H = 1` for a subgroup `H`. -/
theorem isUnramifiedAt_iff_ramificationIdxIn_eq_one {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    Work.LocalFields.IsUnramifiedAt K w ↔
      v.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) = 1 := by
  rw [IsUnramifiedAt, Subgroup.eq_bot_iff_card, card_inertiaSubgroup v w]

end Work.LocalFields
