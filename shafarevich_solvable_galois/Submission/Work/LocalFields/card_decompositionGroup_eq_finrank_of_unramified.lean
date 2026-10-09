import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.Ramification
import Submission.Work.LocalFields.card_decompositionGroup
import Submission.Work.LocalFields.unramifiedAt_iff_inertia_eq_bot
import Submission.Work.LocalFields.orderOf_residueFrobenius
import Submission.Work.LocalFields.isUnramifiedAt_iff_ramificationIdxIn_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField

/-- **The decomposition group of an unramified prime has order the inertia degree.**

For a finite Galois extension `L/K` of number fields and a finite prime `w` of `L` lying over the
finite prime `v` of `K`, if `w` is unramified over `K` then the decomposition group `D_w ≤ Gal(L/K)`
has cardinality equal to the degree of the residue field extension
`f(w/v) = [κ_w : κ_v] = [𝓞 L ⧸ w : 𝓞 K ⧸ v]`.

Indeed `#D_w = e(w/v) · f(w/v)` (`Work.LocalFields.card_decompositionGroup`), while
unramifiedness says precisely `e(w/v) = 1`
(`Work.LocalFields.isUnramifiedAt_iff_ramificationIdxIn_eq_one`); the inertia degree
`f(w/v) = v.asIdeal.inertiaDegIn (𝓞 L)` is the `𝓞 K`-inertia degree of `w`, which by
`Ideal.inertiaDegIn_eq_inertiaDeg` is `w.asIdeal.inertiaDeg (𝓞 K)` and hence, `w` being maximal,
the `𝓞 K ⧸ v`-dimension of `𝓞 L ⧸ w` (`Ideal.inertiaDeg_eq_of_isMaximal`). -/
theorem card_decompositionGroup_eq_finrank_of_unramified {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] (hunr : Work.LocalFields.IsUnramifiedAt K w) :
    Nat.card (Work.LocalFields.decompositionGroup K w) =
      Module.finrank (NumberField.RingOfIntegers K ⧸ v.asIdeal)
        (NumberField.RingOfIntegers L ⧸ w.asIdeal) := by
  -- `#D_w = e(w/v) · f(w/v)`.
  have hcard := card_decompositionGroup v w
  -- Unramifiedness is exactly `e(w/v) = 1`.
  rw [isUnramifiedAt_iff_ramificationIdxIn_eq_one v w] at hunr
  rw [hcard, hunr, one_mul]
  -- Identify the inertia degree with the dimension of the residue field extension.
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal Gal(L/K)]
  exact Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal

end Work.LocalFields
