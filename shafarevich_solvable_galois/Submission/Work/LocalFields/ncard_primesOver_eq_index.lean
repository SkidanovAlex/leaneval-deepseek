import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.card_decompositionGroup_mul_ncard
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField

/-- The number of primes of `𝓞 L` lying over a finite prime `v` of `K` equals the index of the
decomposition group `D_w` in `Gal(L/K)`.

Indeed the Galois group acts transitively on the primes over `v`, so orbit–stabilizer gives
`|D_w| * #(primes over v) = |Gal(L/K)|`, while the subgroup index satisfies
`|D_w| * [Gal(L/K) : D_w] = |Gal(L/K)|`; cancelling the (nonzero) order of `D_w` yields the
claim. -/
theorem ncard_primesOver_eq_index {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    (v.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard =
      (Work.LocalFields.decompositionGroup K w).index := by
  have hcard := card_decompositionGroup_mul_ncard v w
  have hidx := Subgroup.card_mul_index (Work.LocalFields.decompositionGroup K w)
  have hpos : 0 < Nat.card (Work.LocalFields.decompositionGroup K w) := Nat.card_pos
  exact Nat.mul_left_cancel hpos (hcard.trans hidx.symm)

end Work.LocalFields
