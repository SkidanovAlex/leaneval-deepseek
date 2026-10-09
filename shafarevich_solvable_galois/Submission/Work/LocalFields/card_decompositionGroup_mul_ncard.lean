import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Pointwise

/-- **Orbit–stabilizer for the decomposition group.** In a finite Galois extension `L/K` of
number fields, the decomposition group of a prime `w` of `L` lying over `v` is the stabilizer of
`w.asIdeal` under the action of `Gal(L/K)` on the prime ideals of `𝓞 L` lying over `v`. Since this
action is transitive on `v.asIdeal.primesOver (𝓞 L)`, the orbit–stabilizer theorem gives
`|D_w| * #(primes over v) = |Gal(L/K)|`. -/
theorem card_decompositionGroup_mul_ncard {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    Nat.card (Work.LocalFields.decompositionGroup K w)
        * (v.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard
      = Nat.card Gal(L/K) := by
  -- The Galois group acts transitively on the primes of `𝓞 L` lying over `v`.
  have horbit : MulAction.orbit Gal(L/K) w.asIdeal
      = v.asIdeal.primesOver (NumberField.RingOfIntegers L) :=
    Algebra.IsInvariant.orbit_eq_primesOver (𝓞 K) (𝓞 L) Gal(L/K) v.asIdeal w.asIdeal
  -- `decompositionGroup` is by definition the stabilizer, so the orbit–stabilizer theorem applies.
  rw [show Work.LocalFields.decompositionGroup K w
        = MulAction.stabilizer Gal(L/K) w.asIdeal from rfl,
      ← Subgroup.card_mul_index (MulAction.stabilizer Gal(L/K) w.asIdeal),
      MulAction.index_stabilizer, horbit]

end Work.LocalFields
