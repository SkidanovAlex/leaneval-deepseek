import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField

set_option linter.style.haveILetI false

/-- **The cardinality of the decomposition group.**

For a finite Galois extension `L/K` of number fields and a finite prime `w` of `L` lying over
the finite prime `v` of `K`, the decomposition group `D_w ≤ Gal(L/K)` (the stabilizer of `w`)
has cardinality `e(w/v) · f(w/v)`, the product of the ramification index and the inertia degree
of `w` over `v`.

This is the number-field instance of Mathlib's `Ideal.card_stabilizer_eq` for Galois extensions
of Dedekind domains: the stabilizer of a prime `P` over `p` has cardinality
`p.ramificationIdxIn S * p.inertiaDegIn S`. -/
theorem card_decompositionGroup {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    Nat.card (Work.LocalFields.decompositionGroup K w) =
      v.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L)
        * v.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) := by
  -- `𝓞 L` is a finite `𝓞 K`-module (the integral closure of the Noetherian, integrally closed
  -- domain `𝓞 K` in the finite separable field extension `L/K`).
  haveI : Module.Finite (𝓞 K) (𝓞 L) :=
    IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  -- The decomposition group is by definition the stabilizer of `w`; `Gal(L/K)` acts on `𝓞 L`
  -- making `𝓞 L / 𝓞 K` a Galois extension of Dedekind domains, so the fundamental identity
  -- `Ideal.card_stabilizer_eq` applies.
  exact Ideal.card_stabilizer_eq (R := 𝓞 K) (S := 𝓞 L) (G := Gal(L/K)) v.asIdeal w.asIdeal

end Work.LocalFields
