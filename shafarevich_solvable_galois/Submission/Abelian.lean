/-
Copyright (c) 2025. All rights reserved.

# Realizing finite abelian groups over `ℚ`

The abelian case of the inverse Galois problem over `ℚ`: every finite abelian group
occurs as the Galois group of a finite Galois extension of `ℚ`.

The construction is the classical one via cyclotomic fields:

* `ℚ(ζ_N)` has Galois group `(ZMod N)ˣ` over `ℚ`
  (`IsCyclotomicExtension.autEquivPow`),
* `(ZMod N)ˣ` is cyclic of order `N - 1` when `N` is prime, and by the Chinese
  remainder theorem `(ZMod N)ˣ` is the product of the `(ZMod p)ˣ` for `p` running
  over the primes dividing `N`,
* choosing distinct primes `p_i ≡ 1 mod n_i` (Dirichlet's theorem) makes every
  finite product `∏ Multiplicative (ZMod n_i)` a quotient of a suitable `(ZMod N)ˣ`,
* and any quotient of a realizable group is realizable, by taking a fixed field.

The group-theoretic input `exists_surjective_units_zmod` is proved in
`Submission/Work/GroupTheory/UnitsQuotient.lean`.
-/
import Mathlib
import Submission.Realization
import Submission.Work.GroupTheory.exists_surjective_units_zmod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

open scoped Classical

/-- The Galois group of the `N`-th cyclotomic field over `ℚ` is `(ZMod N)ˣ`; hence
`(ZMod N)ˣ` is realizable over `ℚ`. -/
theorem realizableOver_units_zmod (N : ℕ) [NeZero N] : RealizableOver ℚ (ZMod N)ˣ := by
  haveI : NeZero (N : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  refine ⟨CyclotomicField N ℚ, inferInstance, inferInstance, ?_, ?_, ⟨?_⟩⟩
  · exact IsCyclotomicExtension.finiteDimensional {N} ℚ (CyclotomicField N ℚ)
  · exact IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
  · exact (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N))).symm

/-- **The abelian case of the inverse Galois problem over `ℚ`.** Every finite abelian group is
realizable as a Galois group over `ℚ`. -/
theorem realizableOver_of_commGroup (G : Type*) [CommGroup G] [Finite G] : RealizableOver ℚ G := by
  obtain ⟨N, hN, f, hf⟩ := Work.GroupTheory.exists_surjective_units_zmod G
  haveI : NeZero N := ⟨hN⟩
  exact (realizableOver_units_zmod N).of_surjective f hf

/-- A finite abelian group that is a quotient of some `(ZMod N)ˣ` is realizable over `ℚ`. -/
theorem realizableOver_of_surjective_units_zmod {G : Type*} [Group G]
    (N : ℕ) [NeZero N] (f : (ZMod N)ˣ →* G) (hf : Function.Surjective f) :
    RealizableOver ℚ G :=
  (realizableOver_units_zmod N).of_surjective f hf

end Submission
