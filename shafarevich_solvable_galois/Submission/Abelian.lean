import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.SimpleRing.Principal
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
