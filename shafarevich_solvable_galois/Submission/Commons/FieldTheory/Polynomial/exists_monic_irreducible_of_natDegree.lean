import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped Polynomial

namespace Commons.FieldTheory.Polynomial

/-- For every positive integer `n`, there exists a monic irreducible polynomial over a finite
field `F` whose degree is `n`. -/
theorem exists_monic_irreducible_of_natDegree {F : Type*} [Field F] [Fintype F]
    (n : ℕ) (hn : 1 ≤ n) : ∃ p : F[X], p.Monic ∧ Irreducible p ∧ p.natDegree = n := by
  classical
  let q := ringChar F
  haveI : Fact q.Prime := ⟨CharP.char_is_prime F q⟩
  haveI : NeZero n := ⟨by omega⟩
  -- Let E be a degree-`n` extension of the finite field `F`, pick a primitive element `α`,
  -- and take its minimal polynomial.
  let ⟨α, hprim⟩ := Field.exists_primitive_element_of_finite_bot F (FiniteField.Extension F q n)
  let hInt : IsIntegral F α := IsIntegral.of_finite F α
  refine ⟨minpoly F α, minpoly.monic hInt, minpoly.irreducible hInt, ?_⟩
  calc
    (minpoly F α).natDegree = Module.finrank F (FiniteField.Extension F q n) :=
      (Field.primitive_element_iff_minpoly_natDegree_eq F α).mp hprim
    _ = n := FiniteField.finrank_extension F q n

end Commons.FieldTheory.Polynomial