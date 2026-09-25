import Mathlib.Data.Finsupp.Encodable
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.IsSepClosed

open Polynomial

/-- Polynomials over a countable semiring form a countable type.

`Polynomial R` is (definitionally) a one-field structure around
`AddMonoidAlgebra R ℕ`, whose coefficients form the finsupp `ℕ →₀ R`.  Both
structure projections are injective, and `ℕ →₀ R` is countable when `R` is. -/
theorem countable_polynomial {k : Type*} [Semiring k] [Countable k] : Countable k[X] :=
  (AddMonoidAlgebra.coeff_injective.comp (Polynomial.toFinsupp_injective (R := k))).countable

/-- The separable closure of a countable field is countable.

Since `E` is a separable (hence algebraic) extension of `k`, every `x : E` is a
root of some nonzero polynomial `p : k[X]`.  There are only countably many such
polynomials, and each has finitely many roots (`Polynomial.rootSet_finite`), so
`E` is a countable union of finite sets. -/
theorem countable_of_isSepClosure {k E : Type*} [Field k] [Field E] [Algebra k E]
    [IsSepClosure k E] [Countable k] : Countable E := by
  have hc : Countable k[X] := countable_polynomial
  have halg : Algebra.IsAlgebraic k E := inferInstance
  -- Every element of `E` is a root of a nonzero polynomial over `k`.
  have hcover : (Set.univ : Set E) ⊆
      ⋃ (p : {p : k[X] // p ≠ 0}), (p.1.rootSet E) := by
    intro x _
    simp only [Set.mem_iUnion]
    obtain ⟨p, hp, hp0⟩ := (Algebra.isAlgebraic_def.mp halg x)
    exact ⟨⟨p, hp⟩, (Polynomial.mem_rootSet_of_ne (S := E) hp).2 hp0⟩
  -- Each `rootSet` is finite, and the index type is countable.
  have hunion : (⋃ (p : {p : k[X] // p ≠ 0}), (p.1.rootSet E)).Countable :=
    Set.countable_iUnion fun p => (Polynomial.rootSet_finite p.1 E).countable
  exact Set.countable_univ_iff.mp (hunion.mono hcover)

end Commons.FieldTheory.IsSepClosed