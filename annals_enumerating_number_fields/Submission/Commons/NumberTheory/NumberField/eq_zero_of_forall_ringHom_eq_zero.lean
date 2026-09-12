import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.NumberField

/-- A nonzero element of a number field is not killed by all its embeddings into an algebraically
closed field of characteristic zero. -/
theorem eq_zero_of_forall_ringHom_eq_zero (K : Type*) [Field K] [NumberField K]
    (A : Type*) [Field A] [CharZero A] [IsAlgClosed A] (a : K)
    (h : ∀ φ : K →+* A, φ a = 0) : a = 0 := by
  -- The number field `K` is (finite-dimensional, hence) algebraic over `ℚ`, so by the extension
  -- lemma for algebraically closed fields there is a `ℚ`-algebra embedding `K → A`.
  let φ : K →ₐ[ℚ] A := IsAlgClosed.lift
  -- Any ring hom from a field into a domain is injective, so `φ a = 0` forces `a = 0`.
  exact φ.toRingHom.injective (by simpa using h φ.toRingHom)

end Commons.NumberTheory.NumberField