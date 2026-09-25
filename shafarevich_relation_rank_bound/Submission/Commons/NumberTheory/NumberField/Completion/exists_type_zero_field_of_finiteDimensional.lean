import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Shrinking a finite-dimensional field extension to a small universe

Every finite-dimensional field extension `E/F` with `F` small (living, up to
equivalence, in `Type 0`) is itself small: hence `E` admits a model `E₀ : Type`
carrying the same `F`-algebra structure, and `E ≃ₐ[F] E₀`.

The proof shrinks `E` along `Shrink.{0} E`.  Mathlib already transports the
`Field` and `Algebra F` structures to `Shrink E`, and `Shrink.algEquiv F E`
is the corresponding `F`-algebra equivalence.  Smallness of `E` follows from
finite-dimensionality over the small field `F` via a basis: `E ≃ (Fin n → F)`.

This is the "universe bookkeeping" lemma behind the local-completion arguments
in the proof of the Neukirch–Uchida theorem, where one needs all the relevant
fields to live in a common (small) universe.
-/

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false in
theorem exists_type_zero_field_of_finiteDimensional
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [Small.{0} F] :
    ∃ (E₀ : Type) (_ : Field E₀) (_ : Algebra F E₀) (_ : FiniteDimensional F E₀),
      Nonempty (E ≃ₐ[F] E₀) := by
  -- `E` is finite-dimensional over a small field, hence small.
  haveI hsmall : Small.{0} E :=
    small_map (Module.Basis.equivFun (Module.finBasis F E)).toEquiv
  refine ⟨Shrink.{0} E, inferInstance, inferInstance, ?_, ⟨(Shrink.algEquiv F E).symm⟩⟩
  exact (Shrink.linearEquiv F E).symm.finiteDimensional

end Commons.NumberTheory.NumberField.Completion