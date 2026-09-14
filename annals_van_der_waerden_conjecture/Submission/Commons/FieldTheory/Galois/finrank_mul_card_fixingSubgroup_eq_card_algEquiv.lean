import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Galois

theorem finrank_mul_card_fixingSubgroup_eq_card_algEquiv (E : Type*) [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] [IsGalois ℚ E] (L : IntermediateField ℚ E) :
    Module.finrank ℚ ↥L * Nat.card (L.fixingSubgroup) = Nat.card (E ≃ₐ[ℚ] E) := by
  rw [IsGalois.card_fixingSubgroup_eq_finrank L, IsGalois.card_aut_eq_finrank ℚ E,
    Module.finrank_mul_finrank ℚ ↥L E]

end Commons.FieldTheory.Galois