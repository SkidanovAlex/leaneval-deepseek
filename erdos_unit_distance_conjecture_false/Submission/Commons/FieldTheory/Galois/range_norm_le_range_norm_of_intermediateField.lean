import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Galois

/-- For a finite field extension `B/A` and an intermediate field `F`, the norm map
`N_{B/A}` factors as `N_{F/A} ∘ N_{B/F}` (transitivity of the norm), hence the range of
the unit norm `Bˣ →* Aˣ` is contained in the range of the unit norm `Fˣ →* Aˣ`. -/
theorem range_norm_le_range_norm_of_intermediateField
    {A B : Type*} [Field A] [Field B] [Algebra A B] [FiniteDimensional A B]
    (F : IntermediateField A B) :
    MonoidHom.range (Units.map (Algebra.norm A : B →* A)) ≤
      MonoidHom.range (Units.map (Algebra.norm A : F →* A)) := by
  rintro x ⟨u, rfl⟩
  refine ⟨Units.map (Algebra.norm F : B →* F) u, ?_⟩
  ext
  simp only [Units.coe_map]
  rw [Algebra.norm_norm]

end Commons.FieldTheory.Galois