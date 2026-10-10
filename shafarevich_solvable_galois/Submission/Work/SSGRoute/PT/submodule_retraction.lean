import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- Over a prime field `ZMod p`, every submodule of a module splits off: there is an additive
retraction of the inclusion `L ↪ V`.  This is the semisimplicity (injectivity) of modules over
the field `ZMod p`, where `p` is prime. -/
theorem submodule_retraction (p : ℕ) [Fact p.Prime]
    (V : Type*) [AddCommGroup V] [Module (ZMod p) V] (L : Submodule (ZMod p) V) :
    ∃ r : V →+ ↥L, ∀ x : L, r (x : V) = x := by
  obtain ⟨g, hg⟩ :=
    (Submodule.subtype L).exists_leftInverse_of_injective (Submodule.ker_subtype L)
  exact ⟨g, fun x => by simpa using LinearMap.congr_fun hg x⟩

end Work.SSGRoute.PT
