import Mathlib.FieldTheory.Galois.Basic
import Submission.NK.LocalArtin.Reduction.reciprocityMap_of_reciprocityLaw
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kernel condition of local class field theory from the reciprocity law

`NK.LocalCFT.ReciprocityLaw F F'` is the reciprocity law of local class field theory in its
canonical, compatible form: at every finite abelian Galois level `L ≤ F^{ab}` it provides an
isomorphism `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`, compatibly with restriction between levels.

`NK.LocalArtin.KernelCondition F F'` is the *weaker* structural statement that there is a single
homomorphism `Fˣ →* Gal(F^{ab}/F)` whose restriction to every finite abelian Galois level has kernel
exactly the norm group — surjectivity is *not* demanded (it is recovered from the norm index
theorem, see `NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap`).

The content of this file is that the reciprocity law already produces the kernel condition: the
compatible family of level isomorphisms is the family of level restrictions of a single map
`NK.LocalCFT.Reduction.artinMap hlaw : Fˣ →* Gal(F^{ab}/F)`, and each level map is injective on
the quotient by the norm group, so its kernel is the norm group.
-/

set_option linter.unusedVariables false

universe u v

namespace NK.LocalReciprocityLubinTate.Unramified

/-- **The kernel condition from the reciprocity law.**

The Artin map `NK.LocalCFT.Reduction.artinMap hlaw` attached to a reciprocity law restricts at
every finite abelian Galois level `L ≤ F^{ab}` to the reciprocity isomorphism
`Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`; hence the kernel of the level map is exactly the norm group
`N_{L/F} Lˣ`.  Forgetting surjectivity from the reciprocity map therefore yields a
`NK.LocalArtin.KernelCondition F F'`. -/
theorem nonempty_kernelCondition_of_reciprocityLaw {F : Type u} {F' : Type v} [Field F]
    [Field F'] [Algebra F F'] [IsGalois F F'] (hlaw : NK.LocalCFT.ReciprocityLaw F F') :
    Nonempty (NK.LocalArtin.KernelCondition F F') := by
  obtain ⟨R⟩ := NK.LocalArtin.Reduction.reciprocityMap_of_reciprocityLaw hlaw
  exact ⟨R.toKernelCondition⟩

end NK.LocalReciprocityLubinTate.Unramified
