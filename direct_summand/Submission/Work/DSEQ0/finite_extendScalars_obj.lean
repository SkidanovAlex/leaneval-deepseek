import Mathlib

/-!
# Finiteness is preserved by extension of scalars

If `M` is a finite `A`-module and `φ : A →+* B` is a ring homomorphism, then the extension of
scalars `B ⊗[A] M` is a finite `B`-module.  Indeed, if `m₁, …, mₙ` generate `M` over `A` then
`1 ⊗ m₁, …, 1 ⊗ mₙ` generate `B ⊗[A] M` over `B`; this is Mathlib's `Module.Finite.base_change`.

The underlying type of `(ModuleCat.extendScalars φ).obj M` is `TensorProduct A B M`, where `B`
carries the `A`-module structure induced by `φ`; making `φ` into an `Algebra A B` instance
(`φ.toAlgebra`) puts us exactly in the situation of `Module.Finite.base_change`.
-/

namespace Work.DSEQ0

set_option linter.style.haveILetI false

universe u

theorem finite_extendScalars_obj {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (M : ModuleCat.{u} A) [Module.Finite A ↥M] :
    Module.Finite B ↥((ModuleCat.extendScalars φ).obj M) := by
  -- `letI` (rather than `haveI`) is important here: it inlines the value `φ.toAlgebra`, so that
  -- the `Module A B` structure arising from the algebra instance reduces to the `Module.compHom`
  -- structure used in the definition of `ModuleCat.extendScalars`.
  letI : Algebra A B := φ.toAlgebra
  exact Module.Finite.base_change (R := A) (A := B) (M := ↥M)

end Work.DSEQ0
