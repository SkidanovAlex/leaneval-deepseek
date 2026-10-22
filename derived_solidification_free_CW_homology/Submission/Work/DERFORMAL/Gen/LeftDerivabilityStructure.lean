/-
# Left derivability structures from functorial left resolutions

This is the dual of `LocalizerMorphism.isRightDerivabilityStructure_of_functorial_resolutions`
(Mathlib): if `Φ : LocalizerMorphism W₁ W₂` has a fully faithful underlying functor with
`W₁ = W₂.inverseImage Φ.functor`, if there is a functor `ρ : C₂ ⥤ C₁` together with a
natural transformation `i : ρ ⋙ Φ.functor ⟶ 𝟭 C₂` whose components lie in `W₂`, and if `W₂`
is multiplicative and has the two-out-of-three property, then `Φ` is a *left* derivability
structure.

The proof dualises the whole situation: `Φ` is a left derivability structure iff `Φ.op` is a
right derivability structure, and the data `(ρ, i : ρ ⋙ Φ.functor ⟶ 𝟭 C₂)` becomes the data
`(ρ.op, NatTrans.op i : 𝟭 C₂ᵒᵖ ⟶ ρ.op ⋙ Φ.op.functor)` of a functorial right resolution for
`Φ.op`, to which the Mathlib constructor applies.
-/
import Mathlib

namespace Work.DERFORMAL.Gen

open CategoryTheory

theorem LeftDerivabilityStructure {C₁ : Type*} {C₂ : Type*} [Category C₁] [Category C₂] {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} (Φ : LocalizerMorphism W₁ W₂) {ρ : C₂ ⥤ C₁} (i : ρ ⋙ Φ.functor ⟶ 𝟭 C₂) (hi : ∀ X₂, W₂ (i.app X₂)) (hW₁ : W₁ = W₂.inverseImage Φ.functor) [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty] [W₂.IsMultiplicative] : Φ.IsLeftDerivabilityStructure := by
  rw [LocalizerMorphism.isLeftDerivabilityStructure_iff_op]
  have h : W₁.op = W₂.op.inverseImage Φ.functor.op :=
    (congrArg MorphismProperty.op hW₁).trans (MorphismProperty.op_inverseImage W₂ Φ.functor)
  exact LocalizerMorphism.isRightDerivabilityStructure_of_functorial_resolutions (Φ := Φ.op)
    (ρ := ρ.op) (i := NatTrans.op i)
    (hi := fun X => by
      show W₂ ((NatTrans.op i).app X).unop
      simpa using hi X.unop)
    (hW₁ := h)

end Work.DERFORMAL.Gen
