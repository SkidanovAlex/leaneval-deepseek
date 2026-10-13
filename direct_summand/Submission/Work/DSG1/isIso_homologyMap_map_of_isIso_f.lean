import Mathlib

namespace Work.DSG1

open CategoryTheory Limits

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- A morphism of cochain complexes which is an isomorphism in the three degrees
`i - 1`, `i`, `i + 1` induces an isomorphism on `H^i`.

This is the general (functor-free) statement, obtained by observing that the homology in degree
`i` only depends on those three degrees: it is the homology of the short complex
`K.X (i-1) ⟶ K.X i ⟶ K.X (i+1)`, and a morphism of short complexes all of whose components are
isomorphisms is an isomorphism. -/
lemma isIso_homologyMap_of_isIso_three {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) (i : ℤ)
    (h₁ : IsIso (φ.f (i - 1))) (h₂ : IsIso (φ.f i)) (h₃ : IsIso (φ.f (i + 1))) :
    IsIso (HomologicalComplex.homologyMap φ i) := by
  change IsIso (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map φ))
  have h1' : IsIso (φ.f ((ComplexShape.up ℤ).prev i)) := by
    rw [CochainComplex.prev]; exact h₁
  have h3' : IsIso (φ.f ((ComplexShape.up ℤ).next i)) := by
    rw [CochainComplex.next]; exact h₃
  haveI τ1 : IsIso
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map φ).τ₁ := h1'
  haveI τ2 : IsIso
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map φ).τ₂ := h₂
  haveI τ3 : IsIso
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map φ).τ₃ := h3'
  haveI : IsIso ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map φ) :=
    ShortComplex.isIso_of_isIso _
  exact ShortComplex.isIso_homologyMap_of_iso _

/-- An additive functor preserves the property of a morphism of cochain complexes of inducing an
isomorphism on `H^i`, when it is already an isomorphism in the three relevant degrees. -/
theorem isIso_homologyMap_map_of_isIso_f {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ}
    (φ : K ⟶ L) (i : ℤ) (h₁ : IsIso (φ.f (i - 1))) (h₂ : IsIso (φ.f i))
    (h₃ : IsIso (φ.f (i + 1))) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) i) := by
  apply isIso_homologyMap_of_isIso_three
  · haveI := h₁
    rw [Functor.mapHomologicalComplex_map_f]
    infer_instance
  · haveI := h₂
    rw [Functor.mapHomologicalComplex_map_f]
    infer_instance
  · haveI := h₃
    rw [Functor.mapHomologicalComplex_map_f]
    infer_instance

end Work.DSG1
