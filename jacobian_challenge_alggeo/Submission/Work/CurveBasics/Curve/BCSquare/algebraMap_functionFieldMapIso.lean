import Mathlib
import Submission.Work.CurveBasics.Curve.BCSquare.GermNaturality
import Submission.Work.CurveBasics.BaseChangeFunctionField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

/-- The isomorphism of function fields induced by a base-change square is compatible with the
structure morphisms to `Spec F`, hence sends the constants coming from `F` to the constants
coming from `F`.  This is the `F`-linearity of `functionFieldMapIso (isoBaseChange S)`. -/
theorem algebraMap_functionFieldMapIso {k : Type u} [Field k] {F : Type u} [Field F]
    [Algebra k F] {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (c : F) :
    (functionFieldMapIso (isoBaseChange S)).hom (algebraMap F (C.baseChange F).functionField c) =
      algebraMap F C'.functionField c := by
  haveI hY : Nonempty (⊤ : (C.baseChange F).left.Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  haveI hX : Nonempty (⊤ : C'.left.Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  haveI hYp : Nonempty ((isoBaseChange S).hom ⁻¹ᵁ (⊤ : (C.baseChange F).left.Opens)) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  -- unwind the `F`-algebra structures into the explicit composites of ring homomorphisms
  have hkey : algebraMap F (C.baseChange F).functionField c =
      ((C.baseChange F).left.germToFunctionField ⊤).hom
        ((C.baseChange F).hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c)) := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  have hkey2 : algebraMap F C'.functionField c =
      (C'.left.germToFunctionField ⊤).hom
        (C'.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c)) := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  rw [hkey, hkey2]
  -- the compatibility of `functionFieldMapIso` with the canonical maps to the function field
  rw [functionFieldMapIso_germToFunctionField (isoBaseChange S) ⊤
        ((C.baseChange F).hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c))]
  -- the isomorphism is an isomorphism over `Spec F`, so it intertwines the structure morphisms
  have hsnd : (isoBaseChange S).hom ≫ (C.baseChange F).hom = C'.hom := isoBaseChange_hom_snd S
  have happ := congrArg Scheme.Hom.appTop hsnd
  rw [Scheme.Hom.comp_appTop] at happ
  have hpt := ConcreteCategory.congr_hom happ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c)
  simp only [ConcreteCategory.comp_apply] at hpt
  have hpt2 : (CommRingCat.Hom.hom (Scheme.Hom.app (isoBaseChange S).hom ⊤))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (C.baseChange F).hom))
          ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of F)).inv) c))
      = (ConcreteCategory.hom (Scheme.Hom.appTop C'.hom))
          ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of F)).inv) c) := hpt
  -- the preimage of the top open is the top open, so the two germs agree definitionally
  have hgerm : (C'.left.germToFunctionField
        ((isoBaseChange S).hom ⁻¹ᵁ (⊤ : (C.baseChange F).left.Opens)))
      = (C'.left.germToFunctionField ⊤) := rfl
  rw [hpt2, hgerm]
  rfl

end Work.CurveBasics.Curve.BCSquare
