import Mathlib
import Submission.Work.SymQuot.DivOf.C1Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open Work.CurveBasics

/-! ## Auxiliary facts about `Scheme.Hom.appLE`

These are the (elementary) functoriality and proof-irrelevance statements for the restriction
`appLE` of the pullback of sections of a morphism of schemes.  They are used to compare the two
ways of pulling back a section of `C` to `C_{F''}`: directly along `C_{F''} ⟶ C`, or in two
steps through `C_F`. -/

/-- `appLE` only depends on the underlying proposition, not on the chosen proof of the
inclusion of opens. -/
lemma appLE_proof_irrel {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e₁ e₂ : V ≤ f ⁻¹ᵁ U) : f.appLE U V e₁ = f.appLE U V e₂ := by
  unfold Scheme.Hom.appLE
  congr 1

/-- Composition rule for `appLE` evaluated on an element: pulling back along `g` and then along
`f` is pulling back along `f ≫ g`. -/
lemma appLE_comp_appLE_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V)
    (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x)
      = ((f ≫ g).appLE U W
          (e₂.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE e₁)).le)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- `appLE` is invariant under an equality of the underlying morphisms of schemes. -/
lemma appLE_congr_mor {X Y : Scheme} (f f' : X ⟶ Y) (h : f = f') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V e' := by
  subst h
  exact appLE_proof_irrel f U V e e'

/-- **`bcSec` is the pullback along `C_{F''} ⟶ C`.**  Pulling a section of `C` back to `C_F` and
then further to `C_{F''}` along the tower morphism is the same as pulling it back to `C_{F''}`
directly.  This is the functoriality of `appLE` in the morphism, using
`towerHom ≫ baseChangeFst C F = baseChangeFst C F''`. -/
theorem bcSec_secAlpha {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (F F'' : Type u) [Field F] [Field F''] [Algebra K F] [Algebra K F''] [Algebra F F'']
    [IsScalarTower K F F''] (V : C.left.Opens) (b : C.left.presheaf.obj (Opposite.op V)) :
    bcSec (C := C) F F'' V (secAlpha C F V b) = secAlpha C F'' V b := by
  show (BCSquareBaseChange.towerHom.appLE (C.bcOpens F V) (C.bcOpens F'' V)
      (le_of_eq (towerHom_preimage_bcOpens (C := C) F F'' V).symm)).hom
      (((Curve.baseChangeFst C F).appLE V (C.bcOpens F V) le_rfl).hom b)
    = ((Curve.baseChangeFst C F'').appLE V (C.bcOpens F'' V) le_rfl).hom b
  rw [appLE_comp_appLE_apply (BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F''))
        (Curve.baseChangeFst C F) V (C.bcOpens F V) (C.bcOpens F'' V) le_rfl
        (le_of_eq (towerHom_preimage_bcOpens (C := C) F F'' V).symm) b]
  exact congrArg (fun φ => φ.hom b)
    (appLE_congr_mor
      (BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F'') ≫ Curve.baseChangeFst C F)
      (Curve.baseChangeFst C F'') (BCSquareBaseChange.towerHom_fst (C := C) (F := F) (F' := F''))
      V (C.bcOpens F'' V) _ le_rfl)

end Work.SymQuot.DivOf
