import Mathlib
import Submission.Work.SymQuot.Product
import Submission.Work.SymQuot.Prod.isSeparated_prod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# `IsProper` for the powers `Xⁿ` (area SY)

If `X` is a `K`-scheme whose structure morphism `X.hom : X ⟶ Spec K` is proper, then so is
the structure morphism of every power `prod X n = X ×_K ⋯ ×_K X`.

The argument is the same as for separatedness (`SymQuot/Prod/isSeparated_prod.lean`): the
structure morphism of a binary product `Y ⨯ Z` of `K`-schemes proper over `K` is
`Y ×_K Z ⟶ Y ⟶ Spec K`, a base change of `Z.hom` followed by `Y.hom` — proper since
`IsProper` is stable under base change and composition; and `prod X (n+1) ≅ prod X n ⨯ X`
(`prodSuccIso`).  The empty product `prod X 0` is the terminal object of `Over (Spec K)`,
whose structure morphism is an isomorphism, hence proper.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.Prod

/-- The binary product (in `Over (Spec K)`, i.e. the fibre product over `Spec K`) of two
`K`-schemes proper over `K` is proper over `K`. -/
theorem isProper_prod_binary {K : Type*} [Field K] (Y Z : Work.GCBasics.Sch K)
    [IsProper Y.hom] [IsProper Z.hom] : IsProper (Y ⨯ Z).hom := by
  -- `(Y ⨯ Z).left ≅ Y ×_{Spec K} Z` and `(Y ⨯ Z).hom = fst ≫ Y.hom`.
  have hkey : (Over.prodLeftIsoPullback Y Z).hom ≫ (pullback.fst Y.hom Z.hom ≫ Y.hom) =
      (Y ⨯ Z).hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst, Over.w]
  have hproper : IsProper ((Over.prodLeftIsoPullback Y Z).hom ≫
      (pullback.fst Y.hom Z.hom ≫ Y.hom)) := inferInstance
  rwa [hkey] at hproper

/-- **The `n`-fold product of a `K`-scheme proper over `K` is proper over `K`.** -/
theorem isProper_pi_prod {K : Type*} [Field K] (X : Work.GCBasics.Sch K) (n : ℕ)
    [IsProper X.hom] : IsProper (∏ᶜ (fun _ : Fin n => X)).hom := by
  induction n with
  | zero =>
    -- `X⁰` is the terminal object of `Over (Spec K)`; its structure morphism is an isomorphism.
    have hT : IsTerminal (∏ᶜ (fun _ : Fin 0 => X)) :=
      Equiv.toFun (isLimitEquivIsTerminalOfIsEmpty (Work.GCBasics.Sch K)
        (limit.cone (Discrete.functor (fun _ : Fin 0 => X)))) (limit.isLimit _)
    let T := ∏ᶜ (fun _ : Fin 0 => X)
    let g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ T := hT.from _
    let f : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) := Over.homMk T.hom (by simp)
    have h1 : f ≫ g = 𝟙 T := hT.hom_ext (f ≫ g) (𝟙 T)
    have h2 : g.left ≫ T.hom = 𝟙 (Spec (CommRingCat.of K)) := Over.w g
    have h3 : T.hom ≫ g.left = 𝟙 T.left := congrArg (fun φ : T ⟶ T => φ.left) h1
    haveI : IsIso T.hom := ⟨g.left, h3, h2⟩
    exact inferInstance
  | succ n ih =>
    haveI : IsProper (∏ᶜ (fun _ : Fin n => X)).hom := ih
    have hbin : IsProper ((∏ᶜ (fun _ : Fin n => X)) ⨯ X).hom :=
      isProper_prod_binary (∏ᶜ (fun _ : Fin n => X)) X
    haveI hIso : IsIso (prodSuccIso X n).hom.left :=
      (Over.forget _).map_isIso (prodSuccIso X n).hom
    have hcomp : IsProper ((prodSuccIso X n).hom.left ≫
        ((∏ᶜ (fun _ : Fin n => X)) ⨯ X).hom) :=
      (MorphismProperty.cancel_left_of_respectsIso @IsProper (prodSuccIso X n).hom.left
        (((∏ᶜ (fun _ : Fin n => X)) ⨯ X).hom)).mpr hbin
    rwa [Over.w (prodSuccIso X n).hom] at hcomp

theorem isProper_prod {K : Type*} [Field K] (X : Work.GCBasics.Sch K) (n : ℕ) [AlgebraicGeometry.IsProper X.hom] : AlgebraicGeometry.IsProper (Work.SymQuot.prod X n).hom := by
  change IsProper (∏ᶜ (fun _ : Fin n => X)).hom
  exact isProper_pi_prod X n

end Work.SymQuot.Prod
