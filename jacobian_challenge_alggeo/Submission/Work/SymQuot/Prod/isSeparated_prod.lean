import Mathlib
import Submission.Work.SymQuot.Product

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# `IsSeparated` for the powers `Xⁿ` (area SY)

If `X` is a `K`-scheme whose structure morphism `X.hom : X ⟶ Spec K` is separated, then so is
the structure morphism of every power `prod X n = X ×_K ⋯ ×_K X`.

The proof is the classical one: the structure morphism of a binary product `Y ⨯ Z` of separated
`K`-schemes is separated (it is `Y ×_K Z ⟶ Z ⟶ Spec K`, a base change of `Y.hom` followed by
`Z.hom`), and `prod X (n+1) ≅ prod X n ⨯ X`.  The empty product `prod X 0` is the terminal object
of `Over (Spec K)`, whose structure morphism is an isomorphism.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry

namespace Work.SymQuot.Prod

/-- The binary product (in `Over (Spec K)`, i.e. the fibre product over `Spec K`) of two
`K`-schemes separated over `K` is separated over `K`. -/
theorem isSeparated_prod_binary {K : Type*} [Field K] (Y Z : Work.GCBasics.Sch K)
    [IsSeparated Y.hom] [IsSeparated Z.hom] : IsSeparated (Y ⨯ Z).hom := by
  -- `(Y ⨯ Z).left ≅ Y ×_{Spec K} Z` and `(Y ⨯ Z).hom = fst ≫ Y.hom`.
  have hkey : (Over.prodLeftIsoPullback Y Z).hom ≫ (pullback.fst Y.hom Z.hom ≫ Y.hom) =
      (Y ⨯ Z).hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst, Over.w]
  have hsep : IsSeparated ((Over.prodLeftIsoPullback Y Z).hom ≫
      (pullback.fst Y.hom Z.hom ≫ Y.hom)) := inferInstance
  rwa [hkey] at hsep

/-- The `(n+1)`-fold power splits off one factor: `X^{n+1} ≅ Xⁿ ×_K X`. -/
noncomputable def prodSuccIso {K : Type*} [Field K] (X : Work.GCBasics.Sch K) (n : ℕ) :
    (∏ᶜ (fun _ : Fin (n + 1) => X)) ≅ (∏ᶜ (fun _ : Fin n => X)) ⨯ X where
  hom := prod.lift
    (Pi.lift (fun k : Fin n => Pi.π (fun _ : Fin (n + 1) => X) (Fin.succ k)))
    (Pi.π (fun _ : Fin (n + 1) => X) 0)
  inv := Pi.lift (Fin.cases prod.snd (fun k : Fin n => prod.fst ≫ Pi.π (fun _ : Fin n => X) k))
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    induction i using Fin.cases with
    | zero => simp
    | succ k => simp
  inv_hom_id := by
    apply prod.hom_ext
    · apply Pi.hom_ext
      intro k
      simp
    · simp

/-- **The `n`-fold product of a separated `K`-scheme is separated over `K`.** -/
theorem isSeparated_pi_prod {K : Type*} [Field K] (X : Work.GCBasics.Sch K) (n : ℕ)
    [IsSeparated X.hom] : IsSeparated (∏ᶜ (fun _ : Fin n => X)).hom := by
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
    haveI : IsSeparated (∏ᶜ (fun _ : Fin n => X)).hom := ih
    have hbin : IsSeparated ((∏ᶜ (fun _ : Fin n => X)) ⨯ X).hom :=
      isSeparated_prod_binary _ _
    haveI hIso : IsIso (prodSuccIso X n).hom.left :=
      (Over.forget _).map_isIso (prodSuccIso X n).hom
    have hcomp : IsSeparated ((prodSuccIso X n).hom.left ≫
        ((∏ᶜ (fun _ : Fin n => X)) ⨯ X).hom) :=
      (MorphismProperty.cancel_left_of_respectsIso @IsSeparated (prodSuccIso X n).hom.left
        (((∏ᶜ (fun _ : Fin n => X)) ⨯ X).hom)).mpr hbin
    rwa [Over.w (prodSuccIso X n).hom] at hcomp

theorem isSeparated_prod {K : Type*} [Field K] (X : Work.GCBasics.Sch K) (n : ℕ) [AlgebraicGeometry.IsSeparated X.hom] : AlgebraicGeometry.IsSeparated (Work.SymQuot.prod X n).hom := by
  change IsSeparated (∏ᶜ (fun _ : Fin n => X)).hom
  exact isSeparated_pi_prod X n

end Work.SymQuot.Prod
