import Mathlib
import Submission.Work.SymQuot.Product
import Submission.Work.SymQuot.Prod.isSeparated_prod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# `IsReduced` for the powers `Xⁿ` (area SY)

If `X` is a `K`-scheme which is geometrically reduced, flat and locally of finite type over `K`
(and reduced), then every power `prod X n = X ×_K ⋯ ×_K X` is reduced.

The argument is a two-step induction:

* `prod X (n+1) ≅ prod X n ⨯ X` (`prodSuccIso`) and `(prod X n ⨯ X).left ≅ Xⁿ ×_K X`
  (`Over.prodLeftIsoPullback`), so `prod X (n+1)` is (isomorphic to) the fibre product over `K`
  of `prod X n` and `X`;
* Mathlib's `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian` (in the form of the
  instances for `IsReduced (pullback f g)`) says that `X ×_K Y` is reduced as soon as `K`-scheme
  `Y` is geometrically reduced, flat and locally of finite type over a reduced, locally noetherian
  base and `X` is reduced and locally noetherian.  Both these side conditions are inherited by the
  powers:
  * `LocallyOfFiniteType` (hence `IsLocallyNoetherian`, the base `Spec K` being Noetherian) is
    stable under base change and composition, giving `isLocallyNoetherian_prod`;
  * reducedness of `prod X n` is exactly the induction hypothesis.

The empty power `prod X 0` is the terminal object of `Sch K = Over (Spec K)`, whose structure
morphism is an isomorphism; it is reduced (resp. locally noetherian) because `Spec K` is.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry

namespace Work.SymQuot.Prod

variable {K : Type*} [Field K]

/-- `X⁰` is the terminal object of `Sch K = Over (Spec K)`, so its structure morphism is an
isomorphism. -/
lemma isIso_prod_zero_hom (X : Work.GCBasics.Sch K) :
    IsIso (Work.SymQuot.prod X 0).hom := by
  have hT : IsTerminal (∏ᶜ (fun _ : Fin 0 => X)) :=
    Equiv.toFun (isLimitEquivIsTerminalOfIsEmpty (Work.GCBasics.Sch K)
      (limit.cone (Discrete.functor (fun _ : Fin 0 => X)))) (limit.isLimit _)
  let T := ∏ᶜ (fun _ : Fin 0 => X)
  let g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ T := hT.from _
  let f : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) := Over.homMk T.hom (by simp)
  have h1 : f ≫ g = 𝟙 T := hT.hom_ext (f ≫ g) (𝟙 T)
  have h2 : g.left ≫ T.hom = 𝟙 (Spec (CommRingCat.of K)) := Over.w g
  have h3 : T.hom ≫ g.left = 𝟙 T.left := congrArg (fun φ : T ⟶ T => φ.left) h1
  exact ⟨g.left, h3, h2⟩

/-- The empty power `X⁰` is reduced (its structure morphism is an isomorphism onto `Spec K`). -/
lemma isReduced_prod_zero (X : Work.GCBasics.Sch K) :
    IsReduced (Work.SymQuot.prod X 0).left := by
  haveI : IsIso (Work.SymQuot.prod X 0).hom := isIso_prod_zero_hom X
  exact isReduced_of_isOpenImmersion (Work.SymQuot.prod X 0).hom

/-- The empty power `X⁰` is locally noetherian (it is isomorphic to `Spec K`). -/
lemma isLocallyNoetherian_prod_zero (X : Work.GCBasics.Sch K) :
    IsLocallyNoetherian (Work.SymQuot.prod X 0).left := by
  haveI : IsIso (Work.SymQuot.prod X 0).hom := isIso_prod_zero_hom X
  exact isLocallyNoetherian_of_isOpenImmersion (Work.SymQuot.prod X 0).hom

/-- **`Xⁿ⁺¹` is the fibre product of `Xⁿ` and `X` over `K`**: the composite of the splitting
`prod X (n+1) ≅ prod X n ⨯ X` of the powers with the identification of a product in `Over (Spec K)`
with a fibre product over `Spec K`. -/
noncomputable def prodSuccPullbackIso (X : Work.GCBasics.Sch K) (n : ℕ) :
    (Work.SymQuot.prod X (n + 1)).left ≅ pullback (Work.SymQuot.prod X n).hom X.hom :=
  (Over.forget (Spec (CommRingCat.of K))).mapIso (prodSuccIso X n) ≪≫
    Over.prodLeftIsoPullback (Work.SymQuot.prod X n) X

/-- **The `n`-fold power of a `K`-scheme locally of finite type over `K` is locally noetherian**
(`Spec K` being locally noetherian, `LocallyOfFiniteType` = finite type on affine pieces is stable
under base change and composition). -/
lemma isLocallyNoetherian_prod (X : Work.GCBasics.Sch K) (n : ℕ)
    [LocallyOfFiniteType X.hom] : IsLocallyNoetherian (Work.SymQuot.prod X n).left := by
  induction n with
  | zero => exact isLocallyNoetherian_prod_zero X
  | succ n ih =>
    haveI : IsLocallyNoetherian (Work.SymQuot.prod X n).left := ih
    exact isLocallyNoetherian_of_isOpenImmersion (prodSuccPullbackIso X n).hom

theorem isReduced_pi_prod {K : Type*} [Field K] (X : Work.GCBasics.Sch K) (n : ℕ)
    [AlgebraicGeometry.IsReduced X.left] [AlgebraicGeometry.GeometricallyReduced X.hom]
    [AlgebraicGeometry.Flat X.hom] [AlgebraicGeometry.LocallyOfFiniteType X.hom] :
    AlgebraicGeometry.IsReduced (Work.SymQuot.prod X n).left := by
  induction n with
  | zero => exact isReduced_prod_zero X
  | succ n ih =>
    haveI : IsReduced (Work.SymQuot.prod X n).left := ih
    haveI : IsLocallyNoetherian (Work.SymQuot.prod X n).left := isLocallyNoetherian_prod X n
    exact isReduced_of_isOpenImmersion (prodSuccPullbackIso X n).hom

end Work.SymQuot.Prod
