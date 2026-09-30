/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Symⁿ C` is integral (area SY)

The symmetric power `Symⁿ C = Cⁿ/S_n` is integral: it is the quotient of the integral scheme
`Cⁿ` by the finite group `S_n`, and such a quotient is irreducible (it is the continuous image
of the irreducible `Cⁿ` under the surjective quotient map `Sym.quot`) and reduced (it is covered
by the charts `Spec Γ(Cⁿ, U)^{S_n}`, and a subring of the reduced ring `Γ(Cⁿ, U)` is reduced).

The ingredients are:

* `Cⁿ` is integral, `smooth_pi_prod`/`isIntegral_pi_prod`: the `(n+1)`-fold power splits as
  `Cⁿ ×_K C` (`Prod.prodSuccIso`), a fibre product of the geometrically integral curve `C` with
  the integral `Cⁿ`, which is integral by `AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_isLocallyNoetherian`;
  smoothness of the structure morphism — needed to know that `Cⁿ` is locally noetherian — is
  again stable under base change and composition.
* `isIntegral_quotient`: the quotient `X/Γ` of an integral scheme `X` by a finite group is
  integral, using `IsReduced.of_openCover` for the charts and the surjectivity of the quotient
  map (`QuotientData.quotientMap_surjective`) for irreducibility.
-/
import Mathlib
import Submission.Work.SymQuot.Sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

variable {K : Type u} [Field K]

/-- **The empty power `X⁰`**: it is the terminal object of `Sch K`, so its structure morphism
`X⁰ ⟶ Spec K` is an isomorphism. -/
theorem isIso_hom_pi_zero (X : Work.GCBasics.Sch K) :
    IsIso (Over.hom (∏ᶜ (fun _ : Fin 0 => X))) := by
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

/-- **The structure morphism of `Cⁿ` is smooth.**  For `n = 0` this is the isomorphism
`Spec K ⟶ Spec K`, and in the step `C^{n+1} = Cⁿ ×_K C` the structure morphism is the composite
of the projection to `Cⁿ` (a base change of the smooth morphism `C ⟶ Spec K`, hence smooth) with
the structure morphism of `Cⁿ` (smooth by induction). -/
theorem smooth_pi_prod (C : Work.CurveBasics.Curve K) (n : ℕ) :
    Smooth (Over.hom (∏ᶜ (fun _ : Fin n => C.toOver))) := by
  haveI : Smooth C.toOver.hom := SmoothOfRelativeDimension.smooth 1 C.toOver.hom
  induction n with
  | zero =>
    haveI h : IsIso (Over.hom (∏ᶜ (fun _ : Fin 0 => C.toOver))) := isIso_hom_pi_zero C.toOver
    exact inferInstance
  | succ n ih =>
    haveI ih' : Smooth (Over.hom (∏ᶜ (fun _ : Fin n => C.toOver))) := ih
    -- `Cⁿ ×_K C` has the structure morphism `Cⁿ ×_K C ⟶ Cⁿ ⟶ Spec K`.
    have hkey : (Over.prodLeftIsoPullback (∏ᶜ (fun _ : Fin n => C.toOver)) C.toOver).hom ≫
        (pullback.fst (Over.hom (∏ᶜ (fun _ : Fin n => C.toOver))) C.toOver.hom ≫
          Over.hom (∏ᶜ (fun _ : Fin n => C.toOver))) =
        ((∏ᶜ (fun _ : Fin n => C.toOver)) ⨯ C.toOver).hom := by
      rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst, Over.w]
    have hbin : Smooth (((∏ᶜ (fun _ : Fin n => C.toOver)) ⨯ C.toOver).hom) := by
      rw [← hkey]
      exact inferInstance
    haveI hIso : IsIso (Prod.prodSuccIso C.toOver n).hom.left :=
      (Over.forget _).map_isIso (Prod.prodSuccIso C.toOver n).hom
    rw [← Over.w (Prod.prodSuccIso C.toOver n).hom]
    exact inferInstance

/-- **The `n`-fold power `Cⁿ` of a curve is integral.**  For `n = 0` it is `Spec K`, and in the
step `C^{n+1} = Cⁿ ×_K C` the fibre product of the geometrically integral, flat and universally
open morphism `C ⟶ Spec K` with the integral and locally noetherian `Cⁿ` (locally noetherian
because it is smooth over `Spec K`) is integral. -/
theorem isIntegral_pi_prod (C : Work.CurveBasics.Curve K) (n : ℕ) :
    IsIntegral (Over.left (∏ᶜ (fun _ : Fin n => C.toOver))) := by
  induction n with
  | zero =>
    haveI h : IsIso (Over.hom (∏ᶜ (fun _ : Fin 0 => C.toOver))) := isIso_hom_pi_zero C.toOver
    exact IsIntegral.of_isIso (inv (Over.hom (∏ᶜ (fun _ : Fin 0 => C.toOver))))
  | succ n ih =>
    haveI ih' : IsIntegral (Over.left (∏ᶜ (fun _ : Fin n => C.toOver))) := ih
    haveI hsm : Smooth (Over.hom (∏ᶜ (fun _ : Fin n => C.toOver))) := smooth_pi_prod C n
    haveI hlft : LocallyOfFiniteType (Over.hom (∏ᶜ (fun _ : Fin n => C.toOver))) := inferInstance
    haveI hln : IsLocallyNoetherian (Over.left (∏ᶜ (fun _ : Fin n => C.toOver))) :=
      LocallyOfFiniteType.isLocallyNoetherian (Over.hom (∏ᶜ (fun _ : Fin n => C.toOver)))
    haveI hbin : IsIntegral (pullback (Over.hom (∏ᶜ (fun _ : Fin n => C.toOver))) C.toOver.hom) :=
      inferInstance
    haveI hx : IsIntegral (Over.left ((∏ᶜ (fun _ : Fin n => C.toOver)) ⨯ C.toOver)) :=
      IsIntegral.of_isIso (Over.prodLeftIsoPullback (∏ᶜ (fun _ : Fin n => C.toOver)) C.toOver).inv
    haveI hIso : IsIso (Prod.prodSuccIso C.toOver n).inv.left :=
      (Over.forget _).map_isIso (Prod.prodSuccIso C.toOver n).inv
    exact IsIntegral.of_isIso (Prod.prodSuccIso C.toOver n).inv.left

/-- `Cⁿ` is integral, in the form used by the quotient construction (`Work.SymQuot.prod`). -/
theorem isIntegral_prod (C : Work.CurveBasics.Curve K) (n : ℕ) :
    IsIntegral (prod C.toOver n).left :=
  isIntegral_pi_prod C n

/-- **The quotient of an integral scheme by a finite group is integral.**  Reducedness holds
because the quotient is covered by the charts `Spec Γ(X, U)^Γ`, and `Γ(X, U)^Γ` is a subring of
the reduced ring `Γ(X, U)`; irreducibility holds because the quotient map `X ⟶ X/Γ` is surjective
and continuous, so the image of the irreducible space `X` is the irreducible space `X/Γ`. -/
theorem isIntegral_quotient {Γ : Type u} [Group Γ] [Fintype Γ] {X : Scheme.{u}}
    (D : QuotientData Γ X) [IsIntegral X] : IsIntegral D.Quotient := by
  haveI : IrreducibleSpace X := inferInstance
  haveI hinst : ∀ i, IsReduced ((Scheme.IsLocallyDirected.openCover D.chartFunctor).X i) :=
    fun i => by
      change IsReduced (D.chartFunctor.obj i)
      exact (affine_isReduced_iff _).mpr
        (isReduced_of_injective (Subring.subtype _) Subtype.val_injective)
  haveI hred : IsReduced D.Quotient :=
    IsReduced.of_openCover D.Quotient (Scheme.IsLocallyDirected.openCover D.chartFunctor)
  haveI hirr : IrreducibleSpace D.Quotient := by
    rw [irreducibleSpace_def]
    have h := (IrreducibleSpace.isIrreducible_univ X).image D.quotientMap
      D.quotientMap.continuous.continuousOn
    rwa [Set.image_univ, Set.range_eq_univ.mpr D.quotientMap_surjective] at h
  exact isIntegral_of_irreducibleSpace_of_isReduced D.Quotient

end Work.SymQuot

namespace Work.SymQuot.Sym

/-- **The `n`-th symmetric power of a curve is integral.**  `Symⁿ C = Cⁿ/S_n` is the quotient of
the integral scheme `Cⁿ` by the finite group `S_n` (`Work.SymQuot.symData`), and
`Work.SymQuot.isIntegral_quotient` applies. -/
theorem isIntegral_sym {K : Type*} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) : AlgebraicGeometry.IsIntegral (Work.SymQuot.Sym C n).left := by
  haveI h : IsIntegral (Work.SymQuot.prod C.toOver n).left := Work.SymQuot.isIntegral_prod C n
  exact Work.SymQuot.isIntegral_quotient (Work.SymQuot.symData C n)

end Work.SymQuot.Sym
