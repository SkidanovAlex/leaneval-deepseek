/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lifting a point of `Symⁿ C` to `n` points after a finite field extension

Let `C` be a smooth proper curve over a field `K`, `n : ℕ` and `p` a point of the `n`-th
symmetric power `Symⁿ C = Cⁿ/S_n` with values in a field extension `F/K`.  Then there is a
*finite* extension `F'/F` over which `p` becomes a sum of `n` points of `C`: a family
`x : Fin n → C(F')` with `Sym.powMap C n x = p_{F'}`.

This is the "splitting after a finite extension" statement for the point/divisor dictionary: an
effective divisor of degree `n` on `C_F` splits into `n` geometric points over a finite extension
of its field of definition.

## Proof

The quotient map `q = Sym.quot C n : Cⁿ ⟶ Symⁿ C` is surjective, so the fibre product
`W = Cⁿ ×_{Symⁿ C} Spec F` is nonempty.  The key point is that `W` is *locally of finite type*
over `F`, so that its closed points have finite residue field over `F` (Zariski's lemma,
`Work.Charts.finiteDimensional_resField_of_isClosed`).

`W` is not the base change of an obviously finite type morphism — but it is a closed subscheme
of the fibre product *over the base field* `Cⁿ ×_K Spec F`, which is locally of finite type over
`F` because `Cⁿ` is proper (hence locally of finite type) over `K`.  Concretely: for
`i := (Sym C n).hom : Symⁿ C ⟶ Spec K`, `f := q : Cⁿ ⟶ Symⁿ C` and `g := p`, the square

```
   Cⁿ ×_{Symⁿ C} Spec F  ⟶  Cⁿ ×_K Spec F
          |                        |
          ↓                        ↓
      Symⁿ C    ⟶(Δᵢ)       Symⁿ C ×_K Symⁿ C
```

is a pullback (`pullbackDiagonalMapIdIso`), and the diagonal `Δᵢ` is a closed immersion because
`Symⁿ C` is separated over `K` (`Work.SymQuot.Sym.isSeparated_sym`).  Hence the second projection
of `W` is locally of finite type (`locallyOfFiniteType_pullback_snd_of_isSeparated` below).

Taking a closed point `w` of `W` (which exists because a nonempty locally finite type scheme over
a field is Jacobson), the residue field `F' := κ(w)` is finite over `F` and the canonical
`F'`-point of `W` gives, on the two legs, an `F'`-point of `Cⁿ` lying over `p`, and the structure
map `F → F'`.
-/
import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Sym.isSeparated_sym
import Submission.Work.SymQuot.Prod.isProper_prod
import Submission.Work.SymQuot.Sym.isFinite_quot
import Submission.Work.Charts.finiteDimensional_resField_of_isClosed

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

namespace Work.SymQuot.Sym

universe u

/-- **The fibre of a separated quotient over a point is locally of finite type.**

Let `f : X ⟶ T`, `g : Y ⟶ T` and `i : T ⟶ S` be morphisms of schemes with `i` separated, and
assume that the composite `f ≫ i` is locally of finite type.  Then the second projection
`X ×_T Y ⟶ Y` of the fibre product is locally of finite type.

Indeed `X ×_T Y` sits as a closed subscheme of `X ×_S Y` (the pullback of the diagonal of `i`
along the pair map `(f ≫ i, g ≫ i)`, see `pullbackDiagonalMapIdIso`), and `X ×_S Y ⟶ Y` is the
base change of the locally finite type morphism `f ≫ i`. -/
theorem locallyOfFiniteType_pullback_snd_of_isSeparated
    {X Y T S : Scheme.{u}} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S) [IsSeparated i]
    [LocallyOfFiniteType (f ≫ i)] :
    LocallyOfFiniteType (Limits.pullback.snd f g) := by
  have : IsClosedImmersion (pullback.diagonal i) := IsSeparated.isClosedImmersion_diagonal
  have : LocallyOfFiniteType (pullback.diagonal i) := inferInstance
  -- `pullback.snd f g` is, via `pullbackDiagonalMapIdIso`, the composite of the closed immersion
  -- `pullback.snd (pullback.diagonal i) _` with the base change `pullback.snd (f ≫ i) (g ≫ i)`.
  have key : LocallyOfFiniteType ((pullbackDiagonalMapIdIso f g i).hom ≫
      Limits.pullback.snd f g) := by
    rw [pullbackDiagonalMapIdIso_hom_snd]
    infer_instance
  have h1 : LocallyOfFiniteType ((pullbackDiagonalMapIdIso f g i).inv ≫
      ((pullbackDiagonalMapIdIso f g i).hom ≫ Limits.pullback.snd f g)) := inferInstance
  rw [Iso.inv_hom_id_assoc] at h1
  exact h1

/-- **Naturality of `Sym.powMap` in the field of definition.**  For a `K`-algebra homomorphism
of fields `e : F →ₐ[K] F'`, the sum of the base changes (which are `F'`-points of `C`) of `n`
`F`-points of `C` is the base change of their sum: this is how a lift of a point of `Symⁿ C`
over `F` is transported to a bigger field. -/
theorem powMap_map {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F')
    (x : Fin n → Work.GCBasics.FPt C.toOver F) :
    Work.SymQuot.Sym.powMap C n (fun m => Work.GCBasics.RPt.map e (x m)) =
      Work.GCBasics.RPt.map e (Work.SymQuot.Sym.powMap C n x) := by
  simp only [Work.SymQuot.Sym.powMap, Work.GCBasics.RPt.map, Work.SymQuot.pi_lift_comp]
  exact Category.assoc _ _ _

theorem exists_finite_lift {K : Type u} [Field K]
    (C : Work.CurveBasics.Curve K) (n : ℕ)
    {F : Type u} [Field F] [Algebra K F] (p : Work.GCBasics.FPt (Work.SymQuot.Sym C n) F) :
    ∃ (F' : Type u) (_ : Field F') (_ : Algebra K F') (_ : Algebra F F')
      (_ : IsScalarTower K F F') (_ : FiniteDimensional F F'),
      ∃ x : Fin n → Work.GCBasics.FPt C.toOver F',
        Work.SymQuot.Sym.powMap C n x =
          Work.GCBasics.RPt.map (IsScalarTower.toAlgHom K F F') p := by
  classical
  have hsurj : Function.Surjective (Work.SymQuot.Sym.quot C n).left :=
    Work.SymQuot.Sym.quot_surjective C n
  haveI hsurjI : Surjective (Work.SymQuot.Sym.quot C n).left := ⟨hsurj⟩
  -- the fibre product `W = Cⁿ ×_{Symⁿ C} Spec F`
  let W := Limits.pullback (Work.SymQuot.Sym.quot C n).left p.left
  let f₁ : W ⟶ (Work.SymQuot.prod C.toOver n).left :=
    Limits.pullback.fst (Work.SymQuot.Sym.quot C n).left p.left
  let f₂ : W ⟶ Spec (CommRingCat.of F) :=
    Limits.pullback.snd (Work.SymQuot.Sym.quot C n).left p.left
  have hcond : f₁ ≫ (Work.SymQuot.prod C.toOver n).hom = f₂ ≫ (Work.GCBasics.specOf K F).hom := by
    dsimp only [f₁, f₂]
    rw [← Over.w (Work.SymQuot.Sym.quot C n), ← Over.w p]
    simp only [← Category.assoc, Limits.pullback.condition]
  have hpq : f₁ ≫ (Work.SymQuot.Sym.quot C n).left = f₂ ≫ p.left := by
    dsimp only [f₁, f₂]
    exact Limits.pullback.condition
  -- `W` is locally of finite type over `F`
  haveI hproper : IsProper (Work.SymQuot.prod C.toOver n).hom :=
    Work.SymQuot.Prod.isProper_prod C.toOver n
  haveI hlofq : LocallyOfFiniteType
      ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom) := by
    rw [Work.SymQuot.Sym.quot_hom C n]
    infer_instance
  haveI hsep : IsSeparated (Work.SymQuot.Sym C n).hom := Work.SymQuot.Sym.isSeparated_sym C n
  haveI hloc : LocallyOfFiniteType f₂ :=
    locallyOfFiniteType_pullback_snd_of_isSeparated (Work.SymQuot.Sym.quot C n).left p.left
      (Work.SymQuot.Sym C n).hom
  -- `W` is nonempty
  haveI : Nonempty W := by
    haveI : Surjective (Limits.pullback.snd (Work.SymQuot.Sym.quot C n).left p.left) :=
      inferInstance
    obtain ⟨z, -⟩ := (Limits.pullback.snd (Work.SymQuot.Sym.quot C n).left p.left).surjective
      (IsLocalRing.closedPoint F)
    exact ⟨z⟩
  -- `W` is Jacobson, hence has a closed point
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace f₂
  obtain ⟨w, hw⟩ : ∃ w : W, IsClosed ({w} : Set W) := by
    have hZ : closure (closedPoints W) = (⊤ : Set W) := by
      simpa using (JacobsonSpace.closure_inter_closedPoints (X := W) (Z := (⊤ : Set W))
        isClosed_univ)
    have hne : (closedPoints W).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have hbot : (⊤ : Set W) = ⊥ := by
        rw [← hZ, h, closure_empty]
        rfl
      obtain ⟨x⟩ := ‹Nonempty W›
      have h2 : x ∈ (⊥ : Set W) := hbot ▸ (show x ∈ (⊤ : Set W) from trivial)
      exact h2
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, hw⟩
  -- the residue field of the closed point, as a finite extension of `F`
  let WF : Work.GCBasics.Sch F := Over.mk f₂
  haveI hlocWF : LocallyOfFiniteType WF.hom := hloc
  let F' : Type u := Work.GCBasics.resField WF w
  have hFin : FiniteDimensional F F' :=
    Work.Charts.finiteDimensional_resField_of_isClosed (K := F) (X := WF) w hw
  letI : Algebra K F' := ((algebraMap F F').comp (algebraMap K F)).toAlgebra
  haveI hTower : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  suffices h : ∃ x : Fin n → Work.GCBasics.FPt C.toOver F',
      Work.SymQuot.Sym.powMap C n x =
        Work.GCBasics.RPt.map (IsScalarTower.toAlgHom K F F') p from
    ⟨F', inferInstance, inferInstance, inferInstance, inferInstance, hFin, h⟩
  -- the structure map `Spec F' ⟶ Spec F` induced by the residue point of `w`
  have hres : WF.left.fromSpecResidueField w ≫ f₂
      = Spec.map (CommRingCat.ofHom (algebraMap F F')) := by
    change WF.left.fromSpecResidueField w ≫ Over.hom WF
      = Spec.map (CommRingCat.ofHom (algebraMap F F'))
    rw [← Work.GCBasics.specOf_resField_hom WF w, Work.GCBasics.specOf_hom]
  -- the induced point of `Cⁿ` over `F'`
  let xl : (Work.GCBasics.specOf K F').left ⟶ (Work.SymQuot.prod C.toOver n).left :=
    WF.left.fromSpecResidueField w ≫ f₁
  have hxl : xl ≫ (Work.SymQuot.prod C.toOver n).hom = (Work.GCBasics.specOf K F').hom := by
    dsimp only [xl]
    rw [Category.assoc, hcond, ← Category.assoc, hres, Work.GCBasics.specOf_hom,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let x' : Work.GCBasics.FPt (Work.SymQuot.prod C.toOver n) F' := Over.homMk xl hxl
  have hx' : x' ≫ Work.SymQuot.Sym.quot C n
      = Work.GCBasics.RPt.map (IsScalarTower.toAlgHom K F F') p := by
    apply Over.OverMorphism.ext
    show xl ≫ (Work.SymQuot.Sym.quot C n).left
      = (Work.GCBasics.specOfMap (IsScalarTower.toAlgHom K F F')).left ≫ p.left
    rw [Work.GCBasics.specOfMap_left]
    show xl ≫ (Work.SymQuot.Sym.quot C n).left
      = Spec.map (CommRingCat.ofHom (algebraMap F F')) ≫ p.left
    dsimp only [xl]
    rw [Category.assoc, hpq, ← Category.assoc, hres]
  refine ⟨fun m => x' ≫ Work.SymQuot.proj C.toOver n m, ?_⟩
  have hlift : Limits.Pi.lift (fun m => x' ≫ Work.SymQuot.proj C.toOver n m) = x' := by
    apply Limits.Pi.hom_ext
    intro m
    rw [Limits.Pi.lift_comp_π]
    try rfl
  rw [Work.SymQuot.Sym.powMap, hlift]
  exact hx'

end Work.SymQuot.Sym
