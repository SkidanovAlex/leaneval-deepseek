import Mathlib
import Submission.Work.SymQuot.SymGeomOfComplete
import Submission.Work.SymQuot.DivBaseInst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# The `0`-th symmetric power: `SymGeom C 0` is inhabited

`Work.SpecLin.SymGeom C n` is the interface through which area `PR` consumes the symmetric
power `Symⁿ C`: the scheme `Symⁿ C`, the divisor `divOf` of a point of `Symⁿ C` (a bijection
onto the effective divisors of degree `n`), the sum map `powMap`, base change compatibility
and the splitting of effective divisors over algebraically closed extensions.

For `n ≠ 0` the instance is `Work.SymQuot.symGeomOfComplete` (`SymGeomOfComplete.lean`), which
needs `divOf_complete` and `[NeZero n]`.  This file supplies the missing case `n = 0`.

## Mathematics

`Sym⁰ C = C⁰/S₀` is the point `Spec K`: the `0`-fold product `C⁰ = ∏_{∅} C` is the terminal
object of `Sch K`, and the action of the trivial group on it is trivial, so the quotient is
again terminal.  Concretely (`prodZeroPt_quot`), the quotient map

`Work.SymQuot.Sym.quot C 0 : C⁰ ⟶ Sym⁰ C`

is an isomorphism: it has the section `prodZeroPt : Sym⁰ C ⟶ C⁰` (the unique morphism into the
empty product) and any *endomorphism* of the empty product is the identity, so both composites
`quot ≫ prodZeroPt` and `prodZeroPt ≫ quot` are endomorphisms of the empty product; the first is
one by the universal property of the product, and the second forces `quot` to be an isomorphism
through the uniqueness in the universal property of the quotient (`Sym.desc`).

Consequently every hom-set into `Sym⁰ C` is a subsingleton (`subsingleton_hom_sym_zero`), which
is exactly what is needed to *define* `divOf` on `Sym⁰ C` (the only effective divisor of degree
`0` is `0`, so the constant divisor `0` is a bijection): the instance `symGeom_zero_of` below.

The `SymGeom` interface does not pin `S` to a particular scheme, but the instance produced here
uses `S = Sym⁰ C` itself, so that it is definitionally the same choice as `symGeomOfComplete`.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonoidalCategory

universe u

namespace Work.SymQuot.Sym

section ZeroProduct

variable {K : Type u} [Field K]

/-- **Every two morphisms into the empty product `prod X 0` are equal**: the functoriality
condition of `Pi.lift` is vacuous when the index type is empty. -/
theorem subsingleton_hom_prod_zero (X Y : Work.GCBasics.Sch K) :
    Subsingleton (Y ⟶ Work.SymQuot.prod X 0) :=
  ⟨fun f g => Limits.Pi.hom_ext f g (fun i => Fin.elim0 i)⟩

/-- The canonical morphism `Y ⟶ prod X 0` into the empty product (the lift of the empty
family of morphisms). -/
noncomputable def prodZeroPt (X Y : Work.GCBasics.Sch K) :
    Y ⟶ Work.SymQuot.prod X 0 :=
  Limits.Pi.lift (fun i : Fin 0 => Fin.elim0 i)

end ZeroProduct

section SymZero

variable {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C]

/-- Any endomorphism of the empty product `prod C.toOver 0` is the identity: it is equal to the
identity because morphisms into the empty product are unique. -/
theorem permIso_hom_eq_id_zero (σ : Equiv.Perm (Fin 0)) :
    (Work.SymQuot.permIso C.toOver σ).hom = 𝟙 (Work.SymQuot.prod C.toOver 0) :=
  (subsingleton_hom_prod_zero (K := K) C.toOver (Work.SymQuot.prod C.toOver 0)).allEq _ _

/-- The quotient map `C⁰ ⟶ Sym⁰ C` is invariant under the `S₀`-action: the action on the
`0`-fold product is by endomorphisms of the empty product, hence trivial. -/
theorem quot_zero_invariance (σ : ULift.{u} (Equiv.Perm (Fin 0))) :
    (Work.SymQuot.symAction C 0).hom σ ≫ (Work.SymQuot.Sym.quot C 0).left =
      (Work.SymQuot.Sym.quot C 0).left := by
  have h : (Work.SymQuot.permIso C.toOver σ.down).hom = 𝟙 (Work.SymQuot.prod C.toOver 0) :=
    permIso_hom_eq_id_zero C σ.down
  have h' : (Work.SymQuot.permIso C.toOver σ.down).hom.left =
      𝟙 (Work.SymQuot.prod C.toOver 0).left := by
    rw [h, CategoryTheory.Over.id_left]
  rw [Work.SymQuot.symAction_hom]
  change (Work.SymQuot.permIso C.toOver σ.down).hom.left ≫
    (Work.SymQuot.Sym.quot C 0).left = (Work.SymQuot.Sym.quot C 0).left
  rw [h', Category.id_comp]

/-- **The quotient map `C⁰ ⟶ Sym⁰ C` is split by the projection `Sym⁰ C ⟶ C⁰`.**

Both composites of `quot` with `prodZeroPt` are endomorphisms of the empty product; one is
the identity by the uniqueness of morphisms into the empty product, and the other follows from
the uniqueness part of the universal property of the quotient (`Sym.desc`), applied to
`Sym.quot` itself. -/
theorem prodZeroPt_quot :
    prodZeroPt (K := K) C.toOver (Work.SymQuot.Sym C 0) ≫ Work.SymQuot.Sym.quot C 0 =
      𝟙 (Work.SymQuot.Sym C 0) := by
  obtain ⟨g, _hg, huniq⟩ := Work.SymQuot.Sym.desc C 0 (Work.SymQuot.Sym.quot C 0)
    (fun σ => quot_zero_invariance C σ)
  have h2 : Work.SymQuot.Sym.quot C 0 ≫
      prodZeroPt (K := K) C.toOver (Work.SymQuot.Sym C 0) =
      𝟙 (Work.SymQuot.prod C.toOver 0) :=
    Limits.Pi.hom_ext _ _ (fun i => Fin.elim0 i)
  have h1 : Work.SymQuot.Sym.quot C 0 ≫
      (prodZeroPt (K := K) C.toOver (Work.SymQuot.Sym C 0) ≫ Work.SymQuot.Sym.quot C 0) =
      Work.SymQuot.Sym.quot C 0 := by
    rw [← Category.assoc, h2, Category.id_comp]
  exact (huniq _ h1).trans (huniq _ (Category.comp_id _)).symm

/-- **`Sym⁰ C` is the point `C⁰ = Spec K`**: the quotient map `C⁰ ⟶ Sym⁰ C` is an
isomorphism, with inverse the unique morphism `Sym⁰ C ⟶ C⁰` into the empty product. -/
noncomputable def symZeroIso : Work.SymQuot.prod C.toOver 0 ≅ Work.SymQuot.Sym C 0 where
  hom := Work.SymQuot.Sym.quot C 0
  inv := prodZeroPt (K := K) C.toOver (Work.SymQuot.Sym C 0)
  hom_inv_id := Limits.Pi.hom_ext _ _ (fun i => Fin.elim0 i)
  inv_hom_id := prodZeroPt_quot C

/-- Every hom-set into `Sym⁰ C` is a subsingleton: `Sym⁰ C` is the point `Spec K`. -/
theorem subsingleton_hom_sym_zero (Y : Work.GCBasics.Sch K) :
    Subsingleton (Y ⟶ Work.SymQuot.Sym C 0) := by
  haveI : Subsingleton (Y ⟶ Work.SymQuot.prod C.toOver 0) :=
    subsingleton_hom_prod_zero (K := K) C.toOver Y
  refine ⟨fun f g => ?_⟩
  have h1 : f ≫ (symZeroIso C).inv = g ≫ (symZeroIso C).inv := Subsingleton.elim _ _
  calc f = f ≫ (symZeroIso C).inv ≫ (symZeroIso C).hom := by
        rw [Iso.inv_hom_id, Category.comp_id]
    _ = (f ≫ (symZeroIso C).inv) ≫ (symZeroIso C).hom := (Category.assoc _ _ _).symm
    _ = (g ≫ (symZeroIso C).inv) ≫ (symZeroIso C).hom := by rw [h1]
    _ = g ≫ (symZeroIso C).inv ≫ (symZeroIso C).hom := Category.assoc _ _ _
    _ = g := by rw [Iso.inv_hom_id, Category.comp_id]

/-- The canonical point `Y ⟶ Sym⁰ C` (every scheme maps to `Sym⁰ C = Spec K` in a unique
way). -/
noncomputable def symZeroPt (Y : Work.GCBasics.Sch K) : Y ⟶ Work.SymQuot.Sym C 0 :=
  prodZeroPt (K := K) C.toOver Y ≫ Work.SymQuot.Sym.quot C 0

end SymZero

open CategoryTheory Limits AlgebraicGeometry in
theorem symGeom_zero {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [Work.SymQuot.CurveAffineCover C] : Nonempty (Work.SpecLin.SymGeom C 0) := by
  classical
  refine ⟨{ S := Work.SymQuot.Sym C 0
            isProper := Work.SymQuot.Sym.isProper_sym C 0
            divOf := ?_
            divOf_injective := ?_
            divOf_isEffective := ?_
            divOf_deg := ?_
            divOf_complete := ?_
            divOf_map := ?_
            powMap := ?_
            powMap_comp := ?_
            divOf_powMap := ?_
            split := ?_ }⟩
  · -- the only divisor of degree `0` is `0`, so `divOf` is the constant divisor `0`
    exact fun {F : Type u} [Field F] [Algebra K F]
      (_ : Work.SpecLin.FPt (Work.SymQuot.Sym C 0) F) => (0 : Work.SpecLin.Dv C F)
  · exact fun {F : Type u} [Field F] [Algebra K F]
      (p q : Work.SpecLin.FPt (Work.SymQuot.Sym C 0) F) _ => by
      haveI : Subsingleton (Work.SpecLin.FPt (Work.SymQuot.Sym C 0) F) :=
        subsingleton_hom_sym_zero C (Work.SpecLin.specOf (K := K) F)
      exact Subsingleton.elim p q
  · exact fun {F : Type u} [Field F] [Algebra K F]
      (_ : Work.SpecLin.FPt (Work.SymQuot.Sym C 0) F) =>
      Work.CurveBasics.Curve.Div.isEffective_zero
  · exact fun {F : Type u} [Field F] [Algebra K F]
      (_ : Work.SpecLin.FPt (Work.SymQuot.Sym C 0) F) =>
      Work.CurveBasics.Curve.deg_zero (C.baseChange F)
  · exact fun {F : Type u} [Field F] [Algebra K F] (D : Work.SpecLin.Dv C F)
      (hD : D.IsEffective) (hdeg : (C.baseChange F).deg D = (0 : ℤ)) => by
      have hD0 : D = 0 :=
        (Work.CurveBasics.Divisor.deg_eq_zero_iff (C := C.baseChange F) hD).mp hdeg
      exact ⟨symZeroPt C (Work.SpecLin.specOf (K := K) F), by rw [hD0]⟩
  · exact fun {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
      (e : F →ₐ[K] F') (_ : Work.SpecLin.FPt (Work.SymQuot.Sym C 0) F) => by
      rw [Work.SpecLin.DivBase.bc_zero]
  · exact fun {T : Work.GCBasics.Sch K} (_ : Fin 0 → (T ⟶ C.toOver)) => symZeroPt C T
  · exact fun {T T' : Work.GCBasics.Sch K} (_ : T' ⟶ T) (_ : Fin 0 → (T ⟶ C.toOver)) => by
      haveI : Subsingleton (T' ⟶ Work.SymQuot.Sym C 0) := subsingleton_hom_sym_zero C T'
      exact Subsingleton.elim _ _
  · exact fun {F : Type u} [Field F] [Algebra K F] (x : Fin 0 → Work.SpecLin.CurveFPt C F) => by
      simp
  · exact fun {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
      [Algebra F F'] [IsScalarTower K F F'] [IsAlgClosed F']
      (D : Work.SpecLin.Dv C F) (hD : D.IsEffective)
      (hdeg : (C.baseChange F).deg D = (0 : ℤ)) => by
      have hD0 : D = 0 :=
        (Work.CurveBasics.Divisor.deg_eq_zero_iff (C := C.baseChange F) hD).mp hdeg
      refine ⟨fun m : Fin 0 => Fin.elim0 m, ?_⟩
      rw [hD0, Work.SpecLin.DivBase.bc_zero]
      simp

end Work.SymQuot.Sym
