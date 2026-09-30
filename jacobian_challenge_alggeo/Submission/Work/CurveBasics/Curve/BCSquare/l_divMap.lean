/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariance of `l(D)` under base change of curves

For a base-change square `S : BCSquare C C'` of curves (so that `C'` is a model of
`C ×_k Spec F`) and a divisor `D` on `C`, the Riemann-Roch space of the pullback divisor
`S.divMap D` on `C'` has the same dimension over `F` as `C.L D` has over `k`:

  `C'.l (S.divMap D) = C.l D`.

The proof combines two inputs:

* `L_divMap`, i.e. flat base change for `H⁰(O(D))`:
  `C'.L (S.divMap D) = span_F (S.fieldMap '' C.L D)`;
* `finrank_span_image_fieldMap` below: for a `k`-subspace `V ≤ K(C)`, the `F`-span of its image
  under the `k`-linear field map `S.fieldMap` has the same dimension.  This is the
  linear-algebraic content of `linearIndependent_fieldMap`: a `k`-basis of `V` maps to an
  `F`-basis of the span, so the ranks agree.
-/
import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMapTensor
import Submission.Work.CurveBasics.Curve.BCSquare.linearIndependent_fieldMap
import Submission.Work.CurveBasics.Curve.BCSquare.L_divMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry

-- The `k`-algebra structure on the function field of a curve over `F` obtained by restriction
-- of scalars along `k → F`, registered as a local instance so that `Submodule.span k` and
-- `Submodule.span F` inside `K(C')` can be compared (`Submodule.span_span_of_tower`).
attribute [local instance] Work.CurveBasics.Curve.BCSquare.functionFieldAlgebra

universe v

/-- **Base change of a subspace of the function field.**

For a base-change square `S : BCSquare C C'` and a `k`-subspace `V ≤ K(C)`, the `F`-span of
the image of `V` under the `k`-linear map `S.fieldMap` has the same dimension as `V`: a
`k`-basis `(v i)` of `V` maps to an `F`-linearly independent family
(`linearIndependentFieldMap`) spanning the image, hence the two ranks agree. -/
theorem finrank_span_image_fieldMap {k : Type v} [Field k] {F : Type v} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (V : Submodule k C.functionField) :
    Module.finrank F ↥(Submodule.span F (S.fieldMap.hom '' (V : Set C.functionField)))
      = Module.finrank k ↥V := by
  classical
  -- `S.fieldMap.hom` is `k`-linear: it is an algebra homomorphism for the two `k`-structures
  have hφmap : ∀ c : k, S.fieldMap.hom (algebraMap k C.functionField c)
      = algebraMap k C'.functionField c := fun c =>
    (fieldMap_algebraMap S c).trans (functionFieldAlgebra_algebraMap c).symm
  let φa : C.functionField →ₐ[k] C'.functionField :=
    { toRingHom := S.fieldMap.hom, commutes' := hφmap }
  -- a `k`-basis of `V`, pushed into `K(C)`
  set ι := Module.Free.ChooseBasisIndex k ↥V with hι
  let b : Module.Basis ι k ↥V := Module.Free.chooseBasis k ↥V
  let v : ι → C.functionField := fun i => (b i : C.functionField)
  have hv_li : LinearIndependent k v :=
    b.linearIndependent.map' (Submodule.subtype V) (Submodule.ker_subtype V)
  have hv_inj : Function.Injective v := hv_li.injective
  have hspan : Submodule.span k (Set.range v) = V := by
    have h1 : Set.range v = Submodule.subtype V '' (Set.range b) := by
      ext x; constructor
      · rintro ⟨i, rfl⟩; exact ⟨b i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  -- the `F`-span of the image is the `F`-span of the image of the basis
  have hspanF : Submodule.span F (S.fieldMap.hom '' (V : Set C.functionField))
      = Submodule.span F (Set.range (fun i => S.fieldMap.hom (v i))) := by
    have hmap : Submodule.map φa.toLinearMap V
        = Submodule.span k (Set.range (fun i => S.fieldMap.hom (v i))) := by
      rw [← hspan, Submodule.map_span]
      congr 1
      ext y; constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨v i, ⟨i, rfl⟩, rfl⟩
    have hcoe : S.fieldMap.hom '' (V : Set C.functionField)
        = ⇑φa.toLinearMap '' (V : Set C.functionField) := rfl
    rw [hcoe, ← Submodule.map_coe, hmap,
      Submodule.span_span_of_tower k F (Set.range (fun i => S.fieldMap.hom (v i)))]
  -- a `k`-basis maps to an `F`-linearly independent family
  have hliF : LinearIndependent F (fun i => S.fieldMap.hom (v i)) :=
    linearIndependent_fieldMap S hv_li
  have hliF_inj : Function.Injective (fun i => S.fieldMap.hom (v i)) := hliF.injective
  -- the two ranks agree
  have hcard : Cardinal.mk (Set.range (fun i => S.fieldMap.hom (v i)))
      = Cardinal.mk (Set.range v) := by
    refine Cardinal.lift_inj.mp ?_
    rw [Cardinal.mk_range_eq_of_injective hliF_inj, Cardinal.mk_range_eq_of_injective hv_inj]
  have h1 : Module.rank F ↥(Submodule.span F (Set.range (fun i => S.fieldMap.hom (v i))))
      = Cardinal.mk (Set.range (fun i => S.fieldMap.hom (v i))) := rank_span hliF
  have h2 : Module.rank k ↥V = Cardinal.mk (Set.range v) := by
    rw [← hspan]; exact rank_span hv_li
  show (Module.rank F ↥(Submodule.span F (S.fieldMap.hom '' (V : Set C.functionField)))).toNat
      = (Module.rank k ↥V).toNat
  rw [hspanF, h1, h2, hcard]

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem l_divMap {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (D : Curve.Div C) :
    C'.l (S.divMap D) = C.l D := by
  -- flat base change for `H⁰` identifies the two Riemann-Roch spaces up to the `F`-span
  rw [Curve.l, Curve.l, L_divMap S D]
  -- and the `F`-span of the image of `L D` has the same dimension as `L D`
  exact finrank_span_image_fieldMap S (C.L D)

end Work.CurveBasics.Curve.BCSquare
