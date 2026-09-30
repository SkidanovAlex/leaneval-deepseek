/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area GenusZero
-/
import Submission.Work.GenusZero.Principal
import Submission.Work.GenusZero.PointDiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GenusZero: rigidity — a curve of genus zero has no non-constant maps to an abelian variety

This file contains the mathematical heart of the area: **a morphism from a curve of genus zero
which has a rational point to an abelian variety is constant**.

The argument has three steps.

1. *The key lemma at genus zero over a field extension*
   (`point_sum_eq_of_genus_zero_baseChange`).  Let `x`, `y` be two `F`-points of `C_F`.  By
   `Work.GenusZero.principal_of_deg_zero` (genus zero ⇒ degree zero ⇒ principal) applied to the
   degree-zero divisor `[x] - [y]` on `C_F` — `Work.GenusZero.deg_toDiv_single_one` gives
   `deg [x] = deg [y] = 1` — there is a nonzero rational function `h` on `C_F` with
   `div h = [x] - [y]`.  The key lemma `KL` (`Work.KeyLemma.Curve.sumOfPoints_eq_of_linEquiv_uncond`,
   unconditional over any field) then gives `x ≫ f_F = y ≫ f_F` in the commutative group
   `A_F(F)`.

2. *The passage to the base field* (`resPt_eq_toUnit_comp`, then
   `const_of_genus_zero_hasPoint`).  Two morphisms out of the reduced scheme `C` which agree on
   every residue-field point agree (`Work.GCBasics.hom_ext_of_resPt`).  For a point `z` of `C`
   we compare `x := resPt C z` with the *constant* point
   `y := toUnit (specOf k κ(z)) ≫ P` at a rational point `P` of `C`.  Base changing both to
   `κ(z)` and using step 1 gives an equality of the two points of `A_{κ(z)}`;
   `Work.GenusZero.ptBaseChange_injective` descends it to `x ≫ f = y ≫ f`, which is
   `resPt C z ≫ f = resPt C z ≫ (toUnit C ≫ (P ≫ f))`.

3. The corollaries `const_of_genus_zero_baseChange` (step 2 applied to `C_F` over `F`) and
   `point_sum_eq_of_genus_zero`.

## Main results

* `Work.GenusZero.point_sum_eq_of_genus_zero_baseChange`
* `Work.GenusZero.resPt_eq_toUnit_comp`
* `Work.GenusZero.const_of_genus_zero_hasPoint` — **rigidity**
* `Work.GenusZero.const_of_genus_zero_baseChange`
* `Work.GenusZero.point_sum_eq_of_genus_zero`
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

universe u

namespace Work.GenusZero

variable {k : Type u} [Field k]

/-- **The key lemma at genus zero, over a field extension.**  On a curve of genus zero any two
`F`-points have the same image in a proper commutative group scheme, for the group structure of
the base change `A_F`.

The proof is `Work.GenusZero.principal_of_deg_zero` applied to the degree-zero divisor
`[x] - [y]` of `C_F`, followed by the key lemma of area `KL`. -/
theorem point_sum_eq_of_genus_zero_baseChange (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) (F : Type u) [Field F] [Algebra k F]
    {A : Sch k} [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom] [GrpObj A]
    (f : C.toOver ⟶ A) (x y : KeyLemma.Curve.Point (C.baseChange F)) :
    x ≫ (bcFun F).map f = y ≫ (bcFun F).map f := by
  have hgF : RiemannRoch.Curve.genus (C.baseChange F) = 0 := by
    rw [genus_baseChange C F, hg]
  have hdeg : (C.baseChange F).deg
      (KeyLemma.Curve.SumDiv.toDiv (C.baseChange F) (Finsupp.single x 1) -
        KeyLemma.Curve.SumDiv.toDiv (C.baseChange F) (Finsupp.single y 1)) = 0 := by
    rw [CurveBasics.Curve.deg_sub, deg_toDiv_single_one, deg_toDiv_single_one, sub_self]
  obtain ⟨h, hh, hdiv⟩ := principal_of_deg_zero (C.baseChange F) hgF _ hdeg
  have key := KeyLemma.Curve.sumOfPoints_eq_of_linEquiv_uncond (C.baseChange F)
    ((bcFun F).map f) hh hdiv
  rw [← KeyLemma.Curve.SumDiv.sumOfPoints_single_one (C.baseChange F) ((bcFun F).map f) x,
    ← KeyLemma.Curve.SumDiv.sumOfPoints_single_one (C.baseChange F) ((bcFun F).map f) y]
  exact key

/-- The residue-field step of rigidity: an `F`-point `x` of `C` over `Spec k` and the constant
point at a rational point `P` have the same image in an abelian variety. -/
theorem resPt_eq_toUnit_comp (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) (P : KeyLemma.Curve.Point C)
    {A : Sch k} [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom] [GrpObj A]
    (f : C.toOver ⟶ A) (F : Type u) [Field F] [Algebra k F]
    (x : Work.GCBasics.specOf k F ⟶ C.toOver) :
    x ≫ f = (toUnit (Work.GCBasics.specOf k F) ≫ P) ≫ f := by
  apply ptBaseChange_injective (k := k) (F := F) A
  rw [ptBaseChange_comp, ptBaseChange_comp]
  exact point_sum_eq_of_genus_zero_baseChange C hg F f
    (ptBaseChange F C.toOver x)
    (ptBaseChange F C.toOver (toUnit (Work.GCBasics.specOf k F) ≫ P))

/-- **Rigidity at genus zero.**  A morphism from a curve of genus zero with a rational point `P`
to an abelian variety is constant: `f = toUnit C ≫ (P ≫ f)`.

For every residue-field point `z` of `C` we base change to `κ(z)` and apply the key lemma at
genus zero to compare `resPt C z` with the constant point at `P`; the equality descends by
`ptBaseChange_injective`; finally `hom_ext_of_resPt` concludes, the source `C` being reduced and
the target separated. -/
theorem const_of_genus_zero_hasPoint (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) (P : KeyLemma.Curve.Point C)
    {A : Sch k} [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom] [GrpObj A]
    (f : C.toOver ⟶ A) : f = toUnit C.toOver ≫ (P ≫ f) := by
  refine Work.GCBasics.hom_ext_of_resPt f (toUnit C.toOver ≫ (P ≫ f)) fun z => ?_
  -- The residue field of a point carries two `k`-algebra structures in this workspace
  -- (`Work.GCBasics.resFieldAlgebra` and `Work.CurveBasics.Curve.Place.instAlgebraResidueField`,
  -- which agree mathematically but not definitionally).  `resPt` uses the former, so we pin it
  -- locally to make the two sides of `hgoal` below live in the same `specOf`.
  letI : Algebra k (Work.GCBasics.resField C.toOver z) := Work.GCBasics.resFieldAlgebra C.toOver z
  have key := resPt_eq_toUnit_comp C hg P f (Work.GCBasics.resField C.toOver z)
    (Work.GCBasics.resPt C.toOver z)
  have hgoal : Work.GCBasics.resPt C.toOver z ≫ (toUnit C.toOver ≫ (P ≫ f)) =
      (toUnit (Work.GCBasics.specOf k (Work.GCBasics.resField C.toOver z)) ≫ P) ≫ f := by
    rw [← Category.assoc (Work.GCBasics.resPt C.toOver z) (toUnit C.toOver) (P ≫ f),
      toUnit_unique (Work.GCBasics.resPt C.toOver z ≫ toUnit C.toOver)
        (toUnit (Work.GCBasics.specOf k (Work.GCBasics.resField C.toOver z))),
      ← Category.assoc (toUnit (Work.GCBasics.specOf k (Work.GCBasics.resField C.toOver z))) P f]
  rw [hgoal]
  exact key

/-- The base-changed form of rigidity at genus zero: for a field extension `F/k` and an `F`-point
`P` of `C_F`, the base change of `f` to `C_F` is constant with value `P ≫ f_F`. -/
theorem const_of_genus_zero_baseChange (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) (F : Type u) [Field F] [Algebra k F]
    {A : Sch k} [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom] [GrpObj A]
    (f : C.toOver ⟶ A) (P : KeyLemma.Curve.Point (C.baseChange F)) :
    (bcFun F).map f = toUnit (C.baseChange F).toOver ≫ (P ≫ (bcFun F).map f) :=
  const_of_genus_zero_hasPoint (C.baseChange F) (by rw [genus_baseChange C F, hg]) P
    ((bcFun F).map f)

/-- **Rigidity at genus zero, point form**: on a curve of genus zero any two rational points have
the same image in a proper commutative group scheme over the base field. -/
theorem point_sum_eq_of_genus_zero (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0)
    {A : Sch k} [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom] [GrpObj A]
    (f : C.toOver ⟶ A) (x y : KeyLemma.Curve.Point C) : x ≫ f = y ≫ f := by
  haveI : Work.AbVar.IsAbelianVariety A := ⟨inferInstance, inferInstance, inferInstance⟩
  haveI : IsCommMonObj A := Work.AbVar.isCommMonObj_of_isAbelianVariety _
  have hdeg : C.deg (KeyLemma.Curve.SumDiv.toDiv C (Finsupp.single x 1) -
      KeyLemma.Curve.SumDiv.toDiv C (Finsupp.single y 1)) = 0 := by
    rw [CurveBasics.Curve.deg_sub, deg_toDiv_single_one, deg_toDiv_single_one, sub_self]
  obtain ⟨h, hh, hdiv⟩ := principal_of_deg_zero C hg _ hdeg
  have key := KeyLemma.Curve.sumOfPoints_eq_of_linEquiv_uncond C f hh hdiv
  rw [← KeyLemma.Curve.SumDiv.sumOfPoints_single_one C f x,
    ← KeyLemma.Curve.SumDiv.sumOfPoints_single_one C f y]
  exact key

/-- **The sum of the images of a multiset of points at genus zero depends only on the number of
points.**  For `s`, `t` multisets of `k`-points of a genus-zero curve with the same number of
points, the products of the images in a proper commutative group scheme agree.

The difference `toDiv s - toDiv t` has degree `deg s - deg t = 0`
(`Work.KeyLemma.Sum.deg_toDiv`), hence is principal by `Work.GenusZero.principal_of_deg_zero`,
and the key lemma of area `KL` concludes. -/
theorem sumOfPoints_eq_of_genus_zero (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0)
    {A : Sch k} [GrpObj A] [IsProper A.hom] [IsCommMonObj A]
    (f : C.toOver ⟶ A) (s t : KeyLemma.Curve.SumDiv C)
    (h : KeyLemma.Curve.SumDiv.deg s = KeyLemma.Curve.SumDiv.deg t) :
    KeyLemma.Curve.SumDiv.sumOfPoints C f s = KeyLemma.Curve.SumDiv.sumOfPoints C f t := by
  have hdeg : C.deg (KeyLemma.Curve.SumDiv.toDiv C s - KeyLemma.Curve.SumDiv.toDiv C t) = 0 := by
    rw [CurveBasics.Curve.deg_sub, Work.KeyLemma.Sum.deg_toDiv, Work.KeyLemma.Sum.deg_toDiv,
      h, sub_self]
  obtain ⟨h, hh, hdiv⟩ := principal_of_deg_zero C hg _ hdeg
  exact KeyLemma.Curve.sumOfPoints_eq_of_linEquiv_uncond C f hh hdiv

/-- **Rigidity at genus zero, for maps into an abelian variety**, from the single hypothesis
`Work.AbVar.IsAbelianVariety A`. -/
theorem const_of_genus_zero_hasPoint_of_isAbelianVariety (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) (P : KeyLemma.Curve.Point C)
    {A : Sch k} [Work.AbVar.IsAbelianVariety A] [GrpObj A]
    (f : C.toOver ⟶ A) : f = toUnit C.toOver ≫ (P ≫ f) :=
  const_of_genus_zero_hasPoint C hg P f

end Work.GenusZero
