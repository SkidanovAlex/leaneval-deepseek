/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area GenusZero
-/
import Submission.Work.GenusZero.Const

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GenusZero: rigidity of pointed maps out of a curve of genus zero

This is the headline theorem of the area: a morphism out of a curve of genus zero which is
*pointed* — it sends a fixed rational point `P0` to the origin of the abelian variety — is the
constant map.

It is an immediate consequence of `Work.GenusZero.const_of_genus_zero_hasPoint`, which is the
mathematical content (and whose proof, in `Const.lean`, is the residue-field argument of the
design: base change to `κ(z)`, the key lemma at genus zero, descent along
`Work.GenusZero.ptBaseChange_injective`, and `Work.GCBasics.hom_ext_of_resPt`).

In the notation of the challenge: for `C` a curve of genus `0`, `P0 : 𝟙_ ⟶ C.toOver`,
`A` an abelian variety and `f : C.toOver ⟶ A` with `P0 ≫ f = η[A]`,

  `f = toUnit C.toOver ≫ η[A]`.

## Main results

* `Work.GenusZero.eq_const_of_genus_zero`
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

/-- **Rigidity at genus zero.**  A pointed map from a curve of genus zero to an abelian variety
is constant: if `f` sends the rational point `P0` to the origin, then `f` is the constant map
with value the origin. -/
theorem eq_const_of_genus_zero (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) (P0 : 𝟙_ (Sch k) ⟶ C.toOver)
    {A : Sch k} [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom] [GrpObj A]
    (f : C.toOver ⟶ A) (hf : P0 ≫ f = η[A]) :
    f = toUnit C.toOver ≫ η[A] := by
  rw [const_of_genus_zero_hasPoint C hg P0 f, hf]

/-- **Rigidity at genus zero, in the shape of the challenge.**  For a curve `C` given as an
object of `Over (Spec k)` together with the two facts whose absence is bundled in
`CurveBasics.Curve` (`hred`, `hdim`, `hnt`), a pointed map to an abelian variety is
`toUnit C ≫ η[A]`.  This is the form in which the genus-zero branch of
`Work.JacFinal.jacPkgExists` consumes the area. -/
theorem eq_const_of_genus_zero_ofOver (C : Work.GenusZero.Sch k)
    [AlgebraicGeometry.SmoothOfRelativeDimension 1 C.hom]
    [AlgebraicGeometry.IsProper C.hom]
    [AlgebraicGeometry.GeometricallyIrreducible C.hom]
    (hred : AlgebraicGeometry.GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z))
    (hnt : Nontrivial C.left)
    (hg : RiemannRoch.Curve.genus (CurveBasics.Curve.ofOver C hred hdim hnt) = 0)
    (P0 : 𝟙_ (Work.GenusZero.Sch k) ⟶ C)
    {A : Work.GenusZero.Sch k} [AlgebraicGeometry.Smooth A.hom]
    [AlgebraicGeometry.IsProper A.hom] [AlgebraicGeometry.GeometricallyIrreducible A.hom]
    [GrpObj A] (f : C ⟶ A) (hf : P0 ≫ f = η[A]) :
    f = toUnit C ≫ η[A] :=
  eq_const_of_genus_zero (CurveBasics.Curve.ofOver C hred hdim hnt) hg P0 f hf

/-- **Every map from a genus-zero curve with a rational point to an abelian variety is constant,
with a unique constant.**  This is the `∃!` form of `Work.GenusZero.Rigid.isConstant_of_genus_zero`
(which is the `∃` form): the constant is `P ≫ f` for any rational point `P` of `C`, and it is
determined by `f` because `P ≫ toUnit C = 𝟙`. -/
theorem existsUnique_const_of_genus_zero (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) (hP : Nonempty (KeyLemma.Curve.Point C))
    {A : Sch k} [Smooth A.hom] [IsProper A.hom] [GeometricallyIrreducible A.hom] [GrpObj A]
    (f : C.toOver ⟶ A) : ∃! c : 𝟙_ (Sch k) ⟶ A, f = toUnit C.toOver ≫ c := by
  obtain ⟨P⟩ := hP
  refine ⟨P ≫ f, const_of_genus_zero_hasPoint C hg P f, ?_⟩
  intro c hc
  have hP0 : P ≫ toUnit C.toOver = 𝟙 (𝟙_ (Sch k)) := toUnit_unique _ _
  calc c = 𝟙 (𝟙_ (Sch k)) ≫ c := (Category.id_comp c).symm
    _ = (P ≫ toUnit C.toOver) ≫ c := by rw [hP0]
    _ = P ≫ (toUnit C.toOver ≫ c) := Category.assoc _ _ _
    _ = P ≫ f := by rw [← hc]

/-- **Rigidity at genus zero for maps into an abelian variety**, with the single hypothesis
`Work.AbVar.IsAbelianVariety A` instead of the three separate instances.  This is the form used
by area `KL` and by `Work.Universal`. -/
theorem eq_const_of_genus_zero_of_isAbelianVariety (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) (P0 : 𝟙_ (Sch k) ⟶ C.toOver)
    {A : Sch k} [Work.AbVar.IsAbelianVariety A] [GrpObj A]
    (f : C.toOver ⟶ A) (hf : P0 ≫ f = η[A]) :
    f = toUnit C.toOver ≫ η[A] :=
  eq_const_of_genus_zero C hg P0 f hf

end Work.GenusZero
