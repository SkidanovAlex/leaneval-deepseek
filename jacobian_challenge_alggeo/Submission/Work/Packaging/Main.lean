/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area P (packaging)
-/
import Mathlib
import Submission.Work.Packaging.Basic
import Submission.Work.Packaging.Curve
import Submission.Work.Packaging.Univ
import Submission.Work.Packaging.Trivial
import Submission.Work.Packaging.Data
import Submission.Work.Packaging.RelDimUniq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Area P: the definitions and theorems of the challenge

This file mirrors, one for one, the definitions and theorems of the challenge
(`AlgebraicGeometry.JacobianChallenge`), with one extra argument: a proof
`hEx : ∀ P0, Nonempty (JacPkg C P0)` of the existence of a Jacobian package for every `k`-point of
`C`. That proof is the single remaining input of the whole area; everything else here is proved.

The bridge `Submission.lean` only has to supply `hEx` and copy these declarations:

```
def genus (C : Over (Spec (.of k))) [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] : ℕ := Work.Packaging.Main.genus C hEx
def Jacobian ... := Work.Packaging.Main.Jacobian C hEx
instance instGrpObj : GrpObj (Jacobian C) := Work.Packaging.Main.instGrpObj C hEx
instance smoothOfRelativeDimension_genus :
    SmoothOfRelativeDimension (genus C) (Jacobian C).hom :=
  Work.Packaging.Main.smoothOfRelativeDimension_genus C hEx
instance instIsProper : IsProper (Jacobian C).hom := Work.Packaging.Main.instIsProper C hEx
instance instGeometricallyIrreducible : GeometricallyIrreducible (Jacobian C).hom :=
  Work.Packaging.Main.instGeometricallyIrreducible C hEx
def ofCurve (P : 𝟙_ _ ⟶ C) : C ⟶ Jacobian C := Work.Packaging.Main.ofCurve C hEx P
theorem comp_ofCurve ... := Work.Packaging.Main.comp_ofCurve C hEx P
theorem exists_unique_ofCurve_comp ... :=
  Work.Packaging.Main.exists_unique_ofCurve_comp C hEx P f hf
```
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped MonObj
open Classical

namespace Work.Packaging.Main

variable {k : Type u} [Field k]

/-- The Jacobian of `C`: the group scheme of a Jacobian package based at a `k`-point of `C`, or the
trivial group scheme if `C` has no `k`-point. -/
@[reducible] noncomputable def Jacobian (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0)) : Over (Spec (.of k)) :=
  (jacData C hEx).J

/-- The genus of `C`, read off its Jacobian as a relative dimension. -/
@[reducible] noncomputable def genus (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0)) : ℕ :=
  (jacData C hEx).dim

/-- The group scheme structure on the Jacobian. -/
noncomputable def instGrpObj (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0)) :
    GrpObj (Jacobian C hEx) :=
  (jacData C hEx).instGrpObj

/-- The Jacobian is proper over `Spec k`. -/
theorem instIsProper (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0)) :
    IsProper (Jacobian C hEx).hom :=
  (jacData C hEx).instIsProper

/-- The Jacobian is geometrically irreducible over `Spec k`. -/
theorem instGeometricallyIrreducible (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0)) :
    GeometricallyIrreducible (Jacobian C hEx).hom :=
  (jacData C hEx).instGeomIrred

/-- The Jacobian is smooth over `Spec k` of relative dimension the genus of `C`. -/
theorem smoothOfRelativeDimension_genus (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0)) :
    SmoothOfRelativeDimension (genus C hEx) (Jacobian C hEx).hom :=
  (jacData C hEx).instDim

/-- The Abel–Jacobi map from `C` to its Jacobian, based at the `k`-point `P` of `C`. -/
noncomputable def ofCurve (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0))
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) : C ⟶ Jacobian C hEx :=
  (jacData C hEx).AJ ≫
    (GrpObj.mulRight (A := (jacData C hEx).J) (P ≫ (jacData C hEx).AJ)⁻¹).hom

/-- The Abel–Jacobi map sends the base point to the origin. -/
theorem comp_ofCurve (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0))
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    P ≫ ofCurve C hEx P = η[Jacobian C hEx] := by
  by_cases h : Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ C)
  · unfold ofCurve Jacobian jacData
    rw [dite_eq_left h]
    exact Work.Packaging.comp_ofCurve (Classical.choice (hEx (Classical.choice h))) P
  · exact absurd ⟨P⟩ h

/-- The universal property of the Jacobian, in the stronger form where `f` is *not* assumed to send
the base point to the origin (the pointed case follows since `P ≫ ofCurve P = η`). -/
theorem exists_unique_factor_ofCurve (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0))
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) {A : Over (Spec (.of k))} [Smooth A.hom]
    [IsProper A.hom] [GrpObj A] [GeometricallyIrreducible A.hom] (f : C ⟶ A) :
    ∃! g : Jacobian C hEx ⟶ A, f = ofCurve C hEx P ≫ g := by
  by_cases h : Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ C)
  · unfold ofCurve Jacobian jacData
    rw [dite_eq_left h]
    exact Work.Packaging.exists_unique_factor_ofCurve (Classical.choice (hEx (Classical.choice h))) P f
  · exact absurd ⟨P⟩ h

/-- The genus of the Jacobian is the unique relative dimension of `Jacobian C` over `Spec k`. -/
theorem genus_eq (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0))
    (n : ℕ) [SmoothOfRelativeDimension n (Jacobian C hEx).hom] : genus C hEx = n := by
  by_cases h : Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ C)
  · have hJ : Jacobian C hEx = (Classical.choice (hEx (Classical.choice h))).J := by
      unfold Jacobian jacData
      rw [dite_eq_left h]
      rfl
    have hg : genus C hEx = RelDim.genusOf (Classical.choice (hEx (Classical.choice h))) := by
      unfold genus jacData
      rw [dite_eq_left h]
      rfl
    rw [hg]
    haveI hn : SmoothOfRelativeDimension n
        (Classical.choice (hEx (Classical.choice h))).J.hom :=
      hJ ▸ ‹SmoothOfRelativeDimension n (Jacobian C hEx).hom›
    exact RelDim.genusOf_eq _ n
  · have hJ : Jacobian C hEx = 𝟙_ (Over (Spec (.of k))) := by
      unfold Jacobian jacData
      rw [dite_eq_right h]
      rfl
    have hg : genus C hEx = 0 := by
      unfold genus jacData
      rw [dite_eq_right h]
      rfl
    rw [hg]
    haveI hn : SmoothOfRelativeDimension n (𝟙_ (Over (Spec (.of k)))).hom :=
      hJ ▸ ‹SmoothOfRelativeDimension n (Jacobian C hEx).hom›
    haveI : SmoothOfRelativeDimension 0 (𝟙_ (Over (Spec (.of k)))).hom :=
      Trivial.instSmoothOfRelativeDimensionUnit
    exact RelDim.smoothOfRelativeDimension_unique (𝟙_ (Over (Spec (.of k)))).hom 0 n

/-- The universal property of the Jacobian. -/
theorem exists_unique_ofCurve_comp (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0))
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) {A : Over (Spec (.of k))} [Smooth A.hom]
    [IsProper A.hom] [GrpObj A] [GeometricallyIrreducible A.hom] (f : C ⟶ A)
    (hf : P ≫ f = η[A]) :
    ∃! g : Jacobian C hEx ⟶ A, f = ofCurve C hEx P ≫ g := by
  by_cases h : Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ C)
  · unfold ofCurve Jacobian jacData
    rw [dite_eq_left h]
    exact Work.Packaging.exists_unique_ofCurve_comp (Classical.choice (hEx (Classical.choice h))) P f hf
  · exact absurd ⟨P⟩ h

end Work.Packaging.Main
