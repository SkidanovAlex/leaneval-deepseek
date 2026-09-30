/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Submission.Helpers
import Submission.Work.Packaging.Main
import Submission.Work.JacClose.All
import Submission.Work.CurveFacts.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Jacobians in algebraic geometry

Christian Merten's algebraic-geometry analogue of Kevin Buzzard's Jacobian
challenge, posted to leanprover Zulip:
<https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge/near/587802685>.

In the following, by a smooth curve we mean a geometrically irreducible, smooth scheme of relative
dimension one over a field.

## Main missing definitions

* `AlgebraicGeometry.JacobianChallenge.genus` -- genus of a proper, smooth curve
* `AlgebraicGeometry.JacobianChallenge.Jacobian` -- the Jacobian of a proper, smooth curve
* `AlgebraicGeometry.JacobianChallenge.Jacobian.ofCurve` -- the Abel-Jacobi map from a proper smooth
  curve to its Jacobian

## Main missing theorems

* `Jacobian.smoothOfRelativeDimension_genus` -- The Jacobian of a proper, smooth curve `C` is smooth
  of relative dimension `g`, where `g` is the genus of `C`.
* `Jacobian.exists_unique_ofCurve_comp` -- the universal property of the Jacobian of a proper,
  smooth curve.

## Structure of this file

Everything is reduced to a single input, `jacPkgExists` below: a Jacobian package
`Work.Packaging.JacPkg C P0` for every `k`-point `P0` of `C` (areas GC/UP of the blueprint).  The
nine holes of the challenge are then filled by the definitions and theorems of
`Submission.Work.Packaging.Main` (area P), which carries out the packaging, the reduction of the
universal property from `P0` to an arbitrary base point `P`, and the trivial (no `k`-point) branch.

`jacPkgExists` is proved by area `Submission.Work.JacClose` (the closure chapter):
`Work.JacClose.jacPkgExists'` splits at genus zero (area `GenusZero`, see
`Submission/Work/NOTES_LEAD_jacobian_closure.md`), and the three case hypotheses are area
`Submission.Work.CurveFacts`'s A1–A3.  The file contains no `sorry`.
-/

namespace Submission

open AlgebraicGeometry
set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

namespace JacobianChallenge

-- We make `C` implicit at the variable level so that instance and `def` holes
-- whose statement references the outer `C` (e.g. `instance instGrpObj :
-- GrpObj (Jacobian C) := sorry`) elaborate to a Π-type with `{C}` implicit;
-- otherwise the eval-pipeline's `Solution.lean` would have to thread a `C`
-- argument through every delegation. Decls that genuinely need `C` explicit
-- (e.g. `genus`, `Jacobian`, `comp_ofCurve`) supply their own `(C : ...)`
-- binder.
variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  -- smooth curve
  [SmoothOfRelativeDimension 1 C.hom]
  -- proper
  [IsProper C.hom]
  -- geometrically irreducible
  [GeometricallyIrreducible C.hom]

/-- The Jacobian package of `C` based at a `k`-point: this is the single input of the whole
submission (areas GC/UP of the blueprint).  `Work.Packaging.JacPkg` carries a group scheme `J` over
`Spec k`, proper, geometrically irreducible, smooth, with connected underlying space, the
Abel–Jacobi map `AJ₀ : C ⟶ J` based at `P0`, its universal property `univ₀` and the "generation"
property `epi₀`. -/
theorem jacPkgExists (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (Work.Packaging.JacPkg C P0) :=
  fun P0 => by
    haveI : Smooth C.hom := (inferInstance : SmoothOfRelativeDimension 1 C.hom).smooth
    haveI : IrreducibleSpace C.left :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton C.hom
    exact Work.JacClose.jacPkgExists' C
      (Work.CurveFacts.geometricallyReduced_of_smooth C.hom)
      (fun z => Work.CurveFacts.krullDimLE_stalk_of_smoothOfRelativeDimension_one C.hom z)
      (Work.CurveFacts.nontrivial_of_smoothOfRelativeDimension_one C.hom) P0

-- data
/-- The genus of a smooth proper curve. -/
noncomputable def genus (C : Over (Spec (.of k))) [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] : ℕ :=
  Work.Packaging.Main.genus C (jacPkgExists C)

-- data
/-- The Jacobian of a smooth, proper curve over a field `k`. -/
noncomputable def Jacobian (C : Over (Spec (.of k))) [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] : Over (Spec (.of k)) :=
  Work.Packaging.Main.Jacobian C (jacPkgExists C)

namespace Jacobian

/-! ## The Jacobian of `C` is an abelian variety. -/

-- data
/-- The group scheme structure on the Jacobian of the curve `C`. -/
noncomputable instance instGrpObj : GrpObj (Jacobian C) :=
  Work.Packaging.Main.instGrpObj C (jacPkgExists C)

/-- The Jacobian of `C` is smooth of relative dimension `g` over `k`, where `g` is the
genus of `C`. -/
instance smoothOfRelativeDimension_genus :
    SmoothOfRelativeDimension (genus C) (Jacobian C).hom :=
  Work.Packaging.Main.smoothOfRelativeDimension_genus C (jacPkgExists C)

/-- The Jacobian of `C` is proper over `k`. -/
instance instIsProper : IsProper (Jacobian C).hom :=
  Work.Packaging.Main.instIsProper C (jacPkgExists C)

/-- The Jacobian of `C` is geometrically irreducible over `k`. -/
instance instGeometricallyIrreducible : GeometricallyIrreducible (Jacobian C).hom :=
  Work.Packaging.Main.instGeometricallyIrreducible C (jacPkgExists C)

-- data
/-- The Abel-Jacobi map from a smooth, proper curve to its Jacobian associated
to a `k`-rational point of `C`. -/
noncomputable def ofCurve (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) : C ⟶ Jacobian C :=
  Work.Packaging.Main.ofCurve C (jacPkgExists C) P

/-- The Abel-Jacobi map sends the `k`-rational point `P` to `0`, where `0` (denoted by `η` below) is
the neutral element of the group scheme `Jacobian C`. -/
theorem comp_ofCurve (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    P ≫ ofCurve P = η[Jacobian C] :=
  Work.Packaging.Main.comp_ofCurve C (jacPkgExists C) P

/--
The universal property of the Jacobian variety: For any abelian variety `A`,
any morphism `f : C ⟶ A` such that `f(P) = 0` factors uniquely through the
Jacobian of `C`.
In other words, `Jacobian C` is the Albanese variety of `C`.
-/
theorem exists_unique_ofCurve_comp (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [GeometricallyIrreducible A.hom] (f : C ⟶ A) (hf : P ≫ f = η[A]) :
    ∃! (g : Jacobian C ⟶ A), f = ofCurve P ≫ g :=
  Work.Packaging.Main.exists_unique_ofCurve_comp C (jacPkgExists C) P f hf

end Jacobian

end JacobianChallenge

end AlgebraicGeometry

end Submission
