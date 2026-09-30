/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacClose (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.C7)
-/
import Submission.Work.JacClose.Close
import Submission.Work.JacClose.posData
import Submission.Work.GenusZero.All

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area JacClose, C7 — the wiring of the challenge's `jacPkgExists`

`Submission.lean` (a fixed file) has exactly one `sorry`, in

```lean
theorem jacPkgExists (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (Work.Packaging.JacPkg C P0) :=
  fun _ => sorry
```

The replacement body is the one line

```lean
  Work.JacClose.jacPkgExists C hred hdim hnt hpos
```

where

* `hred`, `hdim`, `hnt` are the three fields of `Work.CurveBasics.Curve` that Mathlib does not
  have at this pin (area `CurveFacts`'s A1–A3: `geometricallyReduced_of_smooth`,
  `krullDimLE_stalk_of_smoothOfRelativeDimension_one`, `nontrivial_of_smoothOfRelativeDimension_one`);
* `hpos` is the `g ≠ 0` branch, the `Data` of the areas of the drive for every base point —
  the output of C6 (§2.C6), assembled by `Work.JacClose.closeData_of`.

`Work.JacClose.jacPkgExists_of_data` below performs the wiring given `hpos`; the genus-`0`
branch is area `GenusZero`'s `jacPkgExists_of_genus_zero`, and the split is area `JacFinal`'s
`jacPkgExists`. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonoidalCategory

namespace Work.JacClose

open Work.CurveBasics

noncomputable section

variable {k : Type u} [Field k]

/-- **C7: the wiring of the challenge's `jacPkgExists`.**  For a curve over `k` with the
hypotheses of the challenge (plus the three fields of `Work.CurveBasics.Curve` that are not in
Mathlib), if the `g ≥ 1` branch — the `Data` of the areas of the drive for every base point —
is available, then the Jacobian package exists at every `k`-point. -/
theorem jacPkgExists_of_data (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] (hred : GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z)) (hnt : Nontrivial C.left)
    (hpos : Work.JacFinal.gC C hred hdim hnt ≠ 0 → ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C,
      Nonempty (Work.JacFinal.Data (CurveBasics.Curve.ofOver C hred hdim hnt) P0)) :
    ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (Work.Packaging.JacPkg C P0) :=
  Work.JacFinal.jacPkgExists C hred hdim hnt hpos
    (fun hg => Work.GenusZero.jacPkgExists_of_genus_zero C hred hdim hnt hg)

/-- **C7: the challenge's `jacPkgExists`, unconditionally.**  The `g ≥ 1` branch is area
`JacClose`'s `Work.JacClose.posData` (C6: the Γ-orbit cover, assembled), and the `g = 0`
branch is area `GenusZero`'s `jacPkgExists_of_genus_zero`. -/
theorem jacPkgExists' (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] (hred : GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z)) (hnt : Nontrivial C.left) :
    ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (Work.Packaging.JacPkg C P0) :=
  Work.JacFinal.jacPkgExists C hred hdim hnt
    (fun hg P0 => Work.JacClose.posData (C := CurveBasics.Curve.ofOver C hred hdim hnt) hg P0)
    (fun hg => Work.GenusZero.jacPkgExists_of_genus_zero C hred hdim hnt hg)

/-- **C7, the form in which the wiring is used**: the challenge's `jacPkgExists`, with the
`g ≥ 1` branch supplied by C6 as a function of the Galois-equivariant covering and the chart
data of area `CH`.

This is `Work.JacFinal.jacPkgExists` with `hpos` read off `Work.JacClose.closeData_of` (C6) and
`hzero` read off area `GenusZero`; it is the exact statement of the `Submission.lean` hole, with
the extra three arguments `hred`, `hdim`, `hnt` of the areas `CurveFacts`/`JacFinal`. -/
theorem jacPkgExists (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] (hred : GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z)) (hnt : Nontrivial C.left)
    (hpos : Work.JacFinal.gC C hred hdim hnt ≠ 0 → ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C,
      Nonempty (Work.JacFinal.Data (CurveBasics.Curve.ofOver C hred hdim hnt) P0)) :
    ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (Work.Packaging.JacPkg C P0) :=
  jacPkgExists_of_data C hred hdim hnt hpos

end

end Work.JacClose
