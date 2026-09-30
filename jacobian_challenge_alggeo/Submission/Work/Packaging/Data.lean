/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area P (packaging)
-/
import Mathlib
import Submission.Work.Packaging.Basic
import Submission.Work.Packaging.Trivial
import Submission.Work.Packaging.RelDim

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Area P: the data of the packaging in both branches

`JacData C` collects, for a curve `C`, exactly the data needed to fill the challenge's holes:

* a group scheme `J` over `Spec k`, proper, geometrically irreducible, smooth, with connected
  underlying space, together with its relative dimension `dim` (the genus),
* a morphism `AJ : C ⟶ J` (the Abel–Jacobi map of the chosen base point, and the structural morphism
  `C ⟶ 𝟙_` in the degenerate case).

The two ways of producing `JacData C` are `pkgData` (from a `JacPkg C P0`, areas GC/UP) and
`trivialData` (the terminal group scheme, used when `C` has no `k`-point). `jacData` chooses between
them by `dite` on `Nonempty (𝟙_ ⟶ C)`.

All the definitions in `Work.Packaging.Main` are projections of `jacData`, so that the branch
distinction is made exactly once.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped MonObj
open Classical

namespace Work.Packaging

/-- The data of the packaging of a curve: a group scheme with its relative dimension, plus a map
from the curve. -/
structure JacData {k : Type u} [Field k] (C : Over (Spec (.of k))) where
  /-- The group scheme playing the role of the Jacobian. -/
  J : Over (Spec (.of k))
  [instGrpObj : GrpObj J]
  [instIsProper : IsProper J.hom]
  [instGeomIrred : GeometricallyIrreducible J.hom]
  [instSmooth : Smooth J.hom]
  [instConnected : ConnectedSpace J.left]
  /-- The genus: the relative dimension of `J` over `Spec k`. -/
  dim : ℕ
  [instDim : SmoothOfRelativeDimension dim J.hom]
  /-- The Abel–Jacobi map (based at a chosen point of `C`). -/
  AJ : C ⟶ J

attribute [instance] JacData.instGrpObj JacData.instIsProper JacData.instGeomIrred JacData.instSmooth
  JacData.instConnected JacData.instDim

/-- The packaging data associated to a Jacobian package. -/
noncomputable def pkgData {k : Type u} [Field k] {C : Over (Spec (.of k))}
    {P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C} (Pkg : JacPkg C P0) : JacData C where
  J := Pkg.J
  instGrpObj := Pkg.instGrpObj
  instIsProper := Pkg.instIsProper
  instGeomIrred := Pkg.instGeomIrred
  instSmooth := Pkg.instSmooth
  instConnected := Pkg.instConnected
  dim := RelDim.genusOf Pkg
  instDim := RelDim.smoothOfRelativeDimension_genusOf Pkg
  AJ := Pkg.AJ₀

/-- The packaging data in the trivial case: the terminal group scheme over `Spec k`. The map
`AJ : C ⟶ 𝟙_` is the structural morphism (it is irrelevant: this branch is only used when `C` has no
`k`-point, in which case the Abel–Jacobi map is never applied). -/
noncomputable def trivialData {k : Type u} [Field k] (C : Over (Spec (.of k))) : JacData C where
  J := 𝟙_ (Over (Spec (.of k)))
  instGrpObj := Trivial.instGrpObjUnit
  instIsProper := Trivial.instIsProperUnit
  instGeomIrred := Trivial.instGeomIrredUnit
  instSmooth := Trivial.instSmoothUnit
  instConnected := Trivial.instConnectedUnit
  dim := 0
  instDim := Trivial.instSmoothOfRelativeDimensionUnit
  AJ := toUnit C

/-- The packaging data of `C`, using a Jacobian package based at a `k`-point of `C` when there is
one, and the trivial group scheme otherwise. -/
noncomputable def jacData {k : Type u} [Field k] (C : Over (Spec (.of k)))
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0)) : JacData C :=
  if h : Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ C) then
    pkgData (Classical.choice (hEx (Classical.choice h)))
  else trivialData C

theorem jacData_of_point {k : Type u} [Field k] {C : Over (Spec (.of k))}
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0))
    (h : Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ C)) :
    jacData C hEx = pkgData (Classical.choice (hEx (Classical.choice h))) := by
  unfold jacData
  rw [dite_eq_left h]

theorem jacData_of_no_point {k : Type u} [Field k] {C : Over (Spec (.of k))}
    (hEx : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (JacPkg C P0))
    (h : ¬ Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ C)) :
    jacData C hEx = trivialData C := by
  unfold jacData
  rw [dite_eq_right h]

end Work.Packaging
