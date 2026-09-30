/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Data for the quotient of a scheme by a finite group (area SY)

Given a scheme `X` with an action of a finite group `Γ` and a `Γ`-invariant affine open cover of
`X`, the quotient `X/Γ` is obtained by gluing the charts `Spec Γ(X, U)^Γ` of the invariant affine
open subschemes `U ⊆ X` (see `Submission.Work.SymQuot.Chart`).

This file contains the *data* of the construction: the structure `QuotientData` and the diagram

```
D.Chart ⥤ Scheme,   U ↦ Spec Γ(X,U)^Γ,   (U ≤ V) ↦ chartRes
```

whose locally directed colimit is the quotient (see `Submission.Work.SymQuot.Quotient`).

It is deliberately separated from `Submission.Work.SymQuot.Quotient`: the fact that the diagram is
locally directed is proved in `Submission.Work.SymQuot.Chart.chartFunctor_isLocallyDirected`,
which therefore has to be *above* this file, while the colimit API in
`Submission.Work.SymQuot.Quotient` has to be *below* it.
-/
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Chart.chartRes_chartMap
import Submission.Work.SymQuot.Chart.chartRes_isOpenImmersion_alt
import Submission.Work.SymQuot.Chart.chartMap_image_inf
import Submission.Work.SymQuot.Chart.chartMap_fiber_orbit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u v

namespace Work.SymQuot

/-- Data for the quotient of a scheme by a finite group: the action, the fact that intersections
of affine opens are affine, and the fact that every point lies in an invariant affine open. -/
structure QuotientData (Γ : Type u) [Group Γ] [Fintype Γ] (X : Scheme.{u}) where
  /-- The action of `Γ` on `X`. -/
  action : GAction Γ X
  /-- Intersections of affine opens are affine. -/
  isAffineOpen_inf :
    ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)
  /-- Every point of `X` lies in a `Γ`-invariant affine open subscheme. -/
  covers :
    ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ action.IsInvariantOpen U ∧ x ∈ U

namespace QuotientData

variable {Γ : Type u} [Group Γ] [Fintype Γ] {X : Scheme.{u}} (D : QuotientData Γ X)

/-- The invariant affine open subschemes of `X`, as a subtype of `X.Opens` (a poset, hence a
thin category). -/
abbrev Chart : Type u := {U : X.Opens // IsAffineOpen U ∧ D.action.IsInvariantOpen U}

instance : PartialOrder D.Chart := inferInstanceAs (PartialOrder {_U : X.Opens // _})


instance : Small.{u} D.Chart := small_of_injective Subtype.val_injective

instance : Category D.Chart := Preorder.smallCategory D.Chart

instance : Quiver.IsThin D.Chart := fun _ _ => ⟨fun _ _ => Subsingleton.elim _ _⟩

/-- The chart of an element of the cover. -/
noncomputable abbrev chart (U : D.Chart) : Scheme.{u} :=
  D.action.chart U.1 U.2.2

lemma chart_isAffine (U : D.Chart) : IsAffineOpen U.1 := U.2.1

lemma chart_isInvariant (U : D.Chart) : D.action.IsInvariantOpen U.1 := U.2.2

/-- The meet of two elements of the cover. -/
noncomputable def inf (U V : D.Chart) : D.Chart :=
  ⟨U.1 ⊓ V.1, D.isAffineOpen_inf _ _ U.2.1 V.2.1, U.2.2.inf V.2.2⟩

@[simp] lemma inf_val (U V : D.Chart) : (D.inf U V).1 = U.1 ⊓ V.1 := rfl

/-- The diagram of charts. -/
noncomputable def chartFunctor : D.Chart ⥤ Scheme.{u} where
  obj U := D.chart U
  map {U V} h := D.action.chartRes U.1 V.1 (leOfHom h) V.2.2 U.2.2
  map_id U := Work.SymQuot.GAction.chartRes_id D.action U.1 U.2.2
  map_comp {U V W} h₁ h₂ :=
    (Work.SymQuot.GAction.chartRes_comp D.action U.1 V.1 W.1 (leOfHom h₁) (leOfHom h₂)
      W.2.2 V.2.2 U.2.2).symm

instance (U V : D.Chart) (h : U ⟶ V) : IsOpenImmersion (D.chartFunctor.map h) :=
  Work.SymQuot.Chart.chartRes_isOpenImmersion_alt D.action (leOfHom h) V.2.1 U.2.1 V.2.2 U.2.2

-- (The transition maps are open immersions, as recorded by the instance above; the same statement
-- transported to `Type` along `Scheme.forget` is not a well-typed `IsOpenImmersion` statement, so
-- no companion instance is recorded here.)

end QuotientData

end Work.SymQuot
