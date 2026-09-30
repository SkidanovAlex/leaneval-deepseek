/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The universal property of `X/Γ` and the structure morphism (area SY)

A `Γ`-invariant morphism `f : X ⟶ Z` factors uniquely through the quotient map
(`QuotientData.quotient_lift`), and consequently the quotient of a `k`-scheme by an action by
`k`-automorphisms is again a `k`-scheme (`QuotientData.quotientHom`).
-/
import Submission.Work.SymQuot.QuotientMap
import Submission.Work.SymQuot.Chart.quotient_lift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

namespace QuotientData

variable {Γ : Type u} [Group Γ] [Fintype Γ] {X : Scheme.{u}} (D : QuotientData Γ X)

/-- The universal property of the quotient: a `Γ`-invariant morphism out of `X` factors
uniquely through the quotient map. -/
theorem quotient_lift {Z : Scheme.{u}} (f : X ⟶ Z) (hf : D.action.IsInvariantMorphism f) :
    ∃! g : D.Quotient ⟶ Z, D.quotientMap ≫ g = f :=
  Chart.quotient_lift D f hf

/-- If `X` is a scheme over `S` and `Γ` acts by `S`-automorphisms, the quotient receives a
canonical structure morphism over `S`. -/
noncomputable def quotientHom {S : Scheme.{u}} (f : X ⟶ S) (hf : ∀ g : Γ, D.action.hom g ≫ f = f) :
    D.Quotient ⟶ S :=
  (D.quotient_lift f hf).choose

@[reassoc (attr := simp)]
theorem quotientMap_quotientHom {S : Scheme.{u}} (f : X ⟶ S)
    (hf : ∀ g : Γ, D.action.hom g ≫ f = f) :
    D.quotientMap ≫ D.quotientHom f hf = f :=
  (D.quotient_lift f hf).choose_spec.1

end QuotientData

end Work.SymQuot
