/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The relative quotient property of finite-group quotients (area SY)

The quotient `X/Γ` of a scheme by a finite group commutes with base change: for a `K`-scheme `Y`,
the categorical quotient of `X ⊗ Y` (the fibre product over `Spec K`) by the induced action
`(g, id)` is `(X/Γ) ⊗ Y`, with quotient map `q ▷ Y`.  This is the *relative quotient property*
`relQuot`, the missing ingredient for the addition map `Sym^m C ⊗ Sym^n C ⟶ Sym^{m+n} C`
(`Submission/Work/NOTES_LEAD_jacobian_final.md` §2.2), and with `Y = Spec F` it also gives
`Sym.baseChangeIso`/`SymBC`.

This file contains only the vocabulary:

* `actOver` — the action morphism of `Γ` on `X`, as a morphism of `K`-schemes;
* `relQuotScheme` — the quotient `X/Γ` as a `K`-scheme (from the `QuotientData`);
* `relQuotSchemeMap` — the quotient map `X ⟶ X/Γ`.

The relative quotient property itself is proved downstream.
-/
import Mathlib
import Submission.Work.SymQuot.QuotientMap
import Submission.Work.SymQuot.QuotientHom
import Submission.Work.SymQuot.Invariants.tensor_fixedPoints
import Submission.Work.SpecLin.Conventions

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonoidalCategory

universe u

namespace Work.SymQuot

variable {K : Type u} [Field K]

/-- **The action morphism of `Γ` on `X` as a morphism of `K`-schemes**, from a scheme action
whose morphisms are over `Spec K`. -/
noncomputable abbrev actOver (X : Work.SpecLin.Sch K) {Γ : Type u} [Group Γ] [Fintype Γ]
    (D : QuotientData Γ X.left) (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (g : Γ) :
    X ⟶ X :=
  Over.homMk (D.action.hom g) (hbase g)

/-- **The quotient `X/Γ` as a `K`-scheme**, from a `QuotientData` whose action is over
`Spec K`. -/
noncomputable abbrev relQuotScheme (X : Work.SpecLin.Sch K) {Γ : Type u} [Group Γ] [Fintype Γ]
    (D : QuotientData Γ X.left) (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) :
    Work.SpecLin.Sch K :=
  Over.mk (D.quotientHom X.hom hbase)

/-- **The quotient map** `X ⟶ X/Γ` of `relQuotScheme`. -/
noncomputable abbrev relQuotSchemeMap (X : Work.SpecLin.Sch K) {Γ : Type u} [Group Γ] [Fintype Γ]
    (D : QuotientData Γ X.left) (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) :
    X ⟶ relQuotScheme X D hbase :=
  Over.homMk D.quotientMap (QuotientData.quotientMap_quotientHom D X.hom hbase)

end Work.SymQuot
