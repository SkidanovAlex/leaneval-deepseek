/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Powers of a `K`-scheme and the symmetric-group action (area SY)

`prod X n` is the `n`-fold product of a `K`-scheme `X` with itself (the product over `Spec K`), and
`permIso X σ` is the automorphism of `prod X n` induced by a permutation `σ` of the factors.
These are the input of `Sym n C = (C^n)/S_n`.

The laws of the action are delegated to `SymQuot/Product/…`:
`permIso_hom_π` (the action on the factors), `permIso_one` and `permIso_mul` (in the order needed
for the `GAction` convention `act (σ * τ) = act τ ≫ act σ`).
-/
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

variable {K : Type u} [Field K]

/-- The `n`-fold product of a `K`-scheme with itself. -/
noncomputable def prod (X : Work.GCBasics.Sch K) (n : ℕ) : Work.GCBasics.Sch K :=
  ∏ᶜ (fun _ : Fin n => X)

/-- The automorphism of the `n`-fold product induced by a permutation of the factors. -/
noncomputable def permIso (X : Work.GCBasics.Sch K) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    prod X n ≅ prod X n :=
  Pi.whiskerEquiv σ (fun _ => Iso.refl X)

/-- **Naturality of `Pi.lift` in the source**: lifting the family `m ↦ g ≫ x m` is the same as
composing `g` with the lift of `x`. -/
theorem pi_lift_comp {X : Work.GCBasics.Sch K} (n : ℕ) {T T' : Work.GCBasics.Sch K}
    (g : T' ⟶ T) (x : Fin n → (T ⟶ X)) :
    Limits.Pi.lift (fun m => g ≫ x m) = g ≫ Limits.Pi.lift x := by
  apply Limits.Pi.hom_ext
  intro m
  simp only [Category.assoc, Limits.Pi.lift_comp_π]

/-- The `m`-th projection of the `n`-fold product. -/
noncomputable abbrev proj (X : Work.GCBasics.Sch K) (n : ℕ) (m : Fin n) : prod X n ⟶ X :=
  Limits.Pi.π (fun _ : Fin n => X) m

end Work.SymQuot
