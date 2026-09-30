/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `S_n`-action on the `n`-fold product (area SY)

`permGAction X n` is the action of the symmetric group `S_n = Equiv.Perm (Fin n)` on the
`n`-fold product `prod X n` of a `K`-scheme with itself, by permutation of the factors.  Its laws
are the projection formula `permIso_hom_proj` together with `permIso_one` and `permIso_mul`.
-/
import Submission.Work.SymQuot.Basic
import Submission.Work.SymQuot.Product
import Submission.Work.SymQuot.Product.permIso_one
import Submission.Work.SymQuot.Product.permIso_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

variable {K : Type u} [Field K]

/-- The action of `S_n` on the `n`-fold product of a `K`-scheme with itself, by permutation of
the factors. -/
noncomputable def permGAction (X : Work.GCBasics.Sch K) (n : ℕ) :
    GAction (Equiv.Perm (Fin n)) (prod X n).left where
  hom σ := (permIso X σ).hom.left
  inv σ := (permIso X σ).inv.left
  hom_inv σ := by
    rw [← CategoryTheory.Over.comp_left, Iso.hom_inv_id, CategoryTheory.Over.id_left]
  inv_hom σ := by
    rw [← CategoryTheory.Over.comp_left, Iso.inv_hom_id, CategoryTheory.Over.id_left]
  hom_one := by
    rw [Product.permIso_one, Iso.refl_hom, CategoryTheory.Over.id_left]
  hom_mul σ τ := by
    rw [Product.permIso_mul, Iso.trans_hom, CategoryTheory.Over.comp_left]

end Work.SymQuot
