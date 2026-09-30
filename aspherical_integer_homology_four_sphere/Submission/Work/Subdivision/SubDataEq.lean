/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SubDataSES
import Submission.Work.Subdivision.SubDataQuasiIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Transport of subcomplex data along an equality

If two `SubData`s of a chain complex have the same degreewise submodules, they are
equal as structures (the remaining field is a proof), and the restriction of a
chain map to them differ only in the proof of the compatibility condition:
`SubData.restrictMap_congr`.

Consequently `SubData.quasiIso_of_sub_data_eq` transports the statement
"the restriction of `f` to `S ⊆ S'` is a quasi-isomorphism" along equalities
`T = S`, `T' = S'` of subcomplex data.  This is the tool that identifies the two
endpoints of the cell-by-cell induction over the refined skeletal filtrations with
the plain skeleta (`PolyCW.quasiIso_cellTop_empty_iff`,
`PolyCW.quasiIso_cellTop_faces_iff`).
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

variable {C C' : ChainComplex (ModuleCat ℤ) ℕ}

namespace SubData

section

/-- Fix the ℤ-module structures (see `SubComplex.lean`). -/
local instance instSubEqSub {S : SubData C} {k : ℕ} : Module ℤ ↥(S.sub k) := (S.sub k).module

/-- Restricted chain maps do not depend on the proof of the compatibility
condition. -/
theorem restrictMap_congr (S : SubData C) (S' : SubData C') (f : C ⟶ C')
    (hf hf' : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) :
    S.restrictMap S' f hf = S.restrictMap S' f hf' := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- **Transport of the restriction statement along an equality of subcomplex
data.** -/
theorem quasiIso_of_sub_data_eq (S T : SubData C) (S' T' : SubData C')
    (hTS : T = S) (h'T'S' : T' = S') (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom)
    (hf' : ∀ k, T.sub k ≤ (T'.sub k).comap (f.f k).hom) :
    QuasiIso (T.restrictMap T' f hf') ↔ QuasiIso (S.restrictMap S' f hf) := by
  revert hf hf'
  subst hTS
  subst h'T'S'
  intro hf hf'
  rw [restrictMap_congr _ _ f hf hf']

end

end SubData

end

end Work.Subdivision
