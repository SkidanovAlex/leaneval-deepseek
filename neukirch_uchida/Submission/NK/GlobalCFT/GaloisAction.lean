/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFT.Galois.globalCFT_place_smul_liesOver
import Submission.NK.GlobalCFT.Galois.globalCFT_smul_place_smul
import Submission.NK.GlobalCFT.Galois.globalCFT_one_smul_place

/-!
# The action of `Gal(L/K)` on the places and the idèles

For a finite extension `L / K` the group `Gal(L/K) = (L ≃ₐ[K] L)` acts on the places of `L`
(`NK.GlobalCFT.Place`, defined in `Place.lean`), preserving the places above a fixed place of
`K` (`NK.GlobalCFT.Galois.globalCFT_place_smul_liesOver`).  This file collects the action on
places as a `MulAction` and records the compatibility lemmas needed to descend the action to the
idèle group and the idèle class group.

## Main results

* `NK.GlobalCFT.Place.instMulActionGalois`: `Gal(L/K)` acts on `Place L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Place

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- `Gal(L/K)` acts on the places of `L`. -/
instance mulActionGalois : MulAction (L ≃ₐ[K] L) (Place L) where
  one_smul v := NK.GlobalCFT.Galois.globalCFT_one_smul_place v
  mul_smul σ σ' v := (NK.GlobalCFT.Galois.globalCFT_smul_place_smul σ' σ v).symm

/-- The action of `Gal(L/K)` preserves the places lying over a given place of `K`. -/
theorem liesOver_smul_iff {σ : L ≃ₐ[K] L} {w : Place L} {v : Place K} :
    LiesOver (σ • w) v ↔ LiesOver w v :=
  NK.GlobalCFT.Galois.globalCFT_place_smul_liesOver σ w v

end Place

end NK.GlobalCFT
