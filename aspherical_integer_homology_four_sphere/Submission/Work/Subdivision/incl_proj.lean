/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SubDataQuot

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The composite of the inclusion and the projection of a subcomplex vanishes

For a subcomplex `S` of a chain complex `C` of `ℤ`-modules, the composite
`S.chain ⟶ C ⟶ S.quot` of the inclusion `S.incl` with the projection `S.proj`
onto the quotient is zero.  This is the last ingredient needed for the
short complex `0 → S.chain → C → S.quot → 0` (`SubData.shortComplexOf`).

The proof is componentwise: at degree `k`, the composite is the `ℤ`-linear map
`S.sub k ↪ C.X k ↠ C.X k ⧸ S.sub k`, which is zero because the quotient map
kills the submodule.
-/

namespace Work.Subdivision

open CategoryTheory

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

namespace SubData

variable (S : SubData C)

section

/-- Fix the ℤ-module structures on the submodules (see `SubComplex.lean`). -/
local instance instModuleSub' {k : ℕ} : Module ℤ ↥(S.sub k) := (S.sub k).module

/-- Fix the ℤ-module structures on the quotients (see `SubComplex.lean`). -/
local instance instModuleQuot' {k : ℕ} : Module ℤ (C.X k ⧸ S.sub k) :=
  Submodule.Quotient.module (S.sub k)

/-- The underlying linear map of the `k`-th component of the inclusion. -/
theorem incl_f_hom (k : ℕ) : (S.incl.f k).hom = (Submodule.subtype (S.sub k)) := by
  rw [incl_f]
  exact ModuleCat.hom_ofHom _

/-- The underlying linear map of the `k`-th component of the projection. -/
theorem proj_f_hom (k : ℕ) : (S.proj.f k).hom = (Submodule.mkQ (S.sub k)) := by
  rw [proj_f]
  exact ModuleCat.hom_ofHom _

/-- At every degree the composite of the inclusion and the projection is zero. -/
theorem incl_f_comp_proj_f (k : ℕ) : S.incl.f k ≫ S.proj.f k = 0 := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp (f := S.incl.f k) (g := S.proj.f k), ModuleCat.hom_zero (R := ℤ)]
  rw [S.incl_f_hom k, S.proj_f_hom k]
  change (Submodule.mkQ (S.sub k)).comp (Submodule.subtype (S.sub k)) =
    (0 : ↥(S.sub k) →ₗ[ℤ] (C.X k ⧸ S.sub k))
  ext x
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.subtype_apply]
  exact (Submodule.Quotient.mk_eq_zero (S.sub k)).mpr x.2

end

end SubData

theorem incl_proj {C : ChainComplex (ModuleCat ℤ) ℕ} (S : SubData C) :
    CategoryTheory.CategoryStruct.comp S.incl S.proj = 0 := by
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  exact SubData.incl_f_comp_proj_f S k

end Work.Subdivision
