/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SubDataCpt
import Submission.Work.Subdivision.restrictCptMap_comm
import Submission.Work.Subdivision.quotCptMap_comm
import Submission.Work.Subdivision.incl_restrictCptMap
import Submission.Work.Subdivision.proj_quotCptMap
import Submission.Work.Subdivision.shortComplexOf_shortExact
import Submission.Work.Subdivision.incl_proj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The morphism of short exact sequences induced by a compatible chain map

A chain map `f : C ⟶ C'` carrying `S` into `S'` restricts to the subcomplexes
(`SubData.restrictMap`) and descends to the quotients (`SubData.quotMap`); the two
naturality squares (`Work.Subdivision.incl_restrictCptMap`,
`Work.Subdivision.proj_quotCptMap`) assemble these into a morphism of short exact
sequences (`SubData.shortComplexHom`), whose components are `restrictMap`, `f` and
`quotMap`.
-/

namespace Work.Subdivision

open CategoryTheory

variable {C C' : ChainComplex (ModuleCat ℤ) ℕ}

namespace SubData

variable (S : SubData C) (S' : SubData C')

section

/-- Fix the ℤ-module structures (see `SubComplex.lean`). -/
local instance instSubSES {k : ℕ} : Module ℤ ↥(S.sub k) := (S.sub k).module

/-- Fix the ℤ-module structures (see `SubComplex.lean`). -/
local instance instSubSES' {k : ℕ} : Module ℤ ↥(S'.sub k) := (S'.sub k).module

/-- Fix the ℤ-module structures (see `SubComplex.lean`). -/
local instance instQuotSES {k : ℕ} : Module ℤ (C.X k ⧸ S.sub k) :=
  Submodule.Quotient.module (S.sub k)

/-- Fix the ℤ-module structures (see `SubComplex.lean`). -/
local instance instQuotSES' {k : ℕ} : Module ℤ (C'.X k ⧸ S'.sub k) :=
  Submodule.Quotient.module (S'.sub k)

/-- The restriction of a chain map to compatible subcomplexes. -/
noncomputable def restrictMap (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) : S.chain ⟶ S'.chain :=
  ChainComplex.ofHom (fun k => S.restrictCptMap S' f hf k) fun k => by
    rw [S.chain_d_eq k, S'.chain_d_eq k]
    exact restrictCptMap_comm S S' f hf k

@[simp] theorem restrictMap_f (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) (k : ℕ) :
    (S.restrictMap S' f hf).f k = S.restrictCptMap S' f hf k := rfl

/-- The map induced by a chain map on the quotients. -/
noncomputable def quotMap (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) : S.quot ⟶ S'.quot :=
  ChainComplex.ofHom (fun k => S.quotCptMap S' f hf k) fun k => by
    rw [S.quot_d_eq k, S'.quot_d_eq k]
    exact quotCptMap_comm S S' f hf k

@[simp] theorem quotMap_f (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) (k : ℕ) :
    (S.quotMap S' f hf).f k = S.quotCptMap S' f hf k := rfl

/-- The morphism of short exact sequences `0 → S.chain → C → S.quot → 0` and
`0 → S'.chain → C' → S'.quot → 0` induced by a compatible chain map `f`. -/
noncomputable def shortComplexHom (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom)
    (w : S.incl ≫ S.proj = 0) (w' : S'.incl ≫ S'.proj = 0) :
    S.shortComplexOf w ⟶ S'.shortComplexOf w' where
  τ₁ := S.restrictMap S' f hf
  τ₂ := f
  τ₃ := S.quotMap S' f hf
  comm₁₂ := by
    apply HomologicalComplex.hom_ext
    intro k
    show (S.restrictMap S' f hf).f k ≫ S'.incl.f k = S.incl.f k ≫ f.f k
    rw [S.restrictMap_f, S.incl_f_eq k, S'.incl_f_eq k]
    exact (incl_restrictCptMap S S' f hf k).symm
  comm₂₃ := by
    apply HomologicalComplex.hom_ext
    intro k
    show f.f k ≫ S'.proj.f k = S.proj.f k ≫ (S.quotMap S' f hf).f k
    rw [S.quotMap_f, S.proj_f_eq k, S'.proj_f_eq k]
    exact (proj_quotCptMap S S' f hf k).symm

@[simp] theorem shortComplexHom_τ₁ (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom)
    (w : S.incl ≫ S.proj = 0) (w' : S'.incl ≫ S'.proj = 0) :
    (S.shortComplexHom S' f hf w w').τ₁ = S.restrictMap S' f hf := rfl

@[simp] theorem shortComplexHom_τ₂ (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom)
    (w : S.incl ≫ S.proj = 0) (w' : S'.incl ≫ S'.proj = 0) :
    (S.shortComplexHom S' f hf w w').τ₂ = f := rfl

@[simp] theorem shortComplexHom_τ₃ (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom)
    (w : S.incl ≫ S.proj = 0) (w' : S'.incl ≫ S'.proj = 0) :
    (S.shortComplexHom S' f hf w w').τ₃ = S.quotMap S' f hf := rfl

end

end SubData

end Work.Subdivision
