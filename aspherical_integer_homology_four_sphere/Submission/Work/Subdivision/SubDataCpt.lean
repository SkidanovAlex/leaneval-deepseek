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
# Components of the inclusion, the projection and the quotient map

For `R = ℤ` the elaborator picks different (propositionally equal but not
definitionally equal) `Module ℤ` structures on the same carrier, which makes the
naive `ModuleCat.ofHom (S.dL k)` fail to elaborate at a position where the
expected type is `S.chain.X (k+1) ⟶ S.chain.X k`.  Declaring the components with
an explicit type (as below) fixes the instance choice once and for all.
-/

namespace Work.Subdivision

open CategoryTheory

variable {C C' : ChainComplex (ModuleCat ℤ) ℕ}

namespace SubData

variable (S : SubData C)

section

/-- Fix the ℤ-module structures (see `SubComplex.lean`). -/
local instance instModuleSubC {k : ℕ} : Module ℤ ↥(S.sub k) := (S.sub k).module

/-- Fix the ℤ-module structures (see `SubComplex.lean`). -/
local instance instModuleQuotC {k : ℕ} : Module ℤ (C.X k ⧸ S.sub k) :=
  Submodule.Quotient.module (S.sub k)

/-- The differential of the subcomplex, as a morphism of the ambient complexes. -/
noncomputable def dLcpt (k : ℕ) : S.chain.X (k + 1) ⟶ S.chain.X k :=
  ModuleCat.ofHom (S.dL k)

@[simp] theorem dLcpt_apply (k : ℕ) : (S.dLcpt k).hom = S.dL k := rfl

/-- The inclusion of the subcomplex, degree by degree. -/
noncomputable def inclcpt (k : ℕ) : S.chain.X k ⟶ C.X k :=
  ModuleCat.ofHom (S.sub k).subtype

@[simp] theorem inclcpt_apply (k : ℕ) : (S.inclcpt k).hom = (S.sub k).subtype := rfl

/-- The projection onto the quotient, degree by degree. -/
noncomputable def projcpt (k : ℕ) : C.X k ⟶ S.quot.X k :=
  ModuleCat.ofHom (Submodule.mkQ (S.sub k))

@[simp] theorem projcpt_apply (k : ℕ) : (S.projcpt k).hom = Submodule.mkQ (S.sub k) := rfl

/-- The differential of the quotient, as a morphism. -/
noncomputable def quotDcpt (k : ℕ) : S.quot.X (k + 1) ⟶ S.quot.X k :=
  ModuleCat.ofHom (S.quotD k)

/-- The component of the map induced by a chain map on the quotients, for
compatible subcomplex data. -/
noncomputable def quotCptMap (S' : SubData C') (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) (k : ℕ) :
    S.quot.X k ⟶ S'.quot.X k :=
  ModuleCat.ofHom (Submodule.mapQ (S.sub k) (S'.sub k) (f.f k).hom (hf k))

@[simp] theorem quotCptMap_apply (S' : SubData C') (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) (k : ℕ) :
    (S.quotCptMap S' f hf k).hom =
      Submodule.mapQ (S.sub k) (S'.sub k) (f.f k).hom (hf k) := rfl

/-- The component of the restriction of a chain map to compatible subcomplexes. -/
noncomputable def restrictCptMap (S' : SubData C') (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) (k : ℕ) :
    S.chain.X k ⟶ S'.chain.X k :=
  ModuleCat.ofHom ((f.f k).hom.restrict fun x hx => hf k hx)

@[simp] theorem restrictCptMap_apply (S' : SubData C') (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom) (k : ℕ) :
    (S.restrictCptMap S' f hf k).hom = (f.f k).hom.restrict (fun x hx => hf k hx) := rfl

@[simp] theorem quotDcpt_apply (k : ℕ) : (S.quotDcpt k).hom = S.quotD k := rfl

@[simp] theorem chain_d_eq (k : ℕ) : (S.chain).d (k + 1) k = S.dLcpt k := by
  rw [chain_d]
  rfl

@[simp] theorem quot_d_eq (k : ℕ) : (S.quot).d (k + 1) k = S.quotDcpt k := by
  rw [quot_d]
  rfl

@[simp] theorem incl_f_eq (k : ℕ) : S.incl.f k = S.inclcpt k := by
  rw [incl_f]
  rfl

@[simp] theorem proj_f_eq (k : ℕ) : S.proj.f k = S.projcpt k := by
  rw [proj_f]
  rfl

end

end SubData

end Work.Subdivision
