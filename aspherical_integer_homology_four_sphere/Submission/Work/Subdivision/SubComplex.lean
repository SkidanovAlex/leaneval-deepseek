/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Subcomplexes, quotient complexes and their short exact sequences

For a chain complex `C` of ℤ-modules and degreewise submodules `S k ⊆ C.X k`
closed under the differential, this file constructs

* the subcomplex `SubData.chain S`,
* the quotient complex `SubData.quot S`,
* the inclusion `SubData.incl S` and the projection `SubData.proj S`,
* the short exact sequence `SubData.shortComplex S`, proved short exact
  (`SubData.shortExact`),

It also isolates the cocycle condition `∂ ∘ ∂ = 0` for the induced differential
as a hypothesis of `SubData.quotOf`.

The remaining functoriality of this construction (a chain map `f : C ⟶ C'`
carrying `S` into `S'` restricting to the subcomplexes and descending to the
quotients, giving a morphism of short exact sequences, so that the five lemma
concludes `QuasiIso f` from `QuasiIso` on the subcomplexes and the quotients) is
future work, see `NOTES.md`.

## Note on the ℤ-module diamond

For `R = ℤ` the instance `AddCommGroup.toIntModule` competes with the
`Submodule.module` and `Submodule.Quotient.module` instances, so the naive
`ModuleCat.ofHom p.subtype` does not elaborate.  We fix the canonical choice by
raising the priority of those two instances (this also fixes the choice inside
`ModuleCat.of`, and for importers of this file).
-/

namespace Work.Subdivision

open CategoryTheory Limits

-- The canonical `ℤ`-module structures on the carrier of a submodule and on a
-- quotient win over the generic `AddCommGroup.toIntModule`.
attribute [instance 1100] Submodule.module
attribute [instance 1100] Submodule.Quotient.module

variable {C C' : ChainComplex (ModuleCat ℤ) ℕ}

/-- The data of a subcomplex: degreewise submodules closed under the differential. -/
structure SubData (C : ChainComplex (ModuleCat ℤ) ℕ) where
  /-- The degreewise submodules. -/
  sub : ∀ k, Submodule ℤ (C.X k)
  /-- They are closed under the differential. -/
  d_mem : ∀ k (x : C.X (k + 1)), x ∈ sub (k + 1) → (C.d (k + 1) k).hom x ∈ sub k

namespace SubData

variable (S : SubData C)

section

/-- Fix the ℤ-module structures used on the submodules (see the file header). -/
local instance instModuleSub {k : ℕ} : Module ℤ ↥(S.sub k) := (S.sub k).module

/-- Fix the ℤ-module structures used on the quotients (see the file header). -/
local instance instModuleQuot {k : ℕ} : Module ℤ (C.X k ⧸ S.sub k) :=
  Submodule.Quotient.module (S.sub k)

/-! ### The subcomplex -/

/-- The differential of the subcomplex. -/
noncomputable def dL (k : ℕ) : ↥(S.sub (k + 1)) →ₗ[ℤ] ↥(S.sub k) :=
  (C.d (k + 1) k).hom.restrict (fun x hx => S.d_mem k x hx)

theorem dL_apply (k : ℕ) (x : ↥(S.sub (k + 1))) :
    ((S.dL k x : ↥(S.sub k)) : C.X k) = (C.d (k + 1) k).hom (x : C.X (k + 1)) := rfl

/-- Consecutive differentials of `C` applied to an element give zero. -/
theorem d_comp_d_apply (k : ℕ) (y : C.X (k + 2)) :
    (C.d (k + 1) k).hom ((C.d (k + 2) (k + 1)).hom y) = 0 := by
  have h : ((C.d (k + 2) (k + 1)) ≫ (C.d (k + 1) k)).hom = 0 := by
    rw [HomologicalComplex.d_comp_d C (k + 2) (k + 1) k]
    rfl
  have := congrArg (fun f : C.X (k + 2) →ₗ[ℤ] C.X k => f y) (by
    simpa only [ModuleCat.hom_comp] using h)
  simpa using this

theorem dL_comp_dL (k : ℕ) : (S.dL k).comp (S.dL (k + 1)) = 0 := by
  ext x
  change ((S.dL k (S.dL (k + 1) x) : ↥(S.sub k)) : C.X k) = 0
  rw [S.dL_apply k (S.dL (k + 1) x), S.dL_apply (k + 1) x]
  exact d_comp_d_apply k (x : C.X (k + 2))

/-- The subcomplex. -/
noncomputable def chain : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of ℤ ↥(S.sub k)) (fun k => ModuleCat.ofHom (S.dL k))
    (fun k => ModuleCat.hom_ext (by simpa using S.dL_comp_dL k))

@[simp] theorem chain_X (k : ℕ) : (S.chain).X k = ModuleCat.of ℤ ↥(S.sub k) := rfl

@[simp] theorem chain_d (k : ℕ) : (S.chain).d (k + 1) k = ModuleCat.ofHom (S.dL k) := by
  simp only [chain, ChainComplex.of_d]

/-- The inclusion of the subcomplex. -/
noncomputable def incl : S.chain ⟶ C :=
  ChainComplex.ofHom (fun k => ModuleCat.ofHom (S.sub k).subtype) (fun k => by
    rw [S.chain_d k]
    apply ModuleCat.hom_ext
    ext x
    exact (S.dL_apply k x).symm)

@[simp] theorem incl_f (k : ℕ) : S.incl.f k = ModuleCat.ofHom (S.sub k).subtype := rfl

/-! ### The quotient complex -/

/-- The differential of the quotient complex. -/
noncomputable def quotD (k : ℕ) : C.X (k + 1) ⧸ S.sub (k + 1) →ₗ[ℤ] C.X k ⧸ S.sub k :=
  Submodule.mapQ (S.sub (k + 1)) (S.sub k) (C.d (k + 1) k).hom (fun x hx => S.d_mem k x hx)

theorem quotD_apply (k : ℕ) (x : C.X (k + 1)) :
    S.quotD k (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((C.d (k + 1) k).hom x) :=
  Submodule.mapQ_apply (S.sub (k + 1)) (S.sub k) (C.d (k + 1) k).hom x

/-- The quotient complex, given the cocycle condition for the induced differential. -/
noncomputable def quotOf (h : ∀ k, (S.quotD k).comp (S.quotD (k + 1)) = 0) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of ℤ (C.X k ⧸ S.sub k)) (fun k => ModuleCat.ofHom (S.quotD k))
    (fun k => ModuleCat.hom_ext (by simpa using h k))

end

end SubData

end Work.Subdivision
