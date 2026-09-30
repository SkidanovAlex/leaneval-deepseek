/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SubComplex
import Submission.Work.Subdivision.quotD_comp_quotD

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The quotient complex of a `SubData` and the projection onto it

Completing `Submission.Work.Subdivision.SubComplex`: the quotient complex
`SubData.quot` (using the cocycle lemma `Work.Subdivision.quotD_comp_quotD`), the
projection `SubData.proj` and the short complex
`0 → S.chain → C → S.quot → 0`.
-/

namespace Work.Subdivision

open CategoryTheory

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

namespace SubData

variable (S : SubData C)

section

/-- Fix the ℤ-module structures (see `SubComplex.lean`). -/
local instance instModuleSubQ {k : ℕ} : Module ℤ ↥(S.sub k) := (S.sub k).module

/-- Fix the ℤ-module structures (see `SubComplex.lean`). -/
local instance instModuleQuotQ {k : ℕ} : Module ℤ (C.X k ⧸ S.sub k) :=
  Submodule.Quotient.module (S.sub k)

/-- The quotient complex of `C` by the subcomplex `S`. -/
noncomputable def quot : ChainComplex (ModuleCat ℤ) ℕ :=
  S.quotOf fun k => quotD_comp_quotD S k

theorem quot_X (k : ℕ) : (S.quot).X k = ModuleCat.of ℤ (C.X k ⧸ S.sub k) := by
  simp only [quot, quotOf, ChainComplex.of_X]

theorem quot_d (k : ℕ) : (S.quot).d (k + 1) k = ModuleCat.ofHom (S.quotD k) := by
  simp only [quot, quotOf, ChainComplex.of_d]

/-- The projection onto the quotient complex. -/
noncomputable def proj : C ⟶ S.quot :=
  ChainComplex.ofHom (fun k => ModuleCat.ofHom (Submodule.mkQ (S.sub k))) (fun k => by
    rw [S.quot_d k]
    apply ModuleCat.hom_ext
    ext x
    exact (S.quotD_apply k x).symm)

@[simp] theorem proj_f (k : ℕ) : S.proj.f k = ModuleCat.ofHom (Submodule.mkQ (S.sub k)) := rfl

/-- The short complex `0 → S.chain → C → S.quot → 0`, given the vanishing of the
composite of the inclusion and the projection. -/
noncomputable def shortComplexOf (w : S.incl ≫ S.proj = 0) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk S.incl S.proj w

end

end SubData

end Work.Subdivision
