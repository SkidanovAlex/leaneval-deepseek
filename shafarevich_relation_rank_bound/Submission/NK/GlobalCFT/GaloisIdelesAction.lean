/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.GaloisIdeles
import Submission.NK.GlobalCFT.Galois.globalCFT_eventually_smul_mem
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp

/-!
# The action of `Gal(L/K)` on the idèle group

Using the canonical local field isomorphism `NK.GlobalCFT.Place.localRingEquiv`, we define the
action of `Gal(L/K) = (L ≃ₐ[K] L)` on `𝕀 L` by `(σ · x)_w = σ_*(x_{σ⁻¹ w})` and record its
elementary properties.

## Main definitions

* the `SMul (L ≃ₐ[K] L) (Idele L)` instance.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Idele

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- `Gal(L/K)` acts on the idèles by `(σ · x)_w = σ_*(x_{σ⁻¹ w})`, where `σ_*` is the canonical
local field isomorphism (applied through its inverse at `w`). -/
noncomputable instance : SMul (L ≃ₐ[K] L) (Idele L) where
  smul σ x :=
    ⟨fun w => Units.map (Place.localRingEquiv σ⁻¹ w).symm.toMonoidHom (x (σ⁻¹ • w)),
      NK.GlobalCFT.Galois.globalCFT_eventually_smul_mem σ x⟩

/-- The component formula for the action of `Gal(L/K)` on idèles. -/
theorem smul_apply (σ : L ≃ₐ[K] L) (x : Idele L) (w : Place L) :
    (σ • x) w =
      Units.map (Place.localRingEquiv σ⁻¹ w).symm.toMonoidHom (x (σ⁻¹ • w)) := rfl

end Idele

end NK.GlobalCFT
