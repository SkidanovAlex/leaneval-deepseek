/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The abelian case at an arbitrary universe, from the Hecke `L`-function input

Universe-polymorphic copy of `NK.ChebotarevGeneral.abelianChebotarevDensity_of_lfunctions`
(`Submission/Work/ChebotarevGeneral/Main.lean`): the per-extension Hecke `L`-function input
`NK.Chebotarev.AbelianChebotarevOfLFunctions` (`{K L : Type*}`, so usable at `Type u`) upgrades the
"for every abelian extension" input to the single statement
`NK.UniverseWeakNU.AbelianChebotarevDensityU`.

The *analytic* input itself — `NK.Chebotarev.AbelianLFunctions K N` for every abelian finite Galois
`N/K` in `Type u` — is a leaf: at `Type 0` it is discharged by `Submission/Work/HeckeL/` from the
regularity of Artin `L`-functions at `1`, and the polymorphic bridge
`NK.HeckeL.Consequences.abelianLFunctions` (`{K L : Type*}`) converts the latter into the former,
but the derivation of that analytic input is the `HeckeL` chapter's business.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.ChebotarevU
import Submission.NK.Chebotarev.AbelianChebotarevOfLFunctions
import Submission.NK.Chebotarev.LFunctions
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UniverseWeakNU

noncomputable section

universe u

/-- **The abelian case of Čebotarev's density theorem, at an arbitrary universe, from the Hecke
`L`-function input.**  Copy of `NK.ChebotarevGeneral.abelianChebotarevDensity_of_lfunctions`. -/
theorem abelianChebotarevDensityU_of_lfunctionsU
    (h : ∀ (K N : Type u) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
      [FiniteDimensional K N] [IsGalois K N], (∀ a b : Gal(N/K), a * b = b * a) →
      NK.Chebotarev.AbelianLFunctions K N) : AbelianChebotarevDensityU.{u} := by
  intro K N _ _ _ _ _ _ _ hcomm σ
  exact NK.Chebotarev.AbelianChebotarevOfLFunctions hcomm (h K N hcomm) σ

end

end NK.UniverseWeakNU
