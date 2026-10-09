/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.UniverseWeakNU`: the weak Neukirch–Uchida chain at an arbitrary universe

Umbrella module.  Import `Submission.NK.UniverseWeakNU.All` to get the whole chapter.

## What the chapter delivers

The weak-Neukirch–Uchida chain of `Submission/Work/WeakNU/` and `Submission/Work/UchidaKummer/`,
re-run with `Type` replaced by `Type u`, so that its conclusion

`NK.ReconstructField.LevelIsoInput ϕ hϕ`

is available for `{K₁ K₂ K₁' K₂' : Type u}` (the endgame hypothesis of the Neukirch–Uchida
reconstruction is universe-polymorphic).  The end goals are

* `NK.UniverseWeakNU.perlisGassmannInputU : ChebotarevFrobeniusInputU → PerlisGassmannInputU`;
* `NK.UniverseWeakNU.isWeakUchidaU : IsUchidaModuleDataU 2 → PerlisGassmannInputU → IsWeakUchidaU 2`;
* `NK.UniverseWeakNU.levelIsoInput_of_isWeakUchidaU : IsWeakUchidaU ℓ → LevelIsoInput ϕ hϕ`;
* `NK.UniverseWeakNU.levelIsoInput_of_chebotarevU :
    IsUchidaModuleDataU 2 → ChebotarevFrobeniusInputU → LevelIsoInput ϕ hϕ`
  (and its refinement `…_and_primeCountU`), at `{K₁ K₂ K₁' K₂' : Type u}`;
* the `.{0}` instances `NK.UniverseWeakNU.isWeakUchida` and
  `NK.UniverseWeakNU.levelIsoInput_of_chebotarev` (consistency check).

**The fields may live in *independent* universes.**  `Submission.neukirch_uchida` (and
`NK.Reconstruct.exists_sigma_of_weakNeukirchUchida_and_levelIso`) are stated with
`{K₁ K₂ K₁' K₂' : Type*}`, i.e. four independent universe parameters.  `ArbitraryUniverses.lean`
removes the uniformity assumption of the chain above: the §6 argument only evaluates the module data
at the *common field* it constructs, so the inputs are needed at a single, freely chosen **working
universe** `w`, while the fields live in `u₁ u₂ u₃ u₄`.  With `w = 0` this shows that the **existing
universe-0 inputs** `NK.UchidaKummer.IsUchidaModuleData 2` and
`NK.WeakNU.ChebotarevFrobeniusInput` already give

```lean
NK.UniverseWeakNU.levelIsoInput_of_chebotarev_universePoly :
    NK.UchidaKummer.IsUchidaModuleData 2 → NK.WeakNU.ChebotarevFrobeniusInput →
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) → IsHomeomorph ϕ →
    NK.ReconstructField.LevelIsoInput ϕ hϕ          -- for {K₁ K₂ K₁' K₂' : Type*}
```

i.e. the endgame hypothesis at arbitrary universes from the *same* residual catalogue as at `Type 0`;
see `Usage.lean` (patterns 0 and 0').

The Čebotarev leaf is itself reduced, at `Type u` as at `Type 0`, to the *abelian* case of
Čebotarev's density theorem at `Type u`:

* `NK.UniverseWeakNU.chebotarevFrobeniusInputU_of_abelianU :
    AbelianChebotarevDensityU → ChebotarevFrobeniusInputU`;
* `NK.UniverseWeakNU.chebotarevFrobeniusInputU_of_lfunctionsU` — the same from the Hecke
  `L`-function input `NK.Chebotarev.AbelianLFunctions` at `Type u`.

See `README.md` for the interface, the universe conventions, the axiom audit, and the exact
statements a future prover of the leaves (the abelian case of Čebotarev at `Type u`; Uchida's module
data at `Type u`) should target.
-/

import Submission.NK.UniverseWeakNU.Defs
import Submission.NK.UniverseWeakNU.PrimeOrbitU
import Submission.NK.UniverseWeakNU.ChebotarevU
import Submission.NK.UniverseWeakNU.ChebotarevLFunctionU
import Submission.NK.UniverseWeakNU.chebotarevInfiniteU_of_abelianU
import Submission.NK.UniverseWeakNU.chebotarevFrobeniusInputU_of_infiniteU
import Submission.NK.UniverseWeakNU.ChebotarevAssemblyU
import Submission.NK.UniverseWeakNU.UchidaModuleDataU
import Submission.NK.UniverseWeakNU.primeCountAboveU_eq_primeOrbitCountU
import Submission.NK.UniverseWeakNU.primeOrbitCountU_eq_card_orbits_cosetU
import Submission.NK.UniverseWeakNU.decompositionSubgroup_eq_zpowers_of_isFrobAtU
import Submission.NK.UniverseWeakNU.primeCountAboveU_under_eq_primesOverRatU
import Submission.NK.UniverseWeakNU.PrimeCountU
import Submission.NK.UniverseWeakNU.IsomorphicAbsGaloisU
import Submission.NK.UniverseWeakNU.UchidaU
import Submission.NK.UniverseWeakNU.MainWeak
import Submission.NK.UniverseWeakNU.Main
import Submission.NK.UniverseWeakNU.ArbitraryUniverses
import Submission.NK.UniverseWeakNU.Pinned
import Submission.NK.UniverseWeakNU.Usage
import Submission.NK.UniverseWeakNU.Zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
