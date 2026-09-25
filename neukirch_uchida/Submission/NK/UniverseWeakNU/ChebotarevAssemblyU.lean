/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ChebotarevFrobeniusInputU` from the abelian case at `Type u`

Assembling `Submission/Work/UniverseWeakNU/chebotarevInfiniteU_of_abelianU.lean`
(the cyclic case implies the general case, in existence form) and
`Submission/Work/UniverseWeakNU/chebotarevFrobeniusInputU_of_infiniteU.lean`
(the passage from an arbitrary number-field base to the rational base of
`NK.UniverseWeakNU.ChebotarevFrobeniusInputU`):

* `NK.UniverseWeakNU.chebotarevFrobeniusInputU_of_abelianU :
    AbelianChebotarevDensityU → ChebotarevFrobeniusInputU`
  — the polymorphic analogue of `NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_abelian`;
* `NK.UniverseWeakNU.chebotarevFrobeniusInputU_of_lfunctionsU` — the same from the Hecke
  `L`-function input, the analogue of `..._of_lfunctions`.

Consequently the Čebotarev leaf `ChebotarevFrobeniusInputU` of the polymorphic
weak-Neukirch–Uchida chain is reduced, exactly as at `Type 0`, to the **abelian case** of Čebotarev's
density theorem at `Type u` (`AbelianChebotarevDensityU`), and hence to the analytic input
`NK.Chebotarev.AbelianLFunctions` at `Type u`.  See `README.md` §5.1.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.ChebotarevU
import Submission.NK.UniverseWeakNU.chebotarevInfiniteU_of_abelianU
import Submission.NK.UniverseWeakNU.chebotarevFrobeniusInputU_of_infiniteU
import Submission.NK.UniverseWeakNU.ChebotarevLFunctionU

namespace NK.UniverseWeakNU

noncomputable section

universe u

/-- **Čebotarev at `Type u` from its abelian case**, the polymorphic analogue of
`NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_abelian`. -/
theorem chebotarevFrobeniusInputU_of_abelianU (h : AbelianChebotarevDensityU.{u}) :
    ChebotarevFrobeniusInputU.{u} :=
  chebotarevFrobeniusInputU_of_infiniteU (chebotarevInfiniteU_of_abelianU h)

/-- **Čebotarev at `Type u` from the Hecke `L`-function input**, the polymorphic analogue of
`NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_lfunctions`. -/
theorem chebotarevFrobeniusInputU_of_lfunctionsU
    (h : ∀ (K N : Type u) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
      [FiniteDimensional K N] [IsGalois K N], (∀ a b : Gal(N/K), a * b = b * a) →
      NK.Chebotarev.AbelianLFunctions K N) : ChebotarevFrobeniusInputU.{u} :=
  chebotarevFrobeniusInputU_of_abelianU (abelianChebotarevDensityU_of_lfunctionsU h)

end

end NK.UniverseWeakNU
