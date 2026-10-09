/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The coinduced module `G → A` as an `𝔽_p[G]`-module

Step 1 of the proof of Theorem 15 of Schmidt–Wingberg uses Proposition 6 with the *induced*
module `T = Ind_{G_p}^G 𝔽_p`, i.e. (for `𝔽_p`-coefficients) the coinduced module `G → 𝔽_p` with
the action `(γ • f) x = f (x * γ)`.

That action is registered by `Submission.InducedModules` (and used throughout `Work.Tate`), but
the accompanying `SMulCommClass G (ZMod p) (G → A)` — the fact that scalar multiplication by
`𝔽_p` commutes with the `G`-action, i.e. that the coinduced action is `𝔽_p`-linear — is not
registered as an instance anywhere in the workspace.  It is proved here as a *named fact*, so
that a user who needs `G → 𝔽_p` as an `𝔽_p[G]`-module can install it locally:

```lean
haveI := Work.CohomologicalShrinking.coindSMulCommClass p G (ZMod p)
```

(We do not register it as a global instance: that instance belongs to `Submission.InducedModules`,
not to this chapter, and adding it here could interfere with other work in the workspace.)

## Main result

* `Work.CohomologicalShrinking.coindSMulCommClass`.
-/

import Mathlib
import Submission.InducedModules
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking

/-- The coinduced action of `G` on the function space `G → A` commutes with scalar
multiplication by `𝔽_p`: `g • (c • f) = c • (g • f)`.  Hence `G → A` is an `𝔽_p[G]`-module
whenever `A` is a `ZMod p`-module and `G` acts on `G → A` by the coinduced action
`(g • f) x = f (x * g)`. -/
theorem coindSMulCommClass (p : ℕ) (G : Type*) [Group G] (A : Type*) [AddCommGroup A]
    [Module (ZMod p) A] : SMulCommClass G (ZMod p) (G → A) where
  smul_comm g c f := by
    ext x
    rfl

end Work.CohomologicalShrinking
