/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SubComplex

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The quotient complex is a complex

`SubData.quotD k` is the differential induced by `C.d (k+1) k` on the quotient
`C.X (k+1) ⧸ S.sub (k+1) → C.X k ⧸ S.sub k` (see
`Submission.Work.Subdivision.SubComplex`).  This file proves that consecutive
induced differentials compose to zero:

  `(S.quotD k).comp (S.quotD (k + 1)) = 0`.

This is exactly the hypothesis needed by `SubData.quotOf`, so that the quotient
of a chain complex by a subcomplex is again a chain complex.

## Note on the `ℤ`-module diamond

The quotient module structures used by `SubData.quotD` are the ones fixed at
definition time in `SubComplex.lean` (`SubData.instModuleQuot`), not the
canonical `AddCommGroup.toIntModule` that instance search picks up on its own.
We therefore re-introduce those three instances explicitly in the proof, so
that instance synthesis produces the very structures appearing in the
statement.
-/

namespace Work.Subdivision

set_option linter.style.haveILetI false in
theorem quotD_comp_quotD {C : ChainComplex (ModuleCat ℤ) ℕ} (S : SubData C) (k : ℕ) :
    (S.quotD k).comp (S.quotD (k + 1)) = 0 := by
  -- Recover the three quotient `ℤ`-module structures fixed by `SubData.quotD`.
  letI i₂ : Module ℤ (C.X (k + 1 + 1) ⧸ S.sub (k + 1 + 1)) :=
    Submodule.Quotient.module (S.sub (k + 1 + 1))
  letI i₁ : Module ℤ (C.X (k + 1) ⧸ S.sub (k + 1)) :=
    Submodule.Quotient.module (S.sub (k + 1))
  letI i₀ : Module ℤ (C.X k ⧸ S.sub k) :=
    Submodule.Quotient.module (S.sub k)
  refine LinearMap.ext ?_
  intro x
  refine Submodule.Quotient.induction_on (p := S.sub (k + 1 + 1)) x ?_
  intro y
  rw [LinearMap.comp_apply, S.quotD_apply, S.quotD_apply]
  rw [SubData.d_comp_d_apply k y]
  simp

end Work.Subdivision
