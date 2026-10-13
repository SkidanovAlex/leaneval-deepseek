/-
# The full profile is jointly `α`-Hölder in `(z,τ)` at fixed angle

This file provides the packaged form `Work.FTS.Regularity.profFullHolder` of the joint
`(z,τ)`–`α`-Hölder continuity of the *full* self-similar profile
`profFull α g = F_* + g` (the `F_*`-part being `Lipschitz` in `z`, the `g`-part being the joint
`α`-Hölder jet of `RegPkg'.hg`), specialized to a common fixed angle `θ ∈ Iθ`.

The analytic content (the `F_*`/`g` split and the two regimes of the metric
`|Δz| + |Δτ|`) is proved in `Submission/Work/FTS/Regularity/physVort_holder_time.lean` as
`profFull_holder_ztau`; we restate it here under the name requested by the consumer so that the
name is available without importing the whole time-Hölder development.

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
  Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.FireFix.Prime.physVort_holder_time
import Submission.Work.FTS.RegPkgGal.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-- **Joint `α`-Hölder continuity of the full profile in `(z,τ)` at a fixed angle.**

For a regularity package `RegPkg' α S A B g` there is a constant `N ≥ 0` such that for every
fixed angle `θ ∈ Iθ` and all `z, z' ≥ 0`, `τ, τ' ∈ [0,S]`,

  `|F(z,θ,τ) - F(z',θ,τ')| ≤ N·(|z-z'| + |τ-τ'|)^α`,  `F = profFull α g = F_* + g`,

i.e. the full profile is jointly `α`-Hölder on the strip at fixed angle. -/
theorem profFullHolder {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ z z' θ τ τ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      τ ∈ Set.Icc 0 S → τ' ∈ Set.Icc 0 S →
      |profFull α g z θ τ - profFull α g z' θ τ'| ≤ N * (|z - z'| + |τ - τ'|) ^ α :=
  profFull_holder_ztau h

end Work.FTS.FireFix.Prime
