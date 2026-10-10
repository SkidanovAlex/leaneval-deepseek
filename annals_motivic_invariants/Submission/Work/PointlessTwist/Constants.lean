/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessTwist
-/
import Mathlib
import ChallengeDeps
import Submission.Work.PointlessTwist.FunctionField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The concrete constant curve of the function-field classes

For the classes (b), (c), (d), the curve of the twist is the **Tate normal form with a parameter
`c` in the field of constants `𝔽`**, base-changed to the function field `𝕜 = 𝔽(t)`:

  `E(c) : y² + (1 - c)xy - cy = x³ - cx²`,   `P = (0,0)` of exact order `5`

(`Work.TorsorExistence.Tate.tateCurve`, `Tate.tate_five_smul`).  Because `c ∈ 𝔽`, the curve is
*constant*: it is the base change of the curve `E(c)/𝔽`, which is what makes the specialization /
trivial-action arguments apply.  This file fixes that concrete datum (`ConstantTateData`) and its
API; `Work.PointlessTwist.Constants` also records the two ways of exhibiting a good `c` (`c ∈ 𝔽`
with `Δ ≠ 0` and `j ≠ 1728`) in the three classes: an infinite field (`Tate.exists_tate_param`) and
the specific finite field `𝔽₁₁`.

## Main results

* `ConstantTateData 𝔽 𝕜 c` — the `FiveTorsionCurve 𝕜` whose curve is `(Tate.tateCurve c)` base
  changed to `𝕜`, with the Silverman A.1.2 datum.
* `ConstantTateData.constantsOnly_to_pointless` — **the reduction of the class to the classical
  `E(𝔽(t)) = E(𝔽)`**: for any cyclic quintic extension `L/𝕜` over which `σ` restricts to
  `Point.map (restrictScalars 𝔽 gen)`, the residual `ConstantsOnly 𝔽 (Tate.tateCurve c) L` gives
  `PointlessOf`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.PointlessTwist

noncomputable section

/-- **The concrete constant Tate-model twist curve over a tower `𝔽 ⊆ 𝕜`.**  The `FiveTorsionCurve 𝕜`
whose curve is the base change to `𝕜` of the Tate normal form with parameter `c ∈ 𝔽`, and whose
marked point is the base change of `(0,0)`.  Since `c ∈ 𝔽`, the curve is constant, so every
`L`-point of it is constant (`ConstantsOnly`) and the Galois action is trivial. -/
structure ConstantTateData (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (𝕜 : Type) [Field 𝕜]
    [DecidableEq 𝕜] [Algebra 𝔽 𝕜] (c : 𝔽) where
  /-- The twist curve over `𝕜`. -/
  C₅ : FiveTorsionCurve 𝕜
  /-- It is the base change of the constant Tate model with parameter `c`. -/
  E_eq : C₅.E = (Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜
  /-- The marked point of order `5` is the base change of `(0,0)`. -/
  P : WeierstrassCurve.Affine.Point (Work.TorsorExistence.Tate.tateCurve c)
  /-- `(0,0)` is `5`-torsion (Tate normal form). -/
  five_smul : (5 : ℕ) • P = 0
  /-- It is not the origin. -/
  P_ne_zero : P ≠ 0
  /-- The marked point of `C₅` is the base change of `P`. -/
  P_eq : C₅.P = E_eq ▸ WeierstrassCurve.Affine.Point.baseChange
    (W' := Work.TorsorExistence.Tate.tateCurve c) 𝔽 𝕜 P

namespace ConstantTateData

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
  [Algebra 𝔽 𝕜] {c : 𝔽}

/-- The curve of a `ConstantTateData` is the base change of a curve over `𝔽`; recorded for
rewriting. -/
theorem baseChange_eq (d : ConstantTateData 𝔽 𝕜 c) :
    d.C₅.E = (Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜 := d.E_eq

end ConstantTateData

end

end Work.PointlessTwist
