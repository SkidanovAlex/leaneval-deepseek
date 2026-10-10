import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.exists_shift_pow_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **The rational-point condition of the twist is independent of the chosen generator.**
`QuinticTwist.TorsorHasPointPow D k` is the statement `∃ R, σ ^ k R - R = P` — that the class of
the cocycle `σ ^ k ↦ P` is trivial — and `D.toTorsor.HasPoint` is `cls = 1` in the multiplicative
presentation of `H¹(ℤ/5, E(L))` (`Submission/Work/TorsorExistence/Twist.lean`,
`Work.Arithmetic.Torsor.HasPoint`), i.e. `D.cls = 0` in the additive one.  For `k` coprime to `5`
the two agree.

Ingredients: `Work.TorsorExistence.cls_eq_zero_iff` (`cls = 0 ↔ ∃ R, σ R - R = P`) and
`exists_shift_pow_iff` at `x = D.PL`.  Used to transport `TwistCurveModel` across the choice of
generator (see `TwistBridges`). -/
theorem torsorHasPointPow_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) {k : ℕ} (hk : k % 5 ≠ 0) :
    QuinticTwist.TorsorHasPointPow D k ↔ D.toTorsor.HasPoint := by
  -- `D.toTorsor.HasPoint` is `D.cls = 0`, the additive presentation of the class.
  have htp : D.toTorsor.HasPoint ↔ D.cls = 0 := by
    show Multiplicative.ofAdd (Work.TorsorExistence.QuinticTwist.cls D) = 1 ↔ D.cls = 0
    exact ofAdd_eq_one
  -- `TorsorHasPointPow D k` unfolds to the `(σ ^ k - 1)`-coboundary condition on `P`.
  rw [show QuinticTwist.TorsorHasPointPow D k ↔
      (∃ R : D.LPoints, QuinticTwist.galMapPow D k R - R = D.PL) from Iff.rfl]
  -- Generator-independence of the coboundary condition (`P` is fixed, `5 • P = 0`).
  rw [exists_shift_pow_iff D D.PL D.galMap_PL D.five_smul_PL hk]
  -- The `(σ - 1)`-coboundary condition is `cls = 0`.
  rw [show (∃ R : D.LPoints, D.galMap R - R = D.PL) ↔ D.cls = 0 from
    (Work.TorsorExistence.cls_eq_zero_iff D).symm]
  exact htp

end Work.Twist
