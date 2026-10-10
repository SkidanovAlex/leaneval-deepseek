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

/-- **The pointlessness of a quintic twist does not depend on the chosen generator of the Galois
group.**  `QuinticTwist.PointlessPow D k` is pointlessness of the twist rebuilt with the generator
`σ ^ k` in place of `σ` (`Submission/Work/Twist/Defs.lean`: it is
`¬ ∃ R, σ ^ k R - R = P`), and for `k` coprime to `5` it agrees with `D.Pointless`; `k % 5 ≠ 0`
is exactly the condition for `σ ^ k` to be a generator of the cyclic group `Gal(L/𝕜)`.

This is the well-posedness of the arithmetic residual `HasPointlessTwist 𝕜`: a prover may build
the twist data with any generator and read off the same conclusion.  The ingredient is
`exists_shift_pow_iff` at `x = P` (`D.galMap_PL`, `D.five_smul_PL`), together with
`Work.PointlessIndexFive.pointless_iff_not_exists_shift` and `QuinticTwist.galMapPow_one`. -/
theorem pointless_pow_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) {k : ℕ} (hk : k % 5 ≠ 0) :
    QuinticTwist.PointlessPow D k ↔ D.Pointless := by
  -- `D.Pointless` is the coboundary criterion for the chosen generator `σ`; `PointlessPow D k`
  -- is the same criterion for `σ ^ k`, so it suffices to compare the two coboundary conditions.
  rw [Work.PointlessIndexFive.pointless_iff_not_exists_shift]
  exact not_congr
    (exists_shift_pow_iff D D.PL D.galMap_PL D.five_smul_PL hk)

end Work.Twist
