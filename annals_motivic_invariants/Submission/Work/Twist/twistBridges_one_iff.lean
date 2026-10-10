import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.torsorHasPointPow_iff
import Submission.Work.Twist.torsorDivisorOfDegreePow_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **`TwistBridges` at `k = 1` is exactly the pair of `TwistCurveModel` bridge conditions.**
`TwistBridges D C 1` (`Submission/Work/Twist/Defs.lean`) unfolds to
`C(𝕜) ≠ ∅ ↔ (P is a (σ - 1)-coboundary)` and `HasRatDivisorOfDegree 𝕜 C n ↔ (nP is one)`; the
right-hand sides are `D.toTorsor.HasPoint` and `D.toTorsor.DivisorOfDegree n` by
`Work.TorsorExistence.cls_eq_zero_iff`, `nsmul_cls_eq_zero_iff` and
`Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff`.  This makes precise that the geometric
residual is the pair of bridge conditions stated in `TwistCurveModel`. -/
theorem twistBridges_one_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) {C : Scheme} [C.Over (Spec (CommRingCat.of 𝕜))] :
    TwistBridges D C 1 ↔
      (Work.Arithmetic.HasRatPoint 𝕜 C ↔ D.toTorsor.HasPoint) ∧
        (∀ n : ℕ, Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C n ↔
          D.toTorsor.DivisorOfDegree n) := by
  -- `1` is coprime to `5`, so both presentations of the class agree with the `k = 1` one.
  have hk : (1 : ℕ) % 5 ≠ 0 := by decide
  constructor
  · -- `TwistBridges D C 1 → ⋯`: transport the two bridge conditions to the torsor's own
    -- additive/multiplicative presentation of `H¹(ℤ/5, E(L))`.
    rintro ⟨h₁, h₂⟩
    exact ⟨h₁.trans (torsorHasPointPow_iff D hk),
      fun n => (h₂ n).trans (torsorDivisorOfDegreePow_iff D hk n)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.trans (torsorHasPointPow_iff D hk).symm,
      fun n => (h₂ n).trans (torsorDivisorOfDegreePow_iff D hk n).symm⟩

end Work.Twist
