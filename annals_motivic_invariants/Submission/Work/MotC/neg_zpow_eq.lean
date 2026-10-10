import Mathlib
import Submission.Work.MotC.TransData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC

/-- The negation pullback `TD.neg` is an involution: applying `neg_τ` at the origin `Q = 0`
gives `(neg.trans 1).trans neg = τ 0 = 1`, i.e. `neg * neg = 1`. -/
theorem neg_mul_neg_eq_one {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (TD : Work.MotC.TransData D) :
    TD.neg * TD.neg = 1 := by
  have h := TD.neg_τ 0
  simp only [TD.τ_zero, neg_zero] at h
  show TD.neg.trans TD.neg = AlgEquiv.refl
  ext x
  have hx := congrArg (fun e => e x) h
  simpa using hx

theorem neg_zpow_eq {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (TD : Work.MotC.TransData D) (ε : ℤˣ) :
    TD.neg ^ (ε : ℤ) = TD.neg := by
  have hε : (ε : ℤ) = 1 ∨ (ε : ℤ) = -1 := by
    rcases Int.units_eq_one_or ε with h | h
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr (by rw [h]; simp)
  rcases hε with h | h
  · rw [h, zpow_one]
  · rw [h, zpow_neg_one, inv_eq_of_mul_eq_one_right (neg_mul_neg_eq_one D TD)]

end Work.MotC
