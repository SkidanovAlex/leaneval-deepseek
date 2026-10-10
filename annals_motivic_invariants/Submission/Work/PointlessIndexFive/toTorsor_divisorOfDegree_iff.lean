import Mathlib
import Submission.Work.PointlessIndexFive.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- The divisor-degree bookkeeping of the twist, in the additive presentation: `toTorsor D`
carries a divisor of degree `n` iff `n • cls = 0`. -/
theorem toTorsor_divisorOfDegree_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (n : ℕ) : D.toTorsor.DivisorOfDegree n ↔ n • D.cls = 0 := by
  -- `toTorsor D` is the `Torsor` whose class is `Multiplicative.ofAdd D.cls`, and
  -- `DivisorOfDegree T n` is `T.cls ^ n = 1`; the rest is the defining relation
  -- `ofAdd (n • x) = ofAdd x ^ n` of the type tag `Multiplicative`, together with the
  -- injectivity of the underlying equivalence `ofAdd : α ≃ Multiplicative α`.
  show (Multiplicative.ofAdd D.cls) ^ n = 1 ↔ n • D.cls = 0
  rw [← ofAdd_nsmul]
  constructor
  · intro h
    exact Multiplicative.ofAdd.injective (by simpa using h)
  · intro h
    exact congrArg Multiplicative.ofAdd h

end Work.PointlessIndexFive
