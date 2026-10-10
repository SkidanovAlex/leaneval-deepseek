import Mathlib
import Submission.Work.TorsorExistence.Twist

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.TorsorExistence

/-- A non-trivial class gives a pointless twist: in the `Work.Arithmetic.Torsor` interface,
`toTorsor D` is pointless (`cls ≠ 1`) whenever the class of the cocycle `σ ↦ P` is non-zero
(`D.toTorsor.cls = Multiplicative.ofAdd (D.cls)`, and `ofAdd 0 = 1`). -/
theorem toTorsor_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (h : D.Pointless) : D.toTorsor.Pointless := by
  show Multiplicative.ofAdd D.cls ≠ 1
  intro hp
  rw [ofAdd_eq_one] at hp
  exact h hp

end Work.TorsorExistence
