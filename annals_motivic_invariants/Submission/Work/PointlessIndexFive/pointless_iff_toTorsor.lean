import Mathlib
import Submission.Work.PointlessIndexFive.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- `D.Pointless` (`cls ≠ 0` in `H¹(ℤ/5,E(L))`) is `D.toTorsor.Pointless` (`cls ≠ 1` in the
`Work.Arithmetic.Torsor` presentation). -/
theorem pointless_iff_toTorsor {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) :
    D.Pointless ↔ D.toTorsor.Pointless := by
  -- `D.Pointless` is `cls D ≠ 0` and `D.toTorsor.cls = Multiplicative.ofAdd (cls D)`, so the
  -- two statements are `cls D ≠ 0` and `Multiplicative.ofAdd (cls D) ≠ 1`, which are equivalent
  -- by `ofAdd_eq_one`.
  show D.cls ≠ 0 ↔ Multiplicative.ofAdd D.cls ≠ 1
  exact (not_congr ofAdd_eq_one).symm

end Work.PointlessIndexFive
