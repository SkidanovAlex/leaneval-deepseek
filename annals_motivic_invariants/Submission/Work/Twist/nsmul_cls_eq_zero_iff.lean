import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.quot_mk_eq_zero_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **The divisor-degree condition of the twist, in element form.**  `n • cls = 0` in
`H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)` if and only if the point `n • P` is a coboundary, i.e. iff
`n • P = σ R - R` for some `R ∈ E(L)`.

The class `n • cls` is the class of the cocycle `n • P`: `n • P` lies in `ker N` because
`N(n • P) = 5n • P = 0` (`norm_eq_nsmul` and `5 • P = 0`), and the quotient map sends `P` to
`cls` and is additive (`map_nsmul`).  The element form is what the orbit-divisor argument
computes geometrically (`n • cls = 0` iff the twist carries a rational divisor of degree `n`);
the case `n = 1` is `cls_eq_zero_iff`. -/
theorem nsmul_cls_eq_zero_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (n : ℕ) :
    n • D.cls = 0 ↔ ∃ R : D.LPoints, D.shift R = (n : ℕ) • D.PL := by
  -- `n • P` is again a cocycle: `N(n • P) = n • N(P) = n • 0 = 0`.
  have hmem : (n : ℕ) • D.PL ∈ D.cocycles := by
    rw [Work.TorsorExistence.QuinticTwist.cocycles, AddMonoidHom.mem_ker, map_nsmul,
      D.norm_PL, nsmul_zero]
  -- `n • cls` is the class of the cocycle `n • P`, because `mk'` is additive.
  have hcls : (n : ℕ) • D.cls =
      (QuotientAddGroup.mk' D.coboundaries (⟨(n : ℕ) • D.PL, hmem⟩ : D.cocycles) : D.H1) := by
    rw [Work.TorsorExistence.QuinticTwist.cls]
    exact (map_nsmul (QuotientAddGroup.mk' D.coboundaries) n ⟨D.PL, D.norm_PL⟩).symm
  -- A class vanishes iff its cocycle is a coboundary.
  rw [hcls, Work.Twist.quot_mk_eq_zero_iff]

end Work.Twist
