import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.PointlessIndexFive.shift_mem_cocycles

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **A `σ`-invariant coboundary is `5`-torsion.**  If `x = σ R - R` is fixed by `σ` (every
`𝕜`-rational point is, and every `n • P` is), then `5 • x = 0`.  Equivalently, the image of
`σ - 1 : E(L) → E(L)` meets the subgroup of `σ`-invariant points in the `5`-torsion subgroup of
`E(L)`.

Short proof from existing lemmas: `x = shift R` lies in `ker N`
(`Work.PointlessIndexFive.shift_mem_cocycles`), so `norm x = 0`, while `σ`-invariance gives
`norm x = 5 • x` (`Work.TorsorExistence.QuinticTwist.norm_eq_nsmul`).  Alternatively the orbit
identity `σ ^ i R = R + i • x` gives `N R = 5R + 10x` and `N(σR) = 5R + 15x`, and `N ∘ σ = N`. -/
theorem shift_eq_nsmul_eq_zero {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) {x R : D.LPoints} (hx : D.galMap x = x)
    (h : D.galMap R - R = x) : (5 : ℕ) • x = 0 := by
  -- `x = σR - R = shift R`, and every coboundary lies in `ker N`.
  have h1 : D.norm x = 0 := by
    have hmem := Work.PointlessIndexFive.shift_mem_cocycles D R
    rw [Work.TorsorExistence.QuinticTwist.cocycles, AddMonoidHom.mem_ker] at hmem
    have hshift : D.shift R = x := h
    rw [hshift] at hmem
    exact hmem
  -- A `σ`-fixed point has norm `5 • x`.
  rw [Work.TorsorExistence.QuinticTwist.norm_eq_nsmul D x hx] at h1
  exact h1

end Work.Twist
