import Mathlib
import Submission.Work.Twist.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **The orbit identity of the twist.**  If `R ∈ E(L)` satisfies `σ R - R = x` for a
`σ`-invariant `x` (in the applications `x = P` or `x = n • P`), then the whole orbit of `R`
under `σ` is affine in `x`: `σ ^ k R = R + k • x`.  This is the computation behind the
independence of the twist class from the chosen generator of `Gal(L/𝕜)`.

`QuinticTwist.galMapPow D k : D.LPoints →+ D.LPoints` is the action of `σ ^ k` on `E(L)`,
defined in `Submission/Work/Twist/Defs.lean` (module `Submission.Work.Twist.Defs`) as
`WeierstrassCurve.Affine.Point.map` of the `k`-th power of the chosen generator
`D.ext.gen : D.ext.L ≃ₐ[𝕜] D.ext.L`; the already proved `galMapPow_apply` identifies it with the
`k`-th iterate of `D.galMap`. -/
theorem galMapPow_eq_add_nsmul {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) {x : D.LPoints} (hx : D.galMap x = x)
    {R : D.LPoints} (h : D.galMap R - R = x) (k : ℕ) :
    QuinticTwist.galMapPow D k R = R + (k : ℕ) • x := by
  -- `galMapPow k` is the `k`-th iterate of `galMap`, so it suffices to compute the orbit of `R`.
  rw [QuinticTwist.galMapPow_apply]
  -- `σ R - R = x` says `σ R = R + x`.
  have hR : D.galMap R = R + x := (sub_eq_iff_eq_add').mp h
  -- The orbit of `R` is affine in `x`, by induction on the number of steps: additivity of `σ`
  -- turns each step into "add `x` once".
  have key : ∀ k : ℕ, (D.galMap^[k]) R = R + (k : ℕ) • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_add, map_nsmul, hx, hR, add_nsmul, one_nsmul]
      abel
  exact key k

end Work.Twist
