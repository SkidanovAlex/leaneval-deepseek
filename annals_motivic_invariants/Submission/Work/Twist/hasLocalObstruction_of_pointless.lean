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

/-- **Every pointless quintic twist admits a local obstruction.**  If `cls ≠ 0`, i.e.
`P ∉ (σ - 1)E(L)`, then the quotient map `E(L) → E(L)/(σ - 1)E(L)` is a `LocalObstruction D`
(`Submission/Work/Twist/Defs.lean`): it is additive, kills the coboundaries `σ R - R`, and does not
kill `P`.

Together with `localObstruction_pointless` (the criterion `LocalObstruction D → D.Pointless`,
proved in `Submission/Work/Twist/Assembly.lean`) this shows that the *local-obstruction form* of
the arithmetic residual `HasPointlessTwistByObstruction 𝕜` is equivalent to `HasPointlessTwist 𝕜`:
the paper's way of deciding `cls ≠ 0` loses nothing.

Implementation note: the natural target is the quotient `D.LPoints ⧸ D.shift.range`, where
`D.shift.range` is the range of the additive homomorphism `D.shift` (so that membership is
`∃ R, σ R - R = x`); `QuotientAddGroup.mk'` is the obstruction and `QuotientGroup.eq_zero_iff` /
`QuotientAddGroup.eq_zero_iff` converts the two conditions.  (Beware: inside the structure literal
for `LocalObstruction`, the instance argument of the quotient is not automatically in scope for the
later fields; install it with `letI`/`haveI` first, or state the fields' proofs with `congrArg`
manipulations that avoid typeclass search on the quotient.) -/
theorem hasLocalObstruction_of_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (h : D.Pointless) : HasLocalObstruction D := by
  -- `P` is not a coboundary: `D.PL` lies outside the range of `σ - 1`.
  have hPL : D.PL ∉ D.shift.range := by
    rw [AddMonoidHom.mem_range]
    rintro ⟨R, hR⟩
    exact (Work.PointlessIndexFive.pointless_iff_not_exists_shift D).mp h ⟨R, hR⟩
  -- The quotient map by the coboundaries is the obstruction; it is additive for free, it kills
  -- the coboundaries because they lie in the kernel, and it does not kill `P` because `P` is not
  -- a coboundary.
  refine ⟨{ G := D.LPoints ⧸ D.shift.range
            toFun := QuotientAddGroup.mk' D.shift.range
            map_PL := ?_
            map_shift := ?_ }⟩
  · intro h0
    exact hPL ((QuotientAddGroup.eq_zero_iff D.PL).mp h0)
  · intro R
    exact (QuotientAddGroup.eq_zero_iff (D.shift R)).mpr
      (AddMonoidHom.mem_range.mpr ⟨R, rfl⟩)

end Work.Twist
