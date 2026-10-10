import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.PointlessIndexFive.pointless_iff_not_exists_shift

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **A criterion from the triviality of the Galois action on `E(L)/5E(L)`.**  If every coboundary
is `5`-divisible, `σ R - R ∈ 5·E(L)` for all `R ∈ E(L)` (this holds when `σ` acts trivially on
`E(L)/5E(L)`, in particular when `E(L) = E(𝕜)`), and if `P` is not `5`-divisible in `E(L)`, then
the class of `P` is non-zero.

Proof: `cls = 0` means `P = σ R - R` for some `R` (`Work.TorsorExistence.cls_eq_zero_iff`, or
`Work.PointlessIndexFive.pointless_iff_not_exists_shift`); by the first hypothesis this is
`5 • S` for some `S`, contradicting the second hypothesis. -/
theorem pointless_of_galMap_quot_five {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (hquot : ∀ R : D.LPoints, ∃ S : D.LPoints, D.galMap R - R = (5 : ℕ) • S)
    (hP : ∀ S : D.LPoints, (5 : ℕ) • S ≠ D.PL) : D.Pointless := by
  -- `Pointless` is `cls ≠ 0`, and `cls = 0` holds exactly when `P` is a coboundary `σ R - R`.
  rw [Work.PointlessIndexFive.pointless_iff_not_exists_shift]
  rintro ⟨R, hR⟩
  -- `hR : σ R - R = P` (the shift `D.shift` is definitionally `σ - 1`).
  have hR' : D.galMap R - R = D.PL := hR
  -- The first hypothesis writes the same element as `5 • S`.
  obtain ⟨S, hS⟩ := hquot R
  -- Hence `5 • S = P`, contradicting `hP S`.
  rw [hS] at hR'
  exact hP S hR'

end Work.Twist
