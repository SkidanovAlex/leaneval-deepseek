import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.nsmul_cls_eq_zero_iff
import Submission.Work.Twist.exists_shift_pow_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **The divisor-degree condition of the twist is independent of the chosen generator.**
`QuinticTwist.TorsorDivisorOfDegreePow D k n` is `∃ R, σ ^ k R - R = n • P`, i.e. the class of the
cocycle `σ ^ k ↦ P` raised to the `n`-th power is trivial, and `D.toTorsor.DivisorOfDegree n` is
the multiplicative form `cls ^ n = 1` of `n • cls = 0` (`Work.Arithmetic.Torsor.DivisorOfDegree`,
`Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff`).  For `k` coprime to `5` the two agree.

Ingredients: `nsmul_cls_eq_zero_iff` (the case `k = 1`, turning `n • cls = 0` into
`∃ R, σ R - R = n • P`) and `exists_shift_pow_iff` at `x = n • P`, which is `σ`-invariant
(`map_nsmul`, `galMap_PL`) and `5`-torsion (`five_smul_PL`). -/
theorem torsorDivisorOfDegreePow_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) {k : ℕ} (hk : k % 5 ≠ 0) (n : ℕ) :
    QuinticTwist.TorsorDivisorOfDegreePow D k n ↔ D.toTorsor.DivisorOfDegree n := by
  -- `n • P` is `σ`-invariant, since `P` is.
  have hfix : D.galMap ((n : ℕ) • D.PL) = (n : ℕ) • D.PL := by
    rw [map_nsmul, Work.TorsorExistence.QuinticTwist.galMap_PL]
  -- and `5`-torsion, since `P` is.
  have h5 : (5 : ℕ) • ((n : ℕ) • D.PL) = 0 := by
    rw [smul_comm, Work.TorsorExistence.QuinticTwist.five_smul_PL, nsmul_zero]
  -- `DivisorOfDegree n` is `cls ^ n = 1`, i.e. `n • cls = 0` (`toTorsor_divisorOfDegree_iff`),
  -- and that is `n • P ∈ (σ - 1)E(L)` (`nsmul_cls_eq_zero_iff`).
  rw [Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff D n,
    Work.Twist.nsmul_cls_eq_zero_iff D n]
  show (∃ R : D.LPoints, Work.Twist.QuinticTwist.galMapPow D k R - R = (n : ℕ) • D.PL) ↔
      (∃ R : D.LPoints, D.shift R = (n : ℕ) • D.PL)
  -- The generator-independence `exists_shift_pow_iff` identifies the `(σ ^ k - 1)`-coboundary
  -- condition with the `(σ - 1)`-coboundary condition for the `σ`-invariant, `5`-torsion `n • P`.
  rw [show (∃ R : D.LPoints, Work.Twist.QuinticTwist.galMapPow D k R - R = (n : ℕ) • D.PL) ↔
      (∃ R : D.LPoints, D.galMap R - R = (n : ℕ) • D.PL) from
    Work.Twist.exists_shift_pow_iff D ((n : ℕ) • D.PL) hfix h5 hk]
  -- `D.shift R = σ R - R` by definition.
  simp only [Work.TorsorExistence.QuinticTwist.shift, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

end Work.Twist
