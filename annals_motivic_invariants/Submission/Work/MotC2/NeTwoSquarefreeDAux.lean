import Mathlib
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.NeTwoSquarefreeCubic

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- `D = (a₁X + a₃)² + 4(X³ + a₂X² + a₄X + a₆) = linCoef E ^ 2 + 4 * cubCoef E` is squarefree in
characteristic `≠ 2`, given that it has no root `α : L` with `D(α) = 0 = D'(α)`
(`NeTwoNoDoubleRoot` supplies the latter for `E.IsElliptic`).

Route: `NeTwoSquarefreeCubic` (already proved in this workspace) reduces this to `D.natDegree = 3`.
For the degree: `(2 : L) ≠ 0` gives `(4 : L) ≠ 0`, and
`D = C 4 * X^3 + (C (a₁^2 + 4a₂) * X^2 + C (2a₁a₃ + 4a₄) * X + C (a₃^2 + 4a₆))` has degree `3`
(expand `linCoef E ^ 2 + 4 * cubCoef E`; the remainder has degree `≤ 2`), so `D.natDegree = 3`
(e.g. `Polynomial.natDegree_add_eq_left_of_natDegree_lt` and `Polynomial.natDegree_C_mul_X_pow`).
The statement is deliberately stronger than needed downstream (it does not assume ellipticity,
only the no-double-root hypothesis). -/
lemma NeTwoSquarefreeDAux (L : Type*) [Field L] (E : WeierstrassCurve L) (h2 : (2 : L) ≠ 0)
    (h : ∀ α : L, ¬ ((Work.MotC2.linCoef E ^ 2 + 4 * Work.MotC2.cubCoef E).eval α = 0 ∧
      (Work.MotC2.linCoef E ^ 2 + 4 * Work.MotC2.cubCoef E).derivative.eval α = 0)) :
    Squarefree (Work.MotC2.linCoef E ^ 2 + 4 * Work.MotC2.cubCoef E) := by
  -- In characteristic `≠ 2` the scalar `4` is nonzero, so the leading coefficient `4` of `D`
  -- does not vanish.
  have h4 : (4 : L) ≠ 0 := by
    intro h40
    apply h2
    have h22 : (4 : L) = 2 * 2 := by norm_num
    rw [h22] at h40
    exact (mul_eq_zero.mp h40).elim id id
  refine NeTwoSquarefreeCubic (Work.MotC2.linCoef E ^ 2 + 4 * Work.MotC2.cubCoef E) ?_ h
  -- `D` has degree `3`: expand and compute.
  simp only [Work.MotC2.linCoef, Work.MotC2.cubCoef]
  compute_degree!

end Work.MotC2
