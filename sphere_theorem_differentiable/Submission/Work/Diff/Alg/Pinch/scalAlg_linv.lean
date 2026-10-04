import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.scalAlg_knProd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

/-- The scalar curvature of `linv a b Y` for an algebraic curvature tensor `Y`:
`scal (linv a b Y) = scal Y - ((a/n)/(1+2(n-1)a) · scal Y) · (2n-2) · n`.

Indeed `linv a b Y = Y - c₁•(Ric₀ Y ∧ id) - c₂•(id ∧ id)`, `scal` is linear on these
combinations, `scal (Ric₀ Y ∧ id) = 0` and `scal (id ∧ id) = (2n-2)·n`. -/
theorem scalAlg_linv (n : ℕ) {a b : ℝ} (hb : 1 + ((n : ℝ) - 2) * b ≠ 0)
    (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0) {Y : Submission.Diff.Alg.Curv4 n}
    (hY : Submission.Diff.Alg.IsAlgCurv Y) :
    Submission.Diff.Alg.scalAlg (Work.Diff.Alg.Pinch.linv a b Y)
      = Submission.Diff.Alg.scalAlg Y
        - ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * Submission.Diff.Alg.scalAlg Y)
            * (2 * (n : ℝ) - 2) * (n : ℝ) := by
  rw [linv, scalAlg_sub, scalAlg_sub, scalAlg_smul_linv, scalAlg_smul_linv,
    ellinv_scalAlg_knProd_ric0 hY, ellinv_scalAlg_knProd_id2_id2 n]
  ring

end Work.Diff.Alg.Pinch
