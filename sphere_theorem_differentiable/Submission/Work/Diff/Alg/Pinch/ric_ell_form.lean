import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.ric_knProd_id2
import Submission.Work.Diff.Alg.Pinch.ell_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

theorem ric_ell_form (n : ℕ) (hn : ((n : ℝ)) ≠ 0) (a b : ℝ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) (i j : Fin n) :
    Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.ell a b R) i j
      = (1 + ((n : ℝ) - 2) * b) * Work.Diff.Alg.Pinch.ric R i j
        + ((2 * a * ((n : ℝ) - 1) - ((n : ℝ) - 2) * b) * Submission.Diff.Alg.scalAlg R
            / (n : ℝ)) * (if i = j then (1 : ℝ) else 0) := by
  have h1 := ric0_ell_linv n a b hn hR i j
  have h2 := scalAlg_ell_of_ne n a b hn hR
  simp only [ric0] at h1
  rw [h2] at h1
  simp only [id2] at h1
  linear_combination h1

end Work.Diff.Alg.Pinch
