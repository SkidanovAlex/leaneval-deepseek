import Mathlib
import Submission.Work.Diff.Alg.Pinch.lqkDefs
import Submission.Work.Diff.Alg.Pinch.lqkSums
import Submission.Work.Diff.Alg.Pinch.Q_knProd_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- For a symmetric matrix the row-row product `s2m` coincides with the matrix square `sqT`. -/
lemma s2m_eq_sqT {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) : s2m A = sqT A := by
  funext i j
  rw [sqT_apply]
  exact s2m_rows hA i j

lemma trM_eq_trT {A : Fin n → Fin n → ℝ} : trM A = trT A := by
  rw [trM_eq, trT_apply]

lemma frb_eq_frobT {A : Fin n → Fin n → ℝ} : frb A = frobT A := by
  rw [frb_eq, frobT_apply]

theorem lqk_Q_knProd (n : ℕ) {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) :
    Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n))
      = ((n : ℝ) - 2) • Work.Diff.Alg.Pinch.knProd A A
        + (2 * Work.Diff.Alg.Pinch.trT A) • Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n)
        - 2 • Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.sqT A) (Work.Diff.Alg.Pinch.id2 n)
        + Work.Diff.Alg.Pinch.frobT A • Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.id2 n) (Work.Diff.Alg.Pinch.id2 n) := by
  rw [Q_knProd_apply n hA, s2m_eq_sqT hA, trM_eq_trT, frb_eq_frobT]
  funext i j k l
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Work.Diff.Alg.Pinch
