import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

/-- `∑ a ∑ b ∑ c ∑ d, f a b c d = ∑ c ∑ a ∑ d ∑ b, f a b c d` (a pure reindexing of a
four-fold sum, by three applications of `Finset.sum_comm`). -/
private lemma sum4_swap {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d
      = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
          apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl; intro c _
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.sum_comm]

/-- `qform (bmat v S) w = R4 S v w v w`: contracting the `bmat v S` (0,2)-tensor with `w`
recovers the full multilinear evaluation `S(v, w, v, w)`.  Pure finite-sum rearrangement. -/
theorem qform_bmat (n : ℕ) (v w : Fin n → ℝ) (S : Submission.Diff.Alg.Curv4 n) :
    Work.Diff.Alg.Pinch.qform (Work.Diff.Alg.Pinch.bmat v S) w
      = Submission.Diff.Alg.R4 S v w v w := by
  simp only [Work.Diff.Alg.Pinch.qform, Work.Diff.Alg.Pinch.bmat,
    Submission.Diff.Alg.R4, Finset.sum_mul]
  rw [sum4_swap]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

end Work.Diff.Alg.Pinch
