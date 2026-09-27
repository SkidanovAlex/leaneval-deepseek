import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Cutoff

private lemma seg_nonneg (a b u : ℝ) : 0 ≤ seg a b u := by
  unfold seg clamp
  exact le_max_left 0 (min 1 ((b - |u|) / (b - a)))

private lemma seg_le_one (a b u : ℝ) : seg a b u ≤ 1 := by
  unfold seg clamp
  exact max_le zero_le_one (min_le_left 1 ((b - |u|) / (b - a)))

lemma cubeCut_mem {n : ℕ} {a b : ℝ} (hab : a < b) (x : PL.E n) :
    0 ≤ cubeCut a b x ∧ cubeCut a b x ≤ 1 := by
  unfold cubeCut
  constructor
  · exact Finset.prod_nonneg fun i _ => seg_nonneg a b _
  · exact Finset.prod_le_one₀ (fun i _ => seg_nonneg a b _) (fun i _ => seg_le_one a b _)

end Work.PL.Approx.Cutoff
