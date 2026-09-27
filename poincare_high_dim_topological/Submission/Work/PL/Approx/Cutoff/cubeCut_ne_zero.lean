import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Seg.seg_ne_zero

namespace Work.PL.Approx.Cutoff

/-- If the cutoff `cubeCut a b` is nonzero at `x`, then every coordinate of `x` is bounded
by `b` in absolute value, i.e. `x` lies in the closed cube of radius `b`. -/
lemma cubeCut_ne_zero {n : ℕ} {a b : ℝ} (hab : a < b) {x : PL.E n} (hx : cubeCut a b x ≠ 0) :
    x ∈ PL.closedCube b := by
  change ∀ i, |x i| ≤ b
  intro i
  have hprod : (∏ j : Fin n, seg a b (x j)) ≠ 0 := by
    rwa [cubeCut] at hx
  have hi : seg a b (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  exact le_of_lt (PL.Approx.Seg.seg_ne_zero hab hi)

end Work.PL.Approx.Cutoff
