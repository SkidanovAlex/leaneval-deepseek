import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Cutoff

lemma cubeCut_eq_one {n : ℕ} {a b : ℝ} (hab : a < b) {x : PL.E n} (hx : x ∈ PL.closedCube a) : cubeCut a b x = 1 := by
  unfold cubeCut
  rw [Finset.prod_eq_one]
  intro i _
  unfold seg clamp
  have hxi : |x i| ≤ a := hx i
  have hba : 0 < b - a := by linarith
  have h1 : 1 ≤ (b - |x i|) / (b - a) := by
    rw [le_div_iff₀ hba]
    linarith
  rw [min_eq_left h1, max_eq_right zero_le_one]

end Work.PL.Approx.Cutoff
