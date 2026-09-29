import Mathlib
import Submission.Work.A14D.log_one_sub_jump

namespace Work.A14D

open Complex Metric Filter Topology
open scoped Topology

/-- The boundary values of the principal branch of `Complex.log` at the negative real axis: for
`a < 0`, the points `a + ε i` (upper half-plane) and `a - ε i` (lower half-plane) tend to the cut
point `a` from above resp. below, whence
`log (a + ε i) → log (-a) + π i`,  `log (a - ε i) → log (-a) - π i`.

This is `log_one_sub_jump` transported along `x = 1 - a` (so that `1 - x = a`), with the two
half-planes exchanged by the sign change. -/
theorem tendsto_log_at_neg_real {a : ℝ} (ha : a < 0) :
    Filter.Tendsto (fun ε : ℝ => Complex.log ((a : ℂ) + ε * Complex.I)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Real.log (-a) + Real.pi * Complex.I)) ∧
      Filter.Tendsto (fun ε : ℝ => Complex.log ((a : ℂ) - ε * Complex.I)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Real.log (-a) - Real.pi * Complex.I)) := by
  have hx : 1 < 1 - a := by linarith
  obtain ⟨h1, h2⟩ := log_one_sub_jump (1 - a) hx
  have h1' : Tendsto (fun ε : ℝ => Complex.log (1 - ((1 - a : ℝ) + ε * Complex.I)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.log (-a) - Real.pi * Complex.I)) := by
    have h := h1
    rw [show ((1:ℝ) - a) - 1 = -a by ring] at h
    exact h
  have h2' : Tendsto (fun ε : ℝ => Complex.log (1 - ((1 - a : ℝ) - ε * Complex.I)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.log (-a) + Real.pi * Complex.I)) := by
    have h := h2
    rw [show ((1:ℝ) - a) - 1 = -a by ring] at h
    exact h
  exact ⟨h2'.congr (fun ε => by congr 1; push_cast; ring),
         h1'.congr (fun ε => by congr 1; push_cast; ring)⟩

end Work.A14D
