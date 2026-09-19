import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.Analysis.SpecialFunctions.Frullani.complex_log

open MeasureTheory Set

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- The Frullani-type difference kernel `(e^{-zt} - e^{-mt}) / t` is integrable on
`(0, ∞)` whenever `0 < Re z` and `1 ≤ m`. -/
theorem digamma_logRem_F_integrable (z : ℂ) (hz : 0 < z.re) (m : ℕ) (hm : 1 ≤ m) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Complex.exp (-(z * (t : ℂ))) - Complex.exp (-(((m : ℝ) : ℂ) * (t : ℂ)))) / (t : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  let b : ℂ := ((m : ℝ) : ℂ)
  let c : ℂ := z - b
  let M : ℝ := min z.re (m : ℝ)
  have hmm : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hm)
  have hM : 0 < M := by
    dsimp [M]
    exact lt_min hz hmm
  have hseg : ∀ u ∈ Set.Icc (0 : ℝ) 1, M ≤ ((b + (u : ℂ) * c)).re := by
    intro u hu
    have hmn := Frullani.re_seg_lower b c u hu
    dsimp [M, b, c] at hmn ⊢
    simpa [min_comm] using hmn
  have hint := Frullani.integrableOn_g (b := b) (c := c) (m := M) hM hseg
  simpa [b, c] using hint

end Commons.Analysis.SpecialFunctions.Gamma