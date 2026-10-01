import Mathlib
import Submission.Work.ZeroFreeTables.exp_neg_mul_ibp

namespace Work.ZeroFreeTables.XY

theorem exp_neg_mul_ibp_two (z : ℂ) (hz : z ≠ 0) {b : ℝ} (g g' g'' : ℝ → ℂ)
    (hg : ∀ t ∈ Set.uIcc (0:ℝ) b, HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Set.uIcc (0:ℝ) b, HasDerivAt g' (g'' t) t)
    (hgcont : ContinuousOn g (Set.uIcc (0:ℝ) b))
    (hg'cont : ContinuousOn g' (Set.uIcc (0:ℝ) b))
    (hg''cont : ContinuousOn g'' (Set.uIcc (0:ℝ) b))
    (hb : g b = 0) (hb' : g' b = 0) :
    ∫ t in (0:ℝ)..b, Complex.exp (-(z * (t : ℂ))) * g t
      = g 0 / z + g' 0 / z ^ 2
        + (z ^ 2)⁻¹ * ∫ t in (0:ℝ)..b, Complex.exp (-(z * (t : ℂ))) * g'' t := by
  have h1 := Work.ZeroFreeTables.exp_neg_mul_ibp z hz g g' hg hgcont hg'cont hb
  have h2 := Work.ZeroFreeTables.exp_neg_mul_ibp z hz g' g'' hg' hg'cont hg''cont hb'
  rw [h1, h2]
  field_simp
  ring

end Work.ZeroFreeTables.XY
