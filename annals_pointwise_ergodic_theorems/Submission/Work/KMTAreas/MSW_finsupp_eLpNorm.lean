import Mathlib
import Submission.Port.Aesm

/-!
# The `ℓᵖ` norm of a finitely supported sequence is its finite `ℓᵖ` sum

For a function `g : ℤ → ℂ` supported on a finite set `s` and any real exponent `p > 0`, the
`Lᵖ` seminorm of `g` with respect to counting measure on `ℤ` is the finite sum
`(∑_{n ∈ s} ‖g n‖ ^ p) ^ (1/p)`.
-/

namespace Work.KMTAreas

theorem MSW_finsupp_eLpNorm {g : ℤ → ℂ} {s : Finset ℤ} (hs : ∀ n ∉ s, g n = 0)
    {p : ℝ} (hp : 0 < p) :
    MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count
      = (∑ n ∈ s, enorm (g n) ^ p) ^ (1 / p) := by
  have hp0 : (0 : ℝ) ≤ p := le_of_lt hp
  have hpte : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := ENNReal.ofReal p)
        (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top]
  rw [hpte]
  rw [MeasureTheory.lintegral_count]
  rw [tsum_eq_sum (s := s) (f := fun n => ‖g n‖ₑ ^ p) (by
    intro b hb
    rw [hs b hb]
    simp only [enorm_zero]
    exact ENNReal.zero_rpow_of_pos hp)]

end Work.KMTAreas
