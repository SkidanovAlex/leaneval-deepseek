import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

theorem tail_zero {c : ℝ → ℝ} {a b e z : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) (hz : 0 < z) (hbz : b ≤ z) :
    ∫ t in Set.Ioi z, c t * t ^ e = 0 := by
  have hzero : ∀ t : ℝ, t ∈ Set.Ioi z → c t * t ^ e = (0 : ℝ) := by
    intro t ht
    have hmem : t ∉ Set.Icc a b := by
      intro h
      exact absurd h.2 (not_le.mpr (lt_of_le_of_lt hbz ht))
    rw [hsupp t hmem, zero_mul]
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    (Filter.Eventually.of_forall hzero)]
  simp

end Work.FTS.PhiStar.Honesty.RadGreenSupp
