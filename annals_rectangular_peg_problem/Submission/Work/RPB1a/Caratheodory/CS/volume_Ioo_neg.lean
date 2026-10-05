import Mathlib

namespace Work.RPB1a.Caratheodory.CS

lemma volume_Ioo_neg (r : ℝ) : MeasureTheory.volume (Set.Ioo (-r) r) = ENNReal.ofReal (2 * r) := by
  rw [Real.volume_Ioo]
  ring_nf

end Work.RPB1a.Caratheodory.CS
