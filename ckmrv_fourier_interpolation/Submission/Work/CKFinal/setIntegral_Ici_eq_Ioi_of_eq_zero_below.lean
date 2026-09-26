import Mathlib

open MeasureTheory

namespace Work.CKFinal

/-- A function vanishing below `B ≥ 1` has the same `∫_{Ici 1}` as its restriction to `[B,∞)`. -/
lemma setIntegral_Ici_eq_Ioi_of_eq_zero_below {f g : ℝ → ℂ} {B : ℝ} (hB : 1 ≤ B)
    (hzero : ∀ t : ℝ, t < B → g t = 0) (heq : ∀ t : ℝ, B ≤ t → g t = f t) :
    ∫ t in Set.Ici (1 : ℝ), g t = ∫ t in Set.Ioi B, f t := by
  have h1 : ∫ t in Set.Ici (1 : ℝ), g t = ∫ t in Set.Ici B, g t := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici ?_ ?_
    · intro x hx
      exact Set.mem_Ici.mpr (le_trans hB (Set.mem_Ici.mp hx))
    · intro x hx
      exact hzero x (not_le.mp fun h => hx.2 (Set.mem_Ici.mpr h))
  have h2 : ∫ t in Set.Ici B, g t = ∫ t in Set.Ioi B, g t := integral_Ici_eq_integral_Ioi
  have h3 : ∫ t in Set.Ioi B, g t = ∫ t in Set.Ioi B, f t := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    exact heq x (le_of_lt (Set.mem_Ioi.mp hx))
  rw [h1, h2, h3]

end Work.CKFinal
