import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

open MeasureTheory

theorem efunMellinEqIntegral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) :
    mellin (Set.indicator (Set.Ioi (1:ℝ)) (Work.LinnikAreas.Efun χ)) z
      = ∫ x in Set.Ioi (1:ℝ), Work.LinnikAreas.Efun χ x * (x:ℂ) ^ (z - 1) := by
  rw [mellin]
  have hfun : (fun t : ℝ => (t : ℂ) ^ (z - 1) • Set.indicator (Set.Ioi (1:ℝ)) (Efun χ) t)
      = Set.indicator (Set.Ioi (1:ℝ)) (fun t : ℝ => Efun χ t * (t : ℂ) ^ (z - 1)) := by
    funext t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, mul_comm]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  rw [hfun, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi]
  norm_num

end Work.LinnikAreas
