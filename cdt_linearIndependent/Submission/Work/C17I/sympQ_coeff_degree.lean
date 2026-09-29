import Mathlib
import Submission.Work.CPull.sympQ

namespace Work.C17I

open PowerSeries

/-- The symmetrised powers `P_m(y)` of `Submission.Work.CPull.sympQ` have degree at most `m`:
`coeff n (sympQ m) = 0` whenever `m < n`. -/
theorem sympQ_coeff_degree (m n : ℕ) (h : m < n) :
    PowerSeries.coeff n (Work.CPull.sympQ m) = 0 := by
  have key : ∀ m j : ℕ, m < j → PowerSeries.coeff j (Work.CPull.sympQ m) = 0 := by
    intro m
    refine Nat.twoStepInduction
      (motive := fun m => ∀ j : ℕ, m < j → PowerSeries.coeff j (Work.CPull.sympQ m) = 0)
      ?_ ?_ ?_ m
    · intro j hj
      rw [show Work.CPull.sympQ 0 = (2 : PowerSeries ℚ) from rfl,
        show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from rfl, PowerSeries.coeff_C,
        if_neg hj.ne']
    · intro j hj
      rw [show Work.CPull.sympQ 1 = (X : PowerSeries ℚ) from rfl, PowerSeries.coeff_X,
        if_neg hj.ne']
    · intro k ih1 ih2 j hj
      rcases j with _ | j'
      · omega
      · rw [show Work.CPull.sympQ (k + 2)
              = X * Work.CPull.sympQ (k + 1) - X * Work.CPull.sympQ k from rfl,
          map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
          ih2 j' (by omega), ih1 j' (by omega), sub_zero]
  exact key m n h

end Work.C17I
