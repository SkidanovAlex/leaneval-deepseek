import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.DhRepel.l52Hyp_supply

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex

/-- The windowed divisor sum `winSum χ s δ` is non-negative.

Each summand is `mult u · (1_{‖1+i·Im s-u‖ ≤ δ} · Re (1/(s-u)))`.  The multiplicity
`mult u` is the divisor of the entire function `completedLFunction χ` on the ball, hence
non-negative (`divisor_nonneg`); and whenever `mult u ≠ 0` the point `u` is a zero of `Λ`,
so `0 < Re u < 1 < Re s` and the real part `Re (1/(s-u))` is non-negative
(`kernel_first_nonneg`).  Where `mult u = 0` the summand vanishes.  Hence every summand is
non-negative and so is the finite sum. -/
theorem winSum_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) (δ : ℝ) :
    0 ≤ Work.LinnikAreas.DhRepel.winSum χ s δ := by
  rw [Work.LinnikAreas.DhRepel.winSum]
  apply finsum_nonneg
  intro u
  by_cases hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
  · rw [if_pos hwin]
    by_cases hd : MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 (|s.im| + 2)) u = 0
    · rw [hd]; simp
    · exact mul_nonneg (Work.LinnikAreas.DhRepel.divisor_nonneg χ hχ (|s.im| + 2) u)
        (Work.LinnikAreas.DhRepel.kernel_first_nonneg χ hχ hχprim hs hd)
  · rw [if_neg hwin]; simp

end Work.LinnikAreas.OtherCharRepel
