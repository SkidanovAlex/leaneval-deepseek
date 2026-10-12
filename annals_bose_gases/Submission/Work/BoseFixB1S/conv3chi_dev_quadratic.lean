import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.abs_wSmallScaled_div_convScale_le
import Submission.Work.MGroupInput.newtonianSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- Global quadratic deviation of the big-box cosine self-convolution `(χ⋆χ)`:
`∃ C ≥ 0, ∀ t : ℝ³, |(χ⋆χ)(t) − 1| ≤ C‖t‖²`.
Route: `Submission.BoseGases.conv3chi_second_order_bound` gives the local bound for
`‖t‖ ≤ r₁` (`r₁ > 0`); `conv3chi_nonneg` and `conv3chi_le_one` give `|(χ⋆χ)(t)| ≤ 1`,
so outside the local ball `|(χ⋆χ)(t) − 1| ≤ 2 ≤ (2/r₁²)·‖t‖²`. -/
theorem conv3chi_dev_quadratic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ C * ‖t‖ ^ 2 := by
  obtain ⟨C, hC0, r₁, hr₁, hloc⟩ := Submission.BoseGases.conv3chi_second_order_bound
  -- `C' := max C (2 / r₁ ^ 2)` handles both regimes.
  refine ⟨max C (2 / r₁ ^ 2), le_trans hC0 (le_max_left C _), fun t => ?_⟩
  by_cases ht : ‖t‖ ≤ r₁
  · -- inside the local ball: use the second-order Taylor bound
    calc |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ C * ‖t‖ ^ 2 := hloc t ht
      _ ≤ max C (2 / r₁ ^ 2) * ‖t‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left C _) (sq_nonneg _)
  · -- outside: `|(χ⋆χ)(t) − 1| ≤ 2` and `2 ≤ (2/r₁²)·‖t‖²` since `‖t‖ > r₁`
    have htr : r₁ < ‖t‖ := lt_of_not_ge ht
    have hnn : 0 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t :=
      Submission.BoseGases.conv3chi_nonneg t
    have h1 : Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t ≤ 1 :=
      Submission.BoseGases.conv3chi_le_one t
    have h2 : |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hsq : r₁ ^ 2 ≤ ‖t‖ ^ 2 := by nlinarith [norm_nonneg t]
    have hC2 : 2 / r₁ ^ 2 * r₁ ^ 2 = 2 := by field_simp
    have hkey : 2 ≤ 2 / r₁ ^ 2 * ‖t‖ ^ 2 := by
      have hpos : 0 ≤ 2 / r₁ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hsq hpos
      linarith [this, hC2]
    calc |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1| ≤ 2 := h2
      _ ≤ max C (2 / r₁ ^ 2) * ‖t‖ ^ 2 :=
            le_trans hkey (mul_le_mul_of_nonneg_right (le_max_right C _) (sq_nonneg _))

end Work.BoseFixB1S
