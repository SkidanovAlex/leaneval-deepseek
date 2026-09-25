import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2MaxShiftDefs
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.ell2F_hlMax_twoGrids

namespace Work.BourgainPlan.Maximal

/-- **The `L²(ℓ²)` bound for the half-shifted `ℓ²`-valued dyadic maximal function, uniform in the
number of components.**

Each component `dyMaxShift (1/2) (‖f t ·‖ₑ)` is dominated pointwise by the centred maximal function
`hlMax (‖f t ·‖ₑ)` (`dyMaxShift_le_hlMax`), and the scalar strong `(2,2)` bound of `hlMax`
(`real_maximal_strong_type 2`) is uniform in the function, hence in `t`.  Summing over the finite
index set `Fin n` gives the claim with a constant independent of `n`. -/
theorem lintegral_ell2MaxShift_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∫⁻ x, Work.BourgainPlan.Maximal.ell2MaxShift f x
        ≤ ENNReal.ofReal (C ^ (2 : ℝ)) * ∫⁻ x, Work.BourgainPlan.Maximal.ell2Sq f x := by
  obtain ⟨C, hC, hb⟩ := Commons.Analysis.Maximal.real_maximal_strong_type 2
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨C, hC, fun n f hf => ?_⟩
  have hsum : ∫⁻ x, ell2MaxShift f x
      = ∑ t : Fin n, ∫⁻ x, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ) := by
    unfold ell2MaxShift
    rw [MeasureTheory.lintegral_finsetSum]
    intro t _
    exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp
      (dyMaxShift_measurable (1 / 2) (fun y => ‖f t y‖ₑ))
  have hSq : ∫⁻ x, ell2Sq f x = ∑ t : Fin n, ∫⁻ x, ‖f t x‖ₑ ^ (2 : ℝ) := by
    unfold ell2Sq
    rw [MeasureTheory.lintegral_finsetSum]
    intro t _
    exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp (hf t).enorm
  rw [hsum, hSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  refine le_trans (MeasureTheory.lintegral_mono fun x => ?_) (hb (f t))
  exact ENNReal.rpow_le_rpow (dyMaxShift_le_hlMax (1 / 2) (fun y => ‖f t y‖ₑ) x)
    (by norm_num : (0 : ℝ) ≤ 2)

end Work.BourgainPlan.Maximal
