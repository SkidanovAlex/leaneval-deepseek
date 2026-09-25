import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

namespace Work.BourgainPlan.Maximal

/-- The `L²(ℓ²)` bound for the `ℓ²`-valued dyadic maximal function, with a constant that is
*uniform in the number of components* `n`.  Proof route: copy the proof of
`Submission/Work/BourgainPlan/Maximal/ell2Maximal.lean`'s `lintegral_ell2Max_le` (which has the
same bound with `n` fixed as a parameter and `C` allowed to depend on it), pulling the `∀ n` inside;
the constant comes from `dyMax_strong_type 2` and is independent of `n`. -/
theorem lintegral_ell2Max_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∫⁻ x, Work.BourgainPlan.Maximal.ell2Max f x
        ≤ ENNReal.ofReal (C ^ (2 : ℝ)) * ∫⁻ x, Work.BourgainPlan.Maximal.ell2Sq f x := by
  obtain ⟨C, hC, hb⟩ := dyMax_strong_type 2 (by norm_num : (1 : ℝ) < 2)
  refine ⟨C, hC, fun n f hf => ?_⟩
  have hsum : ∫⁻ x, ell2Max f x
      = ∑ t : Fin n, ∫⁻ x, (dyMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ) := by
    unfold ell2Max
    rw [MeasureTheory.lintegral_finsetSum]
    intro t _
    exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp
      (dyMax_measurable _)
  have hSq : ∫⁻ x, ell2Sq f x = ∑ t : Fin n, ∫⁻ x, ‖f t x‖ₑ ^ (2 : ℝ) := by
    unfold ell2Sq
    rw [MeasureTheory.lintegral_finsetSum]
    intro t _
    exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp (hf t).enorm
  rw [hsum, hSq, Finset.mul_sum]
  exact Finset.sum_le_sum fun t _ => hb (f t)

end Work.BourgainPlan.Maximal
