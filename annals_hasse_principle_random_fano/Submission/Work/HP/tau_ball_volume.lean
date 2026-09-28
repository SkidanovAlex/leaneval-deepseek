import Mathlib
import Submission.Work.HP.tau_basic

namespace Work.HP

/-- The Euclidean unit ball `{u | rNorm u ≤ 1}` in `Fin k → ℝ` has finite Lebesgue
measure, since it is contained in the box `[-1,1]^k`. -/
lemma tau_ball_volume (k : ℕ) :
    MeasureTheory.volume {u : Fin k → ℝ | Work.HP.rNorm u ≤ 1} < ⊤ := by
  have hsub : {u : Fin k → ℝ | rNorm u ≤ 1} ⊆
      Set.univ.pi (fun _ : Fin k => Set.Icc (-1:ℝ) 1) := by
    intro u hu
    change rNorm u ≤ 1 at hu
    rw [Set.mem_univ_pi]
    intro i
    have h1 : |u i| ≤ rNorm u := abs_apply_le_rNorm u i
    rw [Set.mem_Icc]
    exact ⟨by linarith [neg_abs_le (u i), h1, hu],
           by linarith [le_abs_self (u i), h1, hu]⟩
  calc MeasureTheory.volume {u : Fin k → ℝ | rNorm u ≤ 1}
      ≤ MeasureTheory.volume (Set.univ.pi (fun _ : Fin k => Set.Icc (-1:ℝ) 1)) :=
        MeasureTheory.measure_mono hsub
    _ = ∏ i : Fin k, MeasureTheory.volume (Set.Icc (-1:ℝ) 1) := by
        conv_lhs => rw [MeasureTheory.volume_pi]
        exact MeasureTheory.Measure.pi_pi _ _
    _ = (ENNReal.ofReal 2) ^ k := by
        rw [Finset.prod_const, Real.volume_Icc, Finset.card_fin]
        norm_num
    _ < ⊤ := ENNReal.pow_lt_top ENNReal.ofReal_lt_top

end Work.HP
