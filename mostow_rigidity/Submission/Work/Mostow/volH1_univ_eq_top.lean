import Mathlib
import Submission.Work.Mostow.volH1Ioo

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

noncomputable section

/-- The hyperbolic length measure of the slab `{v : E 1 | v 0 ∈ Ioo (-sinh n) (sinh n)}` is `2n`:
`arsinh (sinh n) - arsinh (-sinh n) = n - (-n) = 2n`. -/
private lemma volH1_slab_sinh (n : ℕ) :
    (Submission.Mostow.volH 1)
        {v : Submission.Mostow.E 1 | v 0 ∈ Set.Ioo (-(Real.sinh n)) (Real.sinh n)}
      = ((2 * n : ℕ) : ℝ≥0∞) := by
  have hle : -(Real.sinh (n : ℝ)) ≤ Real.sinh (n : ℝ) := by
    have hnn : (0 : ℝ) ≤ Real.sinh (n : ℝ) := Real.sinh_nonneg_iff.mpr (Nat.cast_nonneg n)
    linarith
  rw [volH1Ioo (-(Real.sinh (n : ℝ))) (Real.sinh (n : ℝ)) hle]
  rw [Real.arsinh_sinh, Real.arsinh_neg, Real.arsinh_sinh]
  have hval : (n : ℝ) - -(n : ℝ) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
  rw [hval, ENNReal.ofReal_natCast]

/-- The hyperbolic length measure of the whole hyperbolic line `ℍ¹ = E 1` is infinite. -/
theorem volH1_univ_eq_top :
    (Submission.Mostow.volH 1) (Set.univ : Set (Submission.Mostow.E 1)) = ⊤ := by
  have hb : ∀ n : ℕ,
      ((2 * n : ℕ) : ℝ≥0∞)
        ≤ (Submission.Mostow.volH 1) (Set.univ : Set (Submission.Mostow.E 1)) := by
    intro n
    rw [← volH1_slab_sinh n]
    exact measure_mono (Set.subset_univ _)
  have hsup : (⨆ n : ℕ, ((2 * n : ℕ) : ℝ≥0∞)) = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : ℝ≥0∞) = ⨆ n : ℕ, (n : ℝ≥0∞) := ENNReal.iSup_natCast.symm
      _ ≤ ⨆ n : ℕ, ((2 * n : ℕ) : ℝ≥0∞) :=
          iSup_le fun n =>
            le_trans ((Nat.cast_le (α := ℝ≥0∞)).mpr (by omega : n ≤ 2 * n))
              (le_iSup (fun m : ℕ => ((2 * m : ℕ) : ℝ≥0∞)) n)
  rw [eq_top_iff]
  calc (⊤ : ℝ≥0∞) = ⨆ n : ℕ, ((2 * n : ℕ) : ℝ≥0∞) := hsup.symm
    _ ≤ (Submission.Mostow.volH 1) (Set.univ : Set (Submission.Mostow.E 1)) := iSup_le hb

end

end Work.Mostow
