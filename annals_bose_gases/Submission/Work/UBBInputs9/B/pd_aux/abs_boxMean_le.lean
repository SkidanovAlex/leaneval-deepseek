import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.B.pd_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.B.pd_aux

open MeasureTheory

lemma abs_boxMean_le {ℓ d M : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X 1 → ℝ} (hM : ∀ x, |Φ x| ≤ M) (u : EuclideanSpace ℝ (Fin 3)) : |Work.UBBInputs9.B.boxMean ℓ d u Φ| ≤ M := by
  have hMnn : 0 ≤ M :=
    le_trans (abs_nonneg (Φ (fun _ : Fin 1 => (0 : EuclideanSpace ℝ (Fin 3))))) (hM _)
  have hfin : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (Submission.BoseGases.dlBox ℓ d u) < ⊤ :=
    Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
  have hJ : ‖∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (fun _ => z)‖
      ≤ M * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real
          (Submission.BoseGases.dlBox ℓ d u) := by
    apply MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) hfin
    intro z hz
    rw [Real.norm_eq_abs]
    exact hM _
  have hmass : Work.SmallBoxSliding.boxMass ℓ d u
      = (volume : Measure (EuclideanSpace ℝ (Fin 3))).real
          (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hmass_nn : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [hmass]; exact MeasureTheory.measureReal_nonneg
  unfold Work.UBBInputs9.B.boxMean
  by_cases hv : Work.SmallBoxSliding.boxMass ℓ d u = 0
  · rw [hv, inv_zero, zero_mul, abs_zero]
    exact hMnn
  · have hvpos : 0 < Work.SmallBoxSliding.boxMass ℓ d u :=
      lt_of_le_of_ne hmass_nn (Ne.symm hv)
    calc |(Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
            ∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (fun _ => z)|
        = (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
            |∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (fun _ => z)| := by
          rw [abs_mul, abs_of_pos (inv_pos.mpr hvpos)]
      _ ≤ (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
            (M * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real
              (Submission.BoseGases.dlBox ℓ d u)) :=
          mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact hJ)
            (inv_nonneg.mpr hvpos.le)
      _ = (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
            (M * Work.SmallBoxSliding.boxMass ℓ d u) := by rw [← hmass]
      _ = M := by
          rw [mul_comm M (Work.SmallBoxSliding.boxMass ℓ d u), ← mul_assoc,
            inv_mul_cancel₀ hv, one_mul]

end Work.UBBInputs9.B.pd_aux
