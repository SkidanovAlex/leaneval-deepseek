import Mathlib
import Submission.Commons.Analysis.Real.tsum_int_inv_one_add_sq_sub_le
import Submission.Commons.Analysis.Fourier.finset_bracket_lattice_le

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped ENNReal

/-- The series `∑_{m ∈ ℤ} (1 + (m - t)²)⁻¹` is summable (dominated by a multiple of
`∑_{m ∈ ℤ} (1 + m²)⁻¹`). -/
private lemma summable_inv_one_add_sq_sub (t : ℝ) :
    Summable (fun m : ℤ => (1 + ((m : ℝ) - t) ^ 2)⁻¹) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((Commons.Analysis.Fourier.summable_one_add_sq_int).mul_left (2 * (1 + t ^ 2)))
  have hkey : 1 + (m : ℝ) ^ 2 ≤ (2 * (1 + t ^ 2)) * (1 + ((m : ℝ) - t) ^ 2) := by
    nlinarith [sq_nonneg ((m : ℝ) - 2 * t), sq_nonneg t]
  rw [show (2 * (1 + t ^ 2)) * (1 + (m : ℝ) ^ 2)⁻¹
      = ((1 + (m : ℝ) ^ 2) / (2 * (1 + t ^ 2)))⁻¹ by rw [inv_div, div_eq_mul_inv]]
  rw [inv_le_inv₀ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [hkey]

-- The series bound needed here is `Commons.Analysis.Real.tsum_int_inv_one_add_sq_sub_le` (in this workspace): for some `B0 > 0`, every `t : ℝ` has `∑' m : ℤ, (1 + ((m : ℝ) - t) ^ 2)⁻¹ ≤ B0`.
theorem exists_kernel_lattice_weight_le (K : ℝ → ℂ) (C : ℝ) (hC : 0 < C)
    (hK : ∀ u : ℝ, ‖K u‖ ≤ C / (1 + u ^ 2)) :
    ∃ B : ℝ, 0 < B ∧ (∫⁻ t : ℝ, ‖K t‖ₑ ∂MeasureTheory.volume ≤ ENNReal.ofReal B) ∧
      (∀ x : ℝ, (∑' m : ℤ, ‖K ((m : ℝ) - x)‖ₑ) ≤ ENNReal.ofReal B) := by
  obtain ⟨B0, hB0pos, hB0⟩ := Commons.Analysis.Real.tsum_int_inv_one_add_sq_sub_le
  have hC0 : (0 : ℝ) ≤ C := le_of_lt hC
  refine ⟨C * (Real.pi + B0), mul_pos hC (by linarith [hB0pos, Real.pi_pos]), ?_, ?_⟩
  · -- the `L¹` bound on the whole line
    have hgint : Integrable (fun t : ℝ => C / (1 + t ^ 2)) := by
      simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C
    have hgval : ∫ t : ℝ, C / (1 + t ^ 2) = C * Real.pi := by
      have h1 : ∫ t : ℝ, C / (1 + t ^ 2) = ∫ t : ℝ, C * (1 + t ^ 2)⁻¹ := by
        congr 1 with t
      rw [h1, MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
    have h2int : ∫⁻ t : ℝ, ENNReal.ofReal (C / (1 + t ^ 2)) ∂MeasureTheory.volume
        = ENNReal.ofReal (C * Real.pi) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint
        (Filter.Eventually.of_forall (fun t => by positivity)), hgval]
    calc ∫⁻ t : ℝ, ‖K t‖ₑ ∂MeasureTheory.volume
        ≤ ∫⁻ t : ℝ, ENNReal.ofReal (C / (1 + t ^ 2)) ∂MeasureTheory.volume := by
          apply lintegral_mono
          intro t
          change ‖K t‖ₑ ≤ ENNReal.ofReal (C / (1 + t ^ 2))
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hK t)
      _ = ENNReal.ofReal (C * Real.pi) := h2int
      _ ≤ ENNReal.ofReal (C * (Real.pi + B0)) :=
          ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (by linarith [hB0pos]) hC0)
  · intro x
    have hsumm : Summable (fun m : ℤ => (1 + ((m : ℝ) - x) ^ 2)⁻¹) :=
      summable_inv_one_add_sq_sub x
    have h2sum : (∑' m : ℤ, ENNReal.ofReal (C / (1 + ((m : ℝ) - x) ^ 2)))
        = ENNReal.ofReal (C * ∑' m : ℤ, (1 + ((m : ℝ) - x) ^ 2)⁻¹) := by
      rw [show (∑' m : ℤ, ENNReal.ofReal (C / (1 + ((m : ℝ) - x) ^ 2)))
            = ∑' m : ℤ, ENNReal.ofReal (C * (1 + ((m : ℝ) - x) ^ 2)⁻¹) from
          tsum_congr (fun m => by rw [div_eq_mul_inv])]
      simp_rw [ENNReal.ofReal_mul hC0]
      rw [ENNReal.tsum_mul_left,
        ← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsumm,
        ← ENNReal.ofReal_mul hC0]
    calc (∑' m : ℤ, ‖K ((m : ℝ) - x)‖ₑ)
        ≤ ∑' m : ℤ, ENNReal.ofReal (C / (1 + ((m : ℝ) - x) ^ 2)) := by
          apply ENNReal.tsum_le_tsum
          intro m
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hK _)
      _ = ENNReal.ofReal (C * ∑' m : ℤ, (1 + ((m : ℝ) - x) ^ 2)⁻¹) := h2sum
      _ ≤ ENNReal.ofReal (C * B0) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hB0 x) hC0)
      _ ≤ ENNReal.ofReal (C * (Real.pi + B0)) :=
          ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (by linarith [Real.pi_pos]) hC0)

end Work.BourgainPlan.IonescuWainger
