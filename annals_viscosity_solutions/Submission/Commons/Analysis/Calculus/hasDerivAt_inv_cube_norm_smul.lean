import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace Commons.Analysis.Calculus

/-- Derivative of the Newtonian force kernel `t ↦ (‖u t‖^3)⁻¹ • u t` along a curve. -/
theorem hasDerivAt_inv_cube_norm_smul {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u : ℝ → F} {u' : F} {t : ℝ} (hu : HasDerivAt u u' t) (hne : u t ≠ 0) :
    HasDerivAt (fun s : ℝ => ((‖u s‖ ^ 3)⁻¹) • u s)
      (((‖u t‖ ^ 3)⁻¹) • u' - (3 * ((‖u t‖ ^ 5)⁻¹ * inner ℝ (u t) u')) • u t) t := by
  have hu_ne : ‖u t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hsq : HasDerivAt (fun s : ℝ => ‖u s‖ ^ 2) (2 * inner ℝ (u t) u') t := hu.norm_sq
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (‖u s‖ ^ 2))
      ((2 * inner ℝ (u t) u') / (2 * Real.sqrt (‖u t‖ ^ 2))) t :=
    hsq.sqrt (pow_ne_zero 2 hu_ne)
  have hnorm : HasDerivAt (fun s : ℝ => ‖u s‖) (inner ℝ (u t) u' / ‖u t‖) t := by
    refine (hsqrt.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun s => (Real.sqrt_sq (norm_nonneg _)).symm
    · rw [Real.sqrt_sq (norm_nonneg _)]
      field_simp
  have h3 : HasDerivAt (fun s : ℝ => ‖u s‖ ^ 3)
      (3 * ‖u t‖ ^ 2 * (inner ℝ (u t) u' / ‖u t‖)) t := by
    have h := (hnorm.pow 3).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => rfl)
    refine h.congr_deriv ?_
    norm_num
  have hinv : HasDerivAt (fun s : ℝ => (‖u s‖ ^ 3)⁻¹)
      (-(3 * ‖u t‖ ^ 2 * (inner ℝ (u t) u' / ‖u t‖)) / (‖u t‖ ^ 3) ^ 2) t :=
    (h3.inv (pow_ne_zero 3 hu_ne)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => rfl)
  have hderiv : (-(3 * ‖u t‖ ^ 2 * (inner ℝ (u t) u' / ‖u t‖)) / (‖u t‖ ^ 3) ^ 2)
      = -(3 * ((‖u t‖ ^ 5)⁻¹ * inner ℝ (u t) u')) := by
    field_simp
  refine ((hinv.smul hu).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => rfl)).congr_deriv ?_
  rw [hderiv]
  simp [sub_eq_add_neg, neg_smul]

end Commons.Analysis.Calculus