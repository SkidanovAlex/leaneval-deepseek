import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.TauSmAdm

open MeasureTheory

/-- The sixth iterated derivative of `z ↦ f (a • z)` at `p` is obtained from the sixth iterated
derivative of `f` at `a • p` by multiplying by the scalar `a ^ 6`. -/
lemma norm_iteratedFDeriv_comp_const_smul_eq
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖iteratedFDeriv ℝ 6 (fun z => f (a • z)) p‖
      = |a| ^ 6 * ‖iteratedFDeriv ℝ 6 f (a • p)‖ := by
  have h6c : ContDiff ℝ ((6 : ℕ) : ℕ∞) f := hf.of_le (mod_cast le_top)
  rw [iteratedFDeriv_comp_const_smul a h6c]
  rw [norm_smul, Real.norm_eq_abs, abs_pow]

theorem integrable_and_integral_iteratedFDeriv_comp_const_smul
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {a : ℝ} (ha : a ≠ 0) :
    (MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        ‖iteratedFDeriv ℝ 6 (fun z => f (a • z)) p‖) ↔
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖iteratedFDeriv ℝ 6 f p‖)) ∧
    (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 (fun z => f (a • z)) p‖)
      = |a| ^ 3 * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 f p‖) := by
  have hpt : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖iteratedFDeriv ℝ 6 (fun z => f (a • z)) p‖ = |a| ^ 6 * ‖iteratedFDeriv ℝ 6 f (a • p)‖ :=
    fun p => norm_iteratedFDeriv_comp_const_smul_eq hf a p
  have hc : IsUnit (|a| ^ 6 : ℝ) :=
    isUnit_iff_ne_zero.mpr (pow_ne_zero 6 (abs_ne_zero.mpr ha))
  constructor
  · simp only [hpt]
    rw [MeasureTheory.integrable_const_mul_iff hc]
    exact MeasureTheory.integrable_comp_smul_iff volume (fun q => ‖iteratedFDeriv ℝ 6 f q‖) ha
  · simp only [hpt]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.Measure.integral_comp_smul volume (fun q => ‖iteratedFDeriv ℝ 6 f q‖) a,
      finrank_euclideanSpace_fin]
    rw [abs_inv, abs_pow]
    simp only [smul_eq_mul]
    have h6 : |a| ^ 6 * (|a| ^ 3)⁻¹ = |a| ^ 3 := by
      rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero 3 (abs_ne_zero.mpr ha)), mul_one]
    rw [← mul_assoc, h6]

end Work.BoseBoxFock.TauSmAdm
