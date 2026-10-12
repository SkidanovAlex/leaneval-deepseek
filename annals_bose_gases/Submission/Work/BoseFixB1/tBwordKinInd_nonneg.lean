import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.A.tBwordBInd_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The centred cube of negative side contains no point. -/
private lemma not_mem_acube_of_neg' {a : ℝ} (ha : a < 0) (y : ℝ³) :
    y ∉ Submission.BoseGases.acube a := by
  intro hy
  have h0 : y 0 ∈ Set.Icc (-a / 2) (a / 2) := hy 0
  rw [Set.mem_Icc] at h0
  linarith [h0.1, h0.2]

/-- The `N`-particle centred box of negative side is empty (for any occupied slot). -/
private lemma abox_eq_empty_of_neg' {N : ℕ} {a : ℝ} (ha : a < 0) (i : Fin N) :
    Submission.BoseGases.abox N a = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  exact not_mem_acube_of_neg' ha (x i)
    ((Submission.BoseGases.mem_abox_iff N a x).mp hx i)

/-- The normalised slot content is nonnegative. -/
private lemma inv_cube_mul_abox_integral_sq_nonneg' (a : ℝ) {N : ℕ} (i : Fin N)
    (g : Submission.BoseGases.X N → ℝ) :
    0 ≤ (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N a, g x ^ 2 := by
  rcases le_or_gt 0 a with ha | ha
  · exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ha 3))
      (integral_nonneg fun x => sq_nonneg (g x))
  · rw [abox_eq_empty_of_neg' ha i]
    simp

/-- **The spectral half of FS `eq:appTB` is nonnegative**, for every real box side `a`. -/
theorem tBwordKinInd_nonneg {a : ℝ} {A : Set ℝ³} {volA : ℝ} {χ : ℝ³ → ℝ} {c : ℝ} {N : ℕ}
    (Ψ : Submission.BoseGases.X N → ℝ) :
    0 ≤ Work.UBBInputs8.tBwordKinInd a A volA χ c Ψ := by
  rw [Work.UBBInputs8.tBwordKinInd]
  unfold Work.UBBInputs8.tBdiagFormInd
  refine Finset.sum_nonneg fun i _ => ?_
  refine mul_nonneg (le_of_lt Work.SmallBoxTBWord.twoPiInv3_pos) ?_
  refine integral_nonneg fun p => ?_
  refine mul_nonneg ?_ ?_
  · exact Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖
  · exact inv_cube_mul_abox_integral_sq_nonneg' a i
      (fun x => ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖)

end Work.BoseFixB1
