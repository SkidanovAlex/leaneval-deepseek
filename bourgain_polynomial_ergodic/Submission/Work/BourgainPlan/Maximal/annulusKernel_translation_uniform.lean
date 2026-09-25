import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusKernel_translation
import Submission.Work.BourgainPlan.Maximal.annulusKernel_size
import Submission.Work.BourgainPlan.Maximal.tsum_annulus_moment

/-!
# Uniform-in-`j` pointwise translation estimate for the annulus kernel family

`annulusKernel_translation` gives, for each shift `j : ℤ`, a constant `C(j)` such that

`(∑_n ‖K_{j+n}(z - y) - K_{j+n}(z)‖²)^{1/2} ≤ C(j) |y| / |z|²`  (`2|y| < |z|`).

That constant is in fact independent of `j`: the pointwise bound
`annulusKernel_difference_bound` is uniform in the scale `m`, and the scale sum is compared with the
universal geometric bound `tsum_annulus_moment`.  This file makes that uniformity explicit, which is
what the square-function / maximal assembly needs.
-/

open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter

theorem annulusKernel_translation_uniform (b : ℤ → ℝ → ℂ)
    (hb : Work.BourgainPlan.Maximal.AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℤ, ∀ y z : ℝ, 2 * |y| < |z| →
      (∑' n : ℤ, ‖FourierTransform.fourierInv (b (j + n)) (z - y)
        - FourierTransform.fourierInv (b (j + n)) z‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ ENNReal.ofReal (C * |y| / |z| ^ 2) := by
  obtain ⟨C₁, hC₁, hPt⟩ := annulusKernel_difference_bound b hb hsmooth
  obtain ⟨K, hK, hGeom⟩ := tsum_annulus_moment
  refine ⟨C₁ * Real.sqrt K + 1, by positivity, fun j y z hyz => ?_⟩
  have hzpos : 0 < |z| := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 2 * |y|) hyz
  have hz : z ≠ 0 := abs_pos.mp hzpos
  obtain ⟨hGsumm, hGbd⟩ := hGeom z hz
  set R : ℤ → ℝ := fun m =>
    (C₁ * |y| * ((2 : ℝ) ^ (-m)) ^ 2 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ))) ^ 2 with hR
  have hRnn : ∀ m, 0 ≤ R m := fun m => sq_nonneg _
  -- pointwise ENNReal comparison
  have hpoint : ∀ n : ℤ,
      ‖FourierTransform.fourierInv (b (j + n)) (z - y)
          - FourierTransform.fourierInv (b (j + n)) z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (R (j + n)) := by
    intro n
    have h := hPt (j + n) y z hyz
    have h1 : ‖FourierTransform.fourierInv (b (j + n)) (z - y)
        - FourierTransform.fourierInv (b (j + n)) z‖ₑ
        = ENNReal.ofReal ‖FourierTransform.fourierInv (b (j + n)) (z - y)
            - FourierTransform.fourierInv (b (j + n)) z‖ := (ofReal_norm _).symm
    rw [h1, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, hR]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)
  -- the square of the geometric bound
  have hReq : ∀ m, R m = (C₁ * |y|) ^ 2
      * (((2 : ℝ) ^ (-m)) ^ 4 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(6 : ℝ))) := by
    intro m
    have hpos : 0 < 1 + (2 : ℝ) ^ (-m) * |z| := by positivity
    have h6 : (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(6 : ℝ))
        = ((1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(3 : ℝ))) ^ 2 := by
      rw [show (-(6 : ℝ)) = (-3) * 2 by norm_num, Real.rpow_mul hpos.le, Real.rpow_two]
    rw [hR, h6]
    ring
  have hRsumm : Summable R := by
    rw [show R = fun m => (C₁ * |y|) ^ 2
      * (((2 : ℝ) ^ (-m)) ^ 4 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(6 : ℝ))) from funext hReq]
    exact hGsumm.mul_left _
  have h4 : |z| ^ (-(4 : ℝ)) = (|z| ^ 2)⁻¹ * (|z| ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg z), show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, show (|z| ^ (4 : ℕ) : ℝ) = (|z| ^ 2) ^ 2 by ring, pow_two, mul_inv]
  have h5 : (C₁ * Real.sqrt K + 1) ^ 2 * |y| ^ 2 * ((|z| ^ 2)⁻¹ * (|z| ^ 2)⁻¹)
      = ((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2 := by
    have hz2 : (|z| ^ 2) ≠ 0 := by positivity
    rw [div_pow, mul_pow]
    field_simp
  have hC2 : C₁ ^ 2 * K ≤ (C₁ * Real.sqrt K + 1) ^ 2 := by
    have h := Real.sq_sqrt hK.le
    nlinarith [h, Real.sqrt_nonneg K, hC₁.le, sq_nonneg (C₁ * Real.sqrt K)]
  have hRbd : ∑' m : ℤ, R m ≤ ((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2 := by
    rw [show R = fun m => (C₁ * |y|) ^ 2
      * (((2 : ℝ) ^ (-m)) ^ 4 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(6 : ℝ))) from funext hReq,
      Summable.tsum_mul_left _ hGsumm]
    calc (C₁ * |y|) ^ 2
          * ∑' m : ℤ, ((2 : ℝ) ^ (-m)) ^ 4 * (1 + (2 : ℝ) ^ (-m) * |z|) ^ (-(6 : ℝ))
        ≤ (C₁ * |y|) ^ 2 * (K * |z| ^ (-(4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hGbd (by positivity)
      _ = C₁ ^ 2 * K * |y| ^ 2 * ((|z| ^ 2)⁻¹ * (|z| ^ 2)⁻¹) := by rw [h4]; ring
      _ ≤ (C₁ * Real.sqrt K + 1) ^ 2 * |y| ^ 2 * ((|z| ^ 2)⁻¹ * (|z| ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 (by positivity))
            (by positivity)
      _ = ((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2 := h5
  -- ENNReal assembly
  have hsum1 : (∑' n : ℤ, ‖FourierTransform.fourierInv (b (j + n)) (z - y)
        - FourierTransform.fourierInv (b (j + n)) z‖ₑ ^ (2 : ℝ))
      ≤ ∑' n : ℤ, ENNReal.ofReal (R (j + n)) := ENNReal.tsum_le_tsum hpoint
  have hreindex : (∑' n : ℤ, ENNReal.ofReal (R (j + n))) = ∑' m : ℤ, ENNReal.ofReal (R m) := by
    simpa using Equiv.tsum_eq (Equiv.addLeft j) (fun m : ℤ => ENNReal.ofReal (R m))
  have hsum2 : (∑' m : ℤ, ENNReal.ofReal (R m)) = ENNReal.ofReal (∑' m : ℤ, R m) :=
    (ENNReal.ofReal_tsum_of_nonneg hRnn hRsumm).symm
  have hfinal : (∑' n : ℤ, ‖FourierTransform.fourierInv (b (j + n)) (z - y)
        - FourierTransform.fourierInv (b (j + n)) z‖ₑ ^ (2 : ℝ))
      ≤ ENNReal.ofReal (((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2) := by
    calc _ ≤ ∑' n : ℤ, ENNReal.ofReal (R (j + n)) := hsum1
      _ = ∑' m : ℤ, ENNReal.ofReal (R m) := hreindex
      _ = ENNReal.ofReal (∑' m : ℤ, R m) := hsum2
      _ ≤ ENNReal.ofReal (((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2) :=
          ENNReal.ofReal_le_ofReal hRbd
  calc (∑' n : ℤ, ‖FourierTransform.fourierInv (b (j + n)) (z - y)
        - FourierTransform.fourierInv (b (j + n)) z‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2)) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hfinal (by norm_num)
    _ = ENNReal.ofReal ((((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) ^ 2) ^ ((1 : ℝ) / 2)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ = ENNReal.ofReal ((C₁ * Real.sqrt K + 1) * |y| / |z| ^ 2) := by
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]

end Work.BourgainPlan.Maximal
