import Submission.NBody.MarchalBumpPotential
import Submission.NBody.MarchalStandardVariation

/-!
# The standard variation never destroys a separation

If `δ ≠ 0` is *not parallel* to a vector `xi`, then the standard variation `stdVar δ T t`, which is
`stdCoef δ T t • δ` with `stdCoef ∈ [0,1]`, cannot bring the parabolic profile
`(c t^{2/3}) • xi` down to zero: the component orthogonal to `δ` survives.  Quantitatively,

  `√(‖xi‖² - ⟪xi,δ⟫²/‖δ‖²) · (c t^{2/3}) ≤ ‖(c t^{2/3}) • xi + stdVar δ T t‖`.

Consequences used later:

* every pair of the bumped parabolic profile stays separated (the "good direction" condition);
* the pair potential gain of a good direction is interval integrable on `(0,T)`
  (with the dominating function `C t^{-2/3}`).
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The orthogonal component never disappears.**  For `δ ≠ 0` and any real `s`,
`√(‖a‖² - ⟪a,δ⟫²/‖δ‖²) ≤ ‖a + s • δ‖`. -/
theorem sqrt_gap_le_norm_add_smul {a δ : E} (hδ : δ ≠ 0) (s : ℝ) :
    Real.sqrt (‖a‖^2 - (inner ℝ a δ)^2 / ‖δ‖^2) ≤ ‖a + s • δ‖ := by
  have hd : 0 < ‖δ‖^2 := pow_pos (norm_pos_iff.mpr hδ) 2
  have hcs : (inner ℝ a δ)^2 ≤ ‖a‖^2 * ‖δ‖^2 := by
    have h := abs_real_inner_le_norm a δ
    have h1 : |inner ℝ a δ|^2 ≤ (‖a‖ * ‖δ‖)^2 :=
      pow_le_pow_left₀ (abs_nonneg _) h 2
    rwa [sq_abs, mul_pow] at h1
  have hnn : 0 ≤ ‖a‖^2 - (inner ℝ a δ)^2 / ‖δ‖^2 := by
    rw [sub_nonneg, div_le_iff₀ hd]
    linarith
  rw [Real.sqrt_le_left (show (0:ℝ) ≤ ‖a + s • δ‖ from norm_nonneg _)]
  have hq : ‖a + s • δ‖^2 = ‖a‖^2 + 2 * s * (inner ℝ a δ) + s^2 * ‖δ‖^2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hq]
  have hkey : 0 ≤ (s * ‖δ‖^2 + inner ℝ a δ)^2 := sq_nonneg _
  have h3 : -((inner ℝ a δ)^2 / ‖δ‖^2) ≤ 2 * s * (inner ℝ a δ) + s^2 * ‖δ‖^2 := by
    rw [← neg_div, div_le_iff₀ hd]
    nlinarith [hkey]
  linarith

/-- **The parabolic profile plus the standard variation.**  The lower bound in the rescaled
variables. -/
theorem mul_sqrt_gap_le_norm_parabolic_add_stdVar {xi δ : E} (hδ : δ ≠ 0) {c T t : ℝ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) :
    Real.sqrt (‖xi‖^2 - (inner ℝ xi δ)^2 / ‖δ‖^2) * (c * t ^ ((2:ℝ)/3))
      ≤ ‖(c * t ^ ((2:ℝ)/3)) • xi + stdVar δ T t‖ := by
  have hmain := sqrt_gap_le_norm_add_smul (a := (c * t ^ ((2:ℝ)/3)) • xi) hδ
    (stdCoef δ T t)
  rw [stdVar]
  have hnorm : ‖(c * t ^ ((2:ℝ)/3)) • xi‖^2
      = (c * t ^ ((2:ℝ)/3))^2 * ‖xi‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hinner : (inner ℝ ((c * t ^ ((2:ℝ)/3)) • xi) δ)^2
      = (c * t ^ ((2:ℝ)/3))^2 * (inner ℝ xi δ)^2 := by
    rw [real_inner_smul_left, mul_pow]
  have hgap : ‖((c * t ^ ((2:ℝ)/3)) • xi)‖^2
        - (inner ℝ ((c * t ^ ((2:ℝ)/3)) • xi) δ)^2 / ‖δ‖^2
      = (c * t ^ ((2:ℝ)/3))^2 * (‖xi‖^2 - (inner ℝ xi δ)^2 / ‖δ‖^2) := by
    rw [hnorm, hinner]
    ring
  rw [hgap] at hmain
  have hsq : Real.sqrt ((c * t ^ ((2:ℝ)/3))^2
      * (‖xi‖^2 - (inner ℝ xi δ)^2 / ‖δ‖^2))
      = Real.sqrt ((c * t ^ ((2:ℝ)/3))^2)
        * Real.sqrt (‖xi‖^2 - (inner ℝ xi δ)^2 / ‖δ‖^2) :=
    Real.sqrt_mul (sq_nonneg _) _
  rw [hsq] at hmain
  have hsqa : Real.sqrt ((c * t ^ ((2:ℝ)/3))^2) = c * t ^ ((2:ℝ)/3) := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hc (Real.rpow_nonneg ht _))]
  rw [hsqa] at hmain
  rw [mul_comm] at hmain
  exact hmain

/-- A single pair term of the model potential gain is interval integrable when the direction is not
parallel to the pair separation. -/
theorem intervalIntegrable_potPairVal_of_good {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N}
    {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (sbar : EN E N) {δ : E} (hδ : δ ≠ 0)
    (hgood : ∀ j ∈ k.erase i₀,
      (inner ℝ (sbar i₀ - sbar j) δ)^2 < ‖sbar i₀ - sbar j‖^2 * ‖δ‖^2) :
    ∀ j ∈ k.erase i₀, IntervalIntegrable (fun t : ℝ =>
      (‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹
        - (Real.sqrt κ * t ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖)⁻¹) volume 0 T := by
  intro j hj
  have hzj : 0 < ‖sbar i₀ - sbar j‖ := by
    by_contra hcon
    have h0 : sbar i₀ - sbar j = 0 :=
      norm_eq_zero.mp (le_antisymm (le_of_not_gt hcon) (norm_nonneg _))
    have h := hgood j hj
    rw [h0] at h
    simp at h
  have hgappos : 0 < ‖sbar i₀ - sbar j‖^2 - (inner ℝ (sbar i₀ - sbar j) δ)^2 / ‖δ‖^2 := by
    have hd : 0 < ‖δ‖^2 := pow_pos (norm_pos_iff.mpr hδ) 2
    rw [sub_pos, div_lt_iff₀ hd]
    exact hgood j hj
  set g : ℝ := Real.sqrt (‖sbar i₀ - sbar j‖^2
      - (inner ℝ (sbar i₀ - sbar j) δ)^2 / ‖δ‖^2) with hg
  have hgpos : 0 < g := Real.sqrt_pos.mpr hgappos
  set C : ℝ := 1 / (g * Real.sqrt κ) + 1 / (Real.sqrt κ * ‖sbar i₀ - sbar j‖) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]; positivity
  have hmaj : IntervalIntegrable (fun t : ℝ => C * t ^ (-((2:ℝ)/3))) volume 0 T :=
    (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := T) (r := -((2:ℝ)/3))
      (by norm_num)).const_mul C
  refine hmaj.mono_fun' ?_ ?_
  · rw [Set.uIoc_of_le hT]
    have hpow : Continuous (fun t : ℝ => t ^ ((2:ℝ)/3)) :=
      continuous_rpow_const (q := (2:ℝ)/3) (by norm_num)
    have hcont1 : Continuous (fun t : ℝ => (Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j)) :=
      (continuous_const.mul hpow).smul continuous_const
    have hcont : Continuous (fun t : ℝ => (Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j)
        + stdVar δ T t) := hcont1.add (continuous_stdVar hδ)
    have hinv1 : ContinuousOn (fun t : ℝ =>
        (‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹)
        (Set.Ioc (0:ℝ) T) := by
      refine hcont.continuousOn.norm.inv₀ fun t ht => ?_
      have ht0 : 0 < t := ht.1
      have hlow := mul_sqrt_gap_le_norm_parabolic_add_stdVar (xi := sbar i₀ - sbar j)
        (T := T) hδ (Real.sqrt_nonneg κ) ht0.le
      rw [← hg] at hlow
      have hpos : 0 < g * (Real.sqrt κ * t ^ ((2:ℝ)/3)) :=
        mul_pos hgpos (mul_pos (Real.sqrt_pos.mpr hκ) (Real.rpow_pos_of_pos ht0 _))
      exact ne_of_gt (lt_of_lt_of_le hpos hlow)
    have hinv2 : ContinuousOn (fun t : ℝ =>
        (Real.sqrt κ * t ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖)⁻¹) (Set.Ioc (0:ℝ) T) := by
      refine (((continuous_const.mul hpow).mul continuous_const).continuousOn).inv₀ fun t ht => ?_
      have ht0 : 0 < t := ht.1
      exact ne_of_gt (mul_pos (mul_pos (Real.sqrt_pos.mpr hκ)
        (Real.rpow_pos_of_pos ht0 _)) hzj)
    exact (hinv1.aestronglyMeasurable measurableSet_Ioc).sub
      (hinv2.aestronglyMeasurable measurableSet_Ioc)
  · rw [Set.uIoc_of_le hT]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have hlow := mul_sqrt_gap_le_norm_parabolic_add_stdVar (xi := sbar i₀ - sbar j)
      (T := T) hδ (Real.sqrt_nonneg κ) ht0.le
    rw [← hg] at hlow
    have hbpos : 0 < g * (Real.sqrt κ * t ^ ((2:ℝ)/3)) :=
      mul_pos hgpos (mul_pos (Real.sqrt_pos.mpr hκ) (Real.rpow_pos_of_pos ht0 _))
    have hnormpos : 0 < ‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖ :=
      lt_of_lt_of_le hbpos hlow
    have hbound1 : (‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹
        ≤ (g * Real.sqrt κ)⁻¹ * t ^ (-((2:ℝ)/3)) := by
      have h1 : (‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹
          ≤ (g * (Real.sqrt κ * t ^ ((2:ℝ)/3)))⁻¹ :=
        (inv_le_inv₀ hnormpos hbpos).mpr hlow
      refine h1.trans (le_of_eq ?_)
      rw [mul_inv, mul_inv, ← Real.rpow_neg ht0.le, inv_eq_one_div]
      ring
    have hbound2 : (Real.sqrt κ * t ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖)⁻¹
        = (Real.sqrt κ * ‖sbar i₀ - sbar j‖)⁻¹ * t ^ (-((2:ℝ)/3)) := by
      rw [mul_inv, mul_inv, ← Real.rpow_neg ht0.le, inv_eq_one_div]
      ring
    have hrp : 0 ≤ t ^ (-((2:ℝ)/3)) := Real.rpow_nonneg ht0.le _
    have hC1 : (g * Real.sqrt κ)⁻¹ ≤ C := by
      rw [hC, inv_eq_one_div]
      exact le_add_of_nonneg_right (by positivity)
    have hC2 : (Real.sqrt κ * ‖sbar i₀ - sbar j‖)⁻¹ ≤ C := by
      rw [hC, inv_eq_one_div]
      exact le_add_of_nonneg_left (by positivity)
    have hle1 := mul_le_mul_of_nonneg_right hC1 hrp
    have hle2 := mul_le_mul_of_nonneg_right hC2 hrp
    have hA0 : 0 ≤ (Real.sqrt κ * ‖sbar i₀ - sbar j‖)⁻¹ * t ^ (-((2:ℝ)/3)) :=
      mul_nonneg (by positivity) hrp
    have hv0 : 0 ≤ (‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹ :=
      inv_nonneg.mpr (norm_nonneg _)
    rw [Real.norm_eq_abs, hbound2]
    refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith

end Submission.NBody
