import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs
import Submission.Work.OddCurve.LowSlope.radon_data_identity
import Submission.Work.OddCurve.LowSlope.radon_centroid_identity

/-!
# The Radon data of a body of revolution, in the vocabulary of the pipeline

`Work.OddRadon.radonProfile` evaluates the one-variable spherical-Radon transform with the real
exponent `(d:ℝ)/2 - 2`.  The two one-dimensional identities of this directory
(`radon_data_eq_inertiaIntegral_proof`, `radon_data_eq_centIntegral`) are stated with *natural*
powers.  This file rewrites the transform into natural powers and records the two identities as
equalities of `radonProfile` with the section integrals of the body — the form the low-slope
pipeline consumes:

* the data of `w ↦ w_1² ρ(w)^{2n+2}` is `(2n+2)|B^{2n-1}|√(1+s²)` times the inertia integral;
* the data of `w ↦ w_1 ρ(w)^{2n+1}` is `(2n+1)|B^{2n-1}|√(1+s²)` times the centroid integral.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The one-variable Radon transform in natural powers**: for `c > 0` the real exponent
`(2n+1)/2 - 2 = n - 3/2` is `(n-1) - 1/2`. -/
lemma radonProfile_eq_natpow (n : ℕ) (hn : 1 ≤ n) (γ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    Work.OddRadon.radonProfile (2 * n + 1) γ c
      = Work.OddRadon.sphereArea (2 * n - 2) *
        (∫ ν in (-1 : ℝ)..1, (1 - ν ^ 2) ^ (n - 1) * γ (c * ν) / Real.sqrt (1 - ν ^ 2)) := by
  rw [Work.OddRadon.radonProfile]
  have hidx : 2 * n + 1 - 3 = 2 * n - 2 := by omega
  rw [hidx]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) (1 : ℝ),
    Measure.ae_ne (volume : Measure ℝ) (-1 : ℝ)] with ν hne1 _ hin
  rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hin
  have hpos : 0 < 1 - ν ^ 2 := by
    have h1 : ν < 1 := lt_of_le_of_ne hin.2 hne1
    nlinarith [hin.1, h1, sq_nonneg ν]
  have hexp : (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) = ((n : ℝ) - 1) + (-(1 / 2)) := by
    push_cast; ring
  have hcast : (((n : ℝ) - 1)) = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [hexp, Real.rpow_add hpos, hcast, Real.rpow_natCast (1 - ν ^ 2) (n - 1),
    Real.rpow_neg hpos.le ((1 : ℝ) / 2), Real.sqrt_eq_rpow, div_eq_mul_inv]
  ring

/-- **The inertia data of a body of revolution.** -/
theorem radonProfile_data_eq_inertiaIntegral (n : ℕ) (hn : 1 ≤ n) :
    ∀ (f ρ x y : ℝ → ℝ) (s : ℝ),
      0 < s →
      ContDiffOn ℝ 1 f (Set.Icc (-1 : ℝ) 1) →
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) →
      ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1) →
      StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) →
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u)) →
      (∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) (Real.sqrt (1 + s ^ 2))⁻¹,
        0 ≤ ρ u + u * deriv ρ u) →
      ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹ = y s →
      ρ (-(Real.sqrt (1 + s ^ 2))⁻¹) * (-(Real.sqrt (1 + s ^ 2))⁻¹) = -(x s) →
      (∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
        ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ∈
          Set.Ioo (-(x s)) (y s)) →
      -(x s) ∈ Set.Ioo (-1 : ℝ) 1 →
      y s ∈ Set.Ioo (-1 : ℝ) 1 →
      f (y s) = s * y s → f (-(x s)) = s * x s →
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = s * t → t = y s) →
      (∀ t ∈ Set.Ioo (-1 : ℝ) 0, f t = -(s * t) → t = -(x s)) →
      -(x s) < y s →
      (∀ t ∈ Set.Ioo (-(x s)) (y s), 0 < rad0 f s t) →
      IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
        rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-(x s)) (y s) →
      IntervalIntegrable (fun t : ℝ => t ^ 2 * rad0 f s t ^ (n - 1) *
        Real.sqrt (rad0 f s t)) volume (-(x s)) (y s) →
      Work.OddRadon.radonProfile (2 * n + 1)
          (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) ((Real.sqrt (1 + s ^ 2))⁻¹)
        = (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) *
          inertiaIntegral n f x y s := by
  intro f ρ x y s hs hfC1 hρpos hρC1 hmono hρ hderivn hend_y hend_x hmem hmx hy hfy hfx
    hrootR hrootL hlt hpos hI1 hI2
  have hcpos : 0 < (Real.sqrt (1 + s ^ 2))⁻¹ := by positivity
  rw [radonProfile_eq_natpow n hn _ hcpos]
  exact radon_data_eq_inertiaIntegral_proof n hn f ρ x y s hs hfC1 hρpos hρC1 hmono hρ hderivn
    hend_y hend_x hmem hmx hy hfy hfx hrootR hrootL hlt hpos hI1 hI2

/-- **The centroid data of a body of revolution.** -/
theorem radonProfile_data_eq_centIntegral (n : ℕ) (hn : 1 ≤ n) :
    ∀ (f ρ x y : ℝ → ℝ) (s : ℝ),
      0 < s →
      ContDiffOn ℝ 1 f (Set.Icc (-1 : ℝ) 1) →
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) →
      ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1) →
      StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) →
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u)) →
      (∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) (Real.sqrt (1 + s ^ 2))⁻¹,
        0 ≤ ρ u + u * deriv ρ u) →
      ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹ = y s →
      ρ (-(Real.sqrt (1 + s ^ 2))⁻¹) * (-(Real.sqrt (1 + s ^ 2))⁻¹) = -(x s) →
      (∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
        ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ∈
          Set.Ioo (-(x s)) (y s)) →
      -(x s) ∈ Set.Ioo (-1 : ℝ) 1 →
      y s ∈ Set.Ioo (-1 : ℝ) 1 →
      f (y s) = s * y s → f (-(x s)) = s * x s →
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = s * t → t = y s) →
      (∀ t ∈ Set.Ioo (-1 : ℝ) 0, f t = -(s * t) → t = -(x s)) →
      -(x s) < y s →
      (∀ t ∈ Set.Ioo (-(x s)) (y s), 0 < rad0 f s t) →
      IntervalIntegrable (fun t : ℝ => t * f t * (f t - t * deriv f t) *
        rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-(x s)) (y s) →
      IntervalIntegrable (fun t : ℝ => t * rad0 f s t ^ (n - 1) *
        Real.sqrt (rad0 f s t)) volume (-(x s)) (y s) →
      Work.OddRadon.radonProfile (2 * n + 1)
          (fun u : ℝ => u * ρ u ^ (2 * n + 1)) ((Real.sqrt (1 + s ^ 2))⁻¹)
        = (2 * (n : ℝ) + 1) * ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) *
          centIntegral n f x y s := by
  intro f ρ x y s hs hfC1 hρpos hρC1 hmono hρ hderivn hend_y hend_x hmem hmx hy hfy hfx
    hrootR hrootL hlt hpos hI1 hI2
  have hcpos : 0 < (Real.sqrt (1 + s ^ 2))⁻¹ := by positivity
  rw [radonProfile_eq_natpow n hn _ hcpos]
  exact radon_data_eq_centIntegral n hn f ρ x y s hs hfC1 hρpos hρC1 hmono hρ hderivn
    hend_y hend_x hmem hmx hy hfy hfx hrootR hrootL hlt hpos hI1 hI2

end

end Work.OddCurve.LowSlope
