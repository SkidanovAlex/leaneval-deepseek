import Mathlib
import Submission.Work.OddCurve.LowSlope.CruxStatements
import Submission.Work.OddCurve.LowSlope.radon_data_identity
import Submission.Work.OddCurve.LowSlope.section_ibp
import Submission.Work.OddCurve.LowSlope.radon_change_gen
import Submission.Work.OddCurve.LowSlope.radon_data_interface
import Submission.Work.OddCurve.LowSlope.radon_data_eq_inertiaIntegral_Ioo

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **Prop. `workHARD1` in one dimension**, in its *weak* (open-interval) form: the profile only
has to be continuous on `[-1,1]` and `C¹` on the open interval `(-1,1)` — the closed-interval
`C¹` hypothesis of `RadonDataEqInertiaIntegral` is not needed, since the proof never
differentiates `f` outside the chord `(-(x s), y s)`, which is contained in `(-1,1)`.

This is `radon_data_eq_inertiaIntegral_Ioo` (`LowSlope/radon_data_eq_inertiaIntegral_Ioo.lean`)
restated in the raw `sphereArea * ∫` form via `radonProfile_eq_natpow`. -/
theorem radon_data_eq_inertiaIntegral_weak (n : ℕ) (hn : 1 ≤ n) :
    ∀ (f ρ x y : ℝ → ℝ) (s : ℝ),
      0 < s →
      ContinuousOn f (Set.Icc (-1 : ℝ) 1) →
      ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) →
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) →
      ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1) →
      StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) →
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u)) →
      (∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) (Real.sqrt (1 + s ^ 2))⁻¹,
        0 ≤ ρ u + u * deriv ρ u) →
      ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * (Real.sqrt (1 + s ^ 2))⁻¹ = y s →
      ρ (-(Real.sqrt (1 + s ^ 2))⁻¹) * (-(Real.sqrt (1 + s ^ 2))⁻¹) = -(x s) →
      (∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
        ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ∈ Set.Ioo (-(x s)) (y s)) →
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
      Work.OddRadon.sphereArea (2 * n - 2) *
          (∫ ν in (-1 : ℝ)..1, (1 - ν ^ 2) ^ (n - 1) *
            (((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ^ 2 *
              ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ^ (2 * n + 2)) / Real.sqrt (1 - ν ^ 2))
        = (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) *
          Real.sqrt (1 + s ^ 2) * inertiaIntegral n f x y s := by
  intro f ρ x y s hs _hfcont hfC1 hρpos hρC1 hmono hρ hderivn hend_y hend_x hmem hxI hyI
    hfy hfx huniqy huniqx hxy hrad hintA hintB
  have hcpos : 0 < (Real.sqrt (1 + s ^ 2))⁻¹ := by positivity
  have hIoo := radon_data_eq_inertiaIntegral_Ioo n hn f ρ x y s hs hfC1 hρpos hρC1 hmono hρ
    hderivn hend_y hend_x hmem hxI hyI hfy hfx huniqy huniqx hxy hrad hintA hintB
  have hbridge : Work.OddRadon.sphereArea (2 * n - 2) *
        (∫ ν in (-1 : ℝ)..1, (1 - ν ^ 2) ^ (n - 1) *
          (((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ^ 2 *
            ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ^ (2 * n + 2)) / Real.sqrt (1 - ν ^ 2))
      = Work.OddRadon.radonProfile (2 * n + 1)
          (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) ((Real.sqrt (1 + s ^ 2))⁻¹) := by
    rw [radonProfile_eq_natpow n hn (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2))
      (c := (Real.sqrt (1 + s ^ 2))⁻¹) hcpos]
  rw [hbridge, hIoo]

end

end Work.OddCurve.LowSlope
