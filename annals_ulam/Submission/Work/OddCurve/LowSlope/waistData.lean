import Mathlib
import Submission.Work.OddCurve.LowSlope.Datum
import Submission.Work.OddCurve.LowSlope.waistRadial_eq_one
import Submission.Work.OddEnvelope.Main

/-!
# The two Radon data below the waist are the ball's

If the radial function `ρ` of a profile equals `1` on the waist `|u| ≤ tStar`, then the
integrals defining the two Radon data only see the integrands of the ball: for `0 < c ≤ tStar`
the probe `s ↦ c * s` stays in `|u| ≤ tStar`, so

* `radonPhi n ρ c = ballPhiData n c` (the first datum is the ball's `radonProfile (·)²`),
* `radonPsi n ρ c = 0` (the second datum vanishes by oddness of `s ↦ c * s`).

These are the two facts that make the deviation of the *glued* data from the ball's vanish on
the waist `(0, tStar]` — the input of the low-slope reconstruction.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set
open scoped Interval Topology

private lemma abs_mul_lt_tStar {c s : ℝ} (hc : 0 < c) (hcb : c < Work.OddEnvelope.tStar)
    (hs : |s| ≤ 1) : |c * s| < Work.OddEnvelope.tStar := by
  have h1 : c * |s| ≤ c * 1 := mul_le_mul_of_nonneg_left hs (le_of_lt hc)
  rw [mul_one] at h1
  rw [abs_mul, abs_of_pos hc]
  linarith

/-- **The first datum below the waist is the ball's.** -/
theorem radonPhi_eq_ballPhiData_of_waist {n : ℕ} {ρ : ℝ → ℝ}
    (hρ : ∀ u : ℝ, |u| < Work.OddEnvelope.tStar → ρ u = 1)
    {c : ℝ} (hc : 0 < c) (hcb : c < Work.OddEnvelope.tStar) :
    radonPhi n ρ c = ballPhiData n c := by
  have hpoint : ∀ s : ℝ, s ∈ Set.uIcc (-1 : ℝ) 1 →
      (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) * ((c * s) ^ 2 * ρ (c * s) ^ (2 * n + 2))
        = (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) * (c * s) ^ 2 := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs
    have hsabs : |s| ≤ 1 := abs_le.mpr hs
    rw [hρ (c * s) (abs_mul_lt_tStar hc hcb hsabs)]
    simp
  simp only [radonPhi, ballPhiData, Work.OddRadon.radonProfile]
  congr 1
  exact intervalIntegral.integral_congr hpoint

/-- **The second datum below the waist vanishes.** -/
theorem radonPsi_eq_zero_of_waist {n : ℕ} {ρ : ℝ → ℝ}
    (hρ : ∀ u : ℝ, |u| < Work.OddEnvelope.tStar → ρ u = 1)
    {c : ℝ} (hc : 0 < c) (hcb : c < Work.OddEnvelope.tStar) :
    radonPsi n ρ c = 0 := by
  have hpoint : ∀ s : ℝ, s ∈ Set.uIcc (-1 : ℝ) 1 →
      (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) * ((c * s) * ρ (c * s) ^ (2 * n + 1))
        = (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) * (c * s) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs
    have hsabs : |s| ≤ 1 := abs_le.mpr hs
    rw [hρ (c * s) (abs_mul_lt_tStar hc hcb hsabs)]
    simp
  simp only [radonPsi, Work.OddRadon.radonProfile]
  have hcongr : (∫ s in (-1 : ℝ)..1,
        (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) * ((c * s) * ρ (c * s) ^ (2 * n + 1)))
      = ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) * (c * s) :=
    intervalIntegral.integral_congr hpoint
  rw [hcongr, mul_eq_zero]
  right
  set e : ℝ := (((2 * n + 1 : ℕ) : ℝ)) / 2 - 2 with he
  set g : ℝ → ℝ := fun s : ℝ => (1 - s ^ 2) ^ e * (c * s) with hg
  have hodd : ∀ s : ℝ, g (-s) = -g s := by
    intro s
    simp only [hg, he]
    rw [neg_sq]
    ring
  have h1 : (∫ s in (-1 : ℝ)..1, g (-s)) = ∫ s in (-1 : ℝ)..1, g s := by
    simpa using intervalIntegral.integral_comp_neg (f := g) (a := (-1 : ℝ)) (b := 1)
  have h2 : (∫ s in (-1 : ℝ)..1, g (-s)) = ∫ s in (-1 : ℝ)..1, -g s :=
    intervalIntegral.integral_congr (fun s _ => hodd s)
  rw [h2, intervalIntegral.integral_neg] at h1
  show (∫ s in (-1 : ℝ)..1, g s) = 0
  linarith

end

end Work.OddCurve.LowSlope
