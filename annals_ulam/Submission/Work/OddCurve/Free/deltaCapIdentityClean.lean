import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDataDefs
import Submission.Work.OddCurve.LowSlope.intervalIntegrable_radonIntegrands
import Submission.Work.OddCurve.LowSlope.radonInverse_radonPhi
import Submission.Work.OddCurve.LowSlope.QuantDefs

/-!
# A self-contained copy of the cap identity for the glued deviation data

`deltaA n ρ = GlueF n ρ - ballPhiData n` and `deltaB n ρ = GlueG n ρ` are the deviations of the
glued Radon data from the ball's data.  On the cap `(0, 4/5)` they are the Radon profiles of the
even deviations `gammaDev n ρ`, `gammaPsi n ρ`.

This file is a self-contained copy (the same proof as
`Work.OddVolterra.Free.delta_cap_identity` together with the linearity lemma it needs), so that
consumers do not depend on the file in which that lemma currently lives.
-/

namespace Work.OddCurve.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddRadon in

lemma radonProfile_sub_free' {d : ℕ} {γ₁ γ₂ : ℝ → ℝ} {c : ℝ}
    (h₁ : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ₁ (c * s))
      volume (-1 : ℝ) 1)
    (h₂ : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ₂ (c * s))
      volume (-1 : ℝ) 1) :
    radonProfile d (γ₁ - γ₂) c = radonProfile d γ₁ c - radonProfile d γ₂ c := by
  simp only [radonProfile]
  rw [← mul_sub]
  congr 1
  rw [← intervalIntegral.integral_sub h₁ h₂]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [Pi.sub_apply]
  ring


theorem deltaCapIdentityClean (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) (4 / 5),
      Work.OddCurve.LowSlope.deltaA n ρ c
        = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaDev n ρ) c ∧
      Work.OddCurve.LowSlope.deltaB n ρ c
        = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaPsi n ρ) c := by
  intro c hc
  have hc4 : c < 4 / 5 := hc.2
  have hcc : |c| < 1 := by rw [abs_of_pos hc.1]; linarith
  have hGlueF : Work.OddCurve.LowSlope.GlueF n ρ c = Work.OddCurve.LowSlope.radonPhi n ρ c := by
    simp only [Work.OddCurve.LowSlope.GlueF]
    rw [abs_of_pos hc.1]
    exact Work.OddCurve.LowSlope.gluedPhi_of_lt hc.1.le hc4
  have hGlueG : Work.OddCurve.LowSlope.GlueG n ρ c = Work.OddCurve.LowSlope.radonPsi n ρ c := by
    simp only [Work.OddCurve.LowSlope.GlueG]
    rw [abs_of_pos hc.1]
    exact Work.OddCurve.LowSlope.gluedPsi_of_lt hc.1.le hc4
  -- continuity of the composed profiles on `[-1,1]`
  have hcontF : ContinuousOn (fun s : ℝ => (c * s) ^ 2 * ρ (c * s) ^ (2 * n + 2))
      (Set.uIcc (-1 : ℝ) 1) := by
    have hmap : Set.MapsTo (fun s : ℝ => c * s) (Set.uIcc (-1 : ℝ) 1) (Set.Ioo (-1 : ℝ) 1) := by
      intro s hs
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Icc] at hs
      have hsabs : |s| ≤ 1 := abs_le.mpr hs
      have h1 : |c * s| ≤ |c| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg c) hsabs
      exact abs_lt.mp (lt_of_le_of_lt h1 hcc)
    have hcomp := (hρ.continuousOn.comp (by fun_prop : ContinuousOn (fun s : ℝ => c * s) _) hmap)
    have h2 : ContinuousOn (fun s : ℝ => (c * s) ^ 2) (Set.uIcc (-1 : ℝ) 1) := by fun_prop
    exact h2.mul (hcomp.pow (2 * n + 2))
  have hcontG : ContinuousOn (fun s : ℝ => (c * s) ^ 2) (Set.uIcc (-1 : ℝ) 1) := by fun_prop
  have hcontFneg : ContinuousOn (fun s : ℝ => (-(c * s)) ^ 2 * ρ (-(c * s)) ^ (2 * n + 2))
      (Set.uIcc (-1 : ℝ) 1) := by
    have hmap : Set.MapsTo (fun s : ℝ => -(c * s)) (Set.uIcc (-1 : ℝ) 1) (Set.Ioo (-1 : ℝ) 1) := by
      intro s hs
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Icc] at hs
      have hsabs : |s| ≤ 1 := abs_le.mpr hs
      have h1 : |-(c * s)| ≤ |c| := by
        rw [abs_neg, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg c) hsabs
      exact abs_lt.mp (lt_of_le_of_lt h1 hcc)
    have hcomp := (hρ.continuousOn.comp (by fun_prop : ContinuousOn (fun s : ℝ => -(c * s)) _) hmap)
    have h2 : ContinuousOn (fun s : ℝ => (-(c * s)) ^ 2) (Set.uIcc (-1 : ℝ) 1) := by fun_prop
    exact h2.mul (hcomp.pow (2 * n + 2))
  have hcontGneg : ContinuousOn (fun s : ℝ => (-(c * s)) ^ 2) (Set.uIcc (-1 : ℝ) 1) := by fun_prop
  have hcontP : ContinuousOn (fun s : ℝ => (c * s) * ρ (c * s) ^ (2 * n + 1))
      (Set.uIcc (-1 : ℝ) 1) := by
    have hmap : Set.MapsTo (fun s : ℝ => c * s) (Set.uIcc (-1 : ℝ) 1) (Set.Ioo (-1 : ℝ) 1) := by
      intro s hs
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Icc] at hs
      have hsabs : |s| ≤ 1 := abs_le.mpr hs
      have h1 : |c * s| ≤ |c| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg c) hsabs
      exact abs_lt.mp (lt_of_le_of_lt h1 hcc)
    have hcomp := (hρ.continuousOn.comp (by fun_prop : ContinuousOn (fun s : ℝ => c * s) _) hmap)
    have h2 : ContinuousOn (fun s : ℝ => (c * s)) (Set.uIcc (-1 : ℝ) 1) := by fun_prop
    exact h2.mul (hcomp.pow (2 * n + 1))
  have hcontP' : ContinuousOn (fun s : ℝ => (-(c * s)) * ρ (-(c * s)) ^ (2 * n + 1))
      (Set.uIcc (-1 : ℝ) 1) := by
    have hmap : Set.MapsTo (fun s : ℝ => -(c * s)) (Set.uIcc (-1 : ℝ) 1) (Set.Ioo (-1 : ℝ) 1) := by
      intro s hs
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Icc] at hs
      have hsabs : |s| ≤ 1 := abs_le.mpr hs
      have h1 : |-(c * s)| ≤ |c| := by
        rw [abs_neg, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg c) hsabs
      exact abs_lt.mp (lt_of_le_of_lt h1 hcc)
    have hcomp := (hρ.continuousOn.comp (by fun_prop : ContinuousOn (fun s : ℝ => -(c * s)) _) hmap)
    have h2 : ContinuousOn (fun s : ℝ => (-(c * s))) (Set.uIcc (-1 : ℝ) 1) := by fun_prop
    exact h2.mul (hcomp.pow (2 * n + 1))
  constructor
  · have h1 := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hcontF
    have h2 := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hcontG
    have hsub := radonProfile_sub_free' (d := 2 * n + 1)
      (γ₁ := fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) (γ₂ := fun u : ℝ => u ^ 2) h1 h2
    rw [Work.OddCurve.LowSlope.deltaA_def, hGlueF]
    show Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) c
        - Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2) c
        = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaDev n ρ) c
    have hf := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn
      (hcontF.sub hcontG)
    have hg : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) *
        (((fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) - fun u : ℝ => u ^ 2) (-(c * s))))
        volume (-1 : ℝ) 1 :=
      Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn (hcontFneg.sub hcontGneg)
    rw [← hsub, Work.OddCurve.LowSlope.radonProfile_evenPart (2 * n + 1) hf hg]
    congr 1
    funext u
    simp only [Pi.sub_apply, Work.OddCurve.LowSlope.gammaDev]
    ring
  · have h1 := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hcontP
    have h2 := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hcontP'
    rw [Work.OddCurve.LowSlope.deltaB_def, hGlueG]
    show Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u * ρ u ^ (2 * n + 1)) c
        = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaPsi n ρ) c
    rw [Work.OddCurve.LowSlope.radonProfile_evenPart (2 * n + 1) h1 h2]
    congr 1
    funext u
    simp only [Work.OddCurve.LowSlope.gammaPsi]
    ring


end

end Work.OddCurve.Free
