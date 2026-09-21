import Mathlib
import Submission.Work.OddVolterra.Free.FreeSetup
import Submission.Work.OddCurve.LowSlope.GlueDataDefs
import Submission.Work.OddCurve.LowSlope.Datum
import Submission.Work.OddVolterra.Free.glueA_eq_inversion
import Submission.Work.OddCurve.LowSlope.anchorPhiData_eq_ballData
import Submission.Work.OddCurve.LowSlope.anchorPsiData_eq_zero
import Submission.Work.OddCurve.LowSlope.step3_anchor_data
import Submission.Work.OddCurve.LowSlope.gapKernel_derivs
import Submission.Work.OddVolterra.Free.glueDataContDiffOnIcc
import Submission.Work.OddVolterra.Free.fixedRangeAbelSmooth

set_option maxHeartbeats 2000000

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval


noncomputable section

/-!
# Smoothness and linear derivative bounds of the glued low-slope data

Placeholder docstring (full version at the bottom of the development).
-/

/-! ## 0. The junction window of the glued data -/

/-- **The junction of the anchor's Radon data, in the `c`-window of the glue.**
For `c ∈ (4/5 - 1/100, 4/5 + 1/100)` the anchor's two Radon data coincide with the ball's, so the
glued data `GlueF`, `GlueG` are `C^∞` at the junction. -/
theorem junctionWindow (n : ℕ) (hn : 1 ≤ n) {h X Y ρ : ℝ → ℝ}
    (hH : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0)
    (hρ : Work.OddVolterra.Free.IsAnchorRadial h X Y ρ) :
    ∀ c ∈ Set.Ioo (4 / 5 - 1 / 100 : ℝ) (4 / 5 + 1 / 100),
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n ρ c = 0 := by
  obtain ⟨hρpos, hρsm, hρmono, hgraph, hρ00⟩ := hρ
  have hρsm1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1) := hρsm.of_le (by simp)
  have htau : 1 - 3 * Work.OddVolterra.tau = 1 - 3 * Work.OddCurve.tau := by
    norm_num [Work.OddVolterra.tau, Work.OddCurve.tau]
  have hA' : ∀ s : ℝ, 1 - 3 * Work.OddCurve.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2) := by
    intro s hs hs1; exact hA s (by rw [htau]; exact hs) hs1
  have hB' : ∀ s : ℝ, 1 - 3 * Work.OddCurve.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0 := by
    intro s hs hs1; exact hB s (by rw [htau]; exact hs) hs1
  have hlow : (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ < 79 / 100 := by
    have := @Work.OddVolterra.Free.cStar_lt_79
    simpa [Work.OddCurve.LowSlope.cStar] using this
  have hhigh : (81 / 100 : ℝ) < (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹ := by
    have hpos : 0 < Real.sqrt (1 + (7 / 10 : ℝ) ^ 2) := Real.sqrt_pos.mpr (by norm_num)
    rw [show (Real.sqrt (1 + (7/10:ℝ) ^ 2))⁻¹ = 1 / Real.sqrt (1 + (7/10:ℝ) ^ 2) by ring,
      lt_div_iff₀ hpos]
    have hsq : Real.sqrt (1 + (7 / 10 : ℝ) ^ 2) ^ 2 = 1 + (7 / 10 : ℝ) ^ 2 :=
      Real.sq_sqrt (by norm_num)
    nlinarith [hsq]
  intro c hc
  refine Work.OddCurve.LowSlope.anchorData_junction_cap n hn hH hρpos hρsm1 hρmono hgraph
    hA' hB' ⟨?_, ?_⟩
  · linarith [hc.1, hlow]
  · linarith [hc.2, hhigh]

/-- **The junction of the anchor's Radon data on the cap `(cStar, 4/5)`.** -/
theorem junctionWindowCap (n : ℕ) (hn : 1 ≤ n) {h X Y ρ : ℝ → ℝ}
    (hH : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0)
    (hρ : Work.OddVolterra.Free.IsAnchorRadial h X Y ρ) :
    ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n ρ c = 0 := by
  obtain ⟨hρpos, hρsm, hρmono, hgraph, hρ00⟩ := hρ
  have hρsm1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1) := hρsm.of_le (by simp)
  have htau : 1 - 3 * Work.OddVolterra.tau = 1 - 3 * Work.OddCurve.tau := by
    norm_num [Work.OddVolterra.tau, Work.OddCurve.tau]
  have hA' : ∀ s : ℝ, 1 - 3 * Work.OddCurve.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2) := by
    intro s hs hs1; exact hA s (by rw [htau]; exact hs) hs1
  have hB' : ∀ s : ℝ, 1 - 3 * Work.OddCurve.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0 := by
    intro s hs hs1; exact hB s (by rw [htau]; exact hs) hs1
  have hhigh : (4 / 5 : ℝ) < (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹ := by
    have hpos : 0 < Real.sqrt (1 + (7 / 10 : ℝ) ^ 2) := Real.sqrt_pos.mpr (by norm_num)
    rw [show (Real.sqrt (1 + (7/10:ℝ) ^ 2))⁻¹ = 1 / Real.sqrt (1 + (7/10:ℝ) ^ 2) by ring,
      lt_div_iff₀ hpos]
    have hsq : Real.sqrt (1 + (7 / 10 : ℝ) ^ 2) ^ 2 = 1 + (7 / 10 : ℝ) ^ 2 :=
      Real.sq_sqrt (by norm_num)
    nlinarith [hsq]
  intro c hc
  refine Work.OddCurve.LowSlope.anchorData_junction_cap n hn hH hρpos hρsm1 hρmono hgraph
    hA' hB' ⟨?_, ?_⟩
  · simpa [Work.OddCurve.LowSlope.cStar] using hc.1
  · linarith [hc.2, hhigh]

/-! ## 1. The cap identities for the glued deviations -/

open Work.OddRadon in
/-- Linearity of `radonProfile` in the profile (difference form). -/
lemma radonProfile_sub_free {d : ℕ} {γ₁ γ₂ : ℝ → ℝ} {c : ℝ}
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

/-- **The composite profile is continuous on `[-1,1]`**: for `|c| < 1` and `γ` continuous on
`(-1,1)`, the function `s ↦ γ (c * s)` is continuous on `[-1,1]`. -/
lemma continuousOn_comp_mul_of_lt_one {γ : ℝ → ℝ} {c : ℝ} (hc : |c| < 1)
    (hγ : ContinuousOn γ (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (fun s : ℝ => γ (c * s)) (Set.uIcc (-1 : ℝ) 1) := by
  refine hγ.comp (by fun_prop) ?_
  intro s hs
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Icc] at hs
  have hsabs : |s| ≤ 1 := abs_le.mpr hs
  have h1 : |c * s| ≤ |c| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg c) hsabs
  exact abs_lt.mp (lt_of_le_of_lt h1 hc)

open Work.OddCurve.LowSlope in
/-- **The glued deviation data on the cap are the Radon profiles of `gammaDev`, `gammaPsi`.** -/
theorem delta_cap_identity (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
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
    have hsub := radonProfile_sub_free (d := 2 * n + 1)
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

end Work.OddVolterra.Free
namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## 2. The inversion of a gap datum is bounded on `[4/5,1]` -/

/-- **The Abel inversion of a datum supported below `a₀` is a fixed-range integral.** -/
lemma abelIntegral_eq_supported_form {a₀ v : ℝ} (ha₀ : 0 < a₀) (hav : a₀ < v) {G : ℝ → ℝ}
    (hG : ∀ c : ℝ, a₀ < c → G c = 0) :
    (∫ c in (0 : ℝ)..v, c * G c / Real.sqrt (v ^ 2 - c ^ 2))
      = ∫ c in (0 : ℝ)..a₀, c * G c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) := by
  have hsub : Set.Ioc (0 : ℝ) a₀ ⊆ Set.Ioc (0 : ℝ) v :=
    fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 hav)⟩
  have hzero : ∀ x ∈ Set.Ioc (0 : ℝ) v \ Set.Ioc (0 : ℝ) a₀,
      x * G x / Real.sqrt (v ^ 2 - x ^ 2) = 0 := by
    intro x hx
    obtain ⟨⟨hx1, hx2⟩, hxnot⟩ := hx
    have hxgt : a₀ < x := by
      by_contra hle
      exact hxnot ⟨hx1, le_of_not_gt hle⟩
    rw [hG x hxgt]
    ring
  have hv0 : (0 : ℝ) < v := lt_trans ha₀ hav
  have h1 : (∫ x in Set.Ioc (0 : ℝ) v, x * G x / Real.sqrt (v ^ 2 - x ^ 2))
      = ∫ x in Set.Ioc (0 : ℝ) a₀, x * G x / Real.sqrt (v ^ 2 - x ^ 2) :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub hzero
  have h2 : (∫ x in Set.Ioc (0 : ℝ) a₀, x * G x / Real.sqrt (v ^ 2 - x ^ 2))
      = ∫ x in Set.Ioc (0 : ℝ) a₀, x * G x * (v ^ 2 - x ^ 2) ^ (-(1 / 2 : ℝ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    have hxpos : 0 < v ^ 2 - x ^ 2 := by
      have h1 : x ≤ a₀ := hx.2
      nlinarith [hav, ha₀, hx.1]
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hxpos.le, div_eq_mul_inv, mul_assoc]
  rw [intervalIntegral.integral_of_le hv0.le, intervalIntegral.integral_of_le ha₀.le, h1, h2]

/-- **The inversion of a gap datum is bounded, and differentiable, on `[4/5,1]`.**

Let `γ` be continuous on `[0,a₀]` with `γ 0 = 0` and `|γ| ≤ M` on `(0,a₀)`, and let `δ` be the
`(2n+1)`-dimensional Radon datum of `γ` on `(0,a₀)` (`δ = radonProfile (2n+1) γ` there) and `0`
above `a₀`.  Then on `[4/5,1]` the Abel inversion of `δ` and its first derivative are bounded by
`C M` and the inversion is differentiable.  The point is that `a₀ ≤ cStar < 4/5`, so that the
kernel of the inversion is bounded away from its singularity on the support of the datum. -/
theorem radonInverse_gap_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ δ : ℝ → ℝ) (a₀ M : ℝ),
      0 < a₀ → a₀ ≤ Work.OddCurve.LowSlope.cStar → 0 ≤ M →
      Function.Even γ → ContinuousOn γ (Set.Icc 0 a₀) → γ 0 = 0 →
      (∀ c ∈ Set.Ioo (0 : ℝ) (79 / 100), |γ c| ≤ M) →
      (∀ c : ℝ, a₀ < c → δ c = 0) →
      (∀ c ∈ Set.Ioo (0 : ℝ) a₀, δ c = Work.OddRadon.radonProfile (2 * n + 1) γ c) →
      ∀ u ∈ Set.Icc (4 / 5 : ℝ) 1,
        |Work.OddRadon.radonInverse n δ u| ≤ C * M ∧
        |deriv (fun v : ℝ => Work.OddRadon.radonInverse n δ v) u| ≤ C * M ∧
        DifferentiableAt ℝ (Work.OddRadon.radonInverse n δ) u := by
  refine ⟨10 ^ 5, by norm_num, ?_⟩
  intro γ δ a₀ M ha₀ ha₀c hM hγeven hγC hγ0 hγb hδz hδr u hu
  -- ### 0. numerics
  have hcStar79 : Work.OddCurve.LowSlope.cStar < 79 / 100 := Work.OddVolterra.Free.cStar_lt_79
  have hcStar45 : Work.OddCurve.LowSlope.cStar < 4 / 5 :=
    Work.OddCurve.LowSlope.cStar_lt_four_fifths
  have ha79 : a₀ < 79 / 100 := lt_of_le_of_lt ha₀c hcStar79
  have ha45 : a₀ < 4 / 5 := lt_of_le_of_lt ha₀c hcStar45
  have hau : a₀ < u := lt_of_lt_of_le ha45 hu.1
  have hu0 : (0 : ℝ) < u := by linarith [hu.1]
  have hu11 : u < 11 / 10 := by linarith [hu.2]
  -- ### 1. the reduced datum and the trigonometric weight
  set Th : ℝ → ℝ := fun c => Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
      (Work.OddRadon.abelDatum n δ) c with hThdef
  set Θ : ℝ → ℝ := fun c => Work.OddRadon.abelTrans (-(1 / 2)) γ c with hΘdef
  have hTh_zero : ∀ c : ℝ, a₀ < c → Th c = 0 := by
    intro c hc
    have habel : Set.EqOn (Work.OddRadon.abelDatum n δ) 0 (Set.Ioi a₀) := by
      intro x hx
      simp only [Pi.zero_apply, Work.OddRadon.abelDatum]
      rw [hδz x hx]
      ring
    have h := Work.OddRadon.abelReduceIter_congr_open isOpen_Ioi (n - 1) ((n : ℝ) - 3 / 2) habel
    show Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
      (Work.OddRadon.abelDatum n δ) c = 0
    rw [h hc, Work.OddVolterra.Free.abelReduceIter_zero]
    rfl
  have hk : (((n - 1 : ℕ)) : ℝ) - 1 < (n : ℝ) - 3 / 2 := by
    rw [Nat.cast_sub hn]; push_cast; linarith
  have hexp : ((n : ℝ) - 3 / 2) - (((n - 1 : ℕ)) : ℝ) = -(1 / 2) := by
    rw [Nat.cast_sub hn]; ring
  have hTh_eq : ∀ c ∈ Set.Ioo (0 : ℝ) a₀, Th c = Θ c := by
    intro c hc
    have habel : Set.EqOn (Work.OddRadon.abelDatum n δ)
        (Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) γ) (Set.Ioo (0 : ℝ) a₀) := by
      intro x hx
      simp only [Work.OddRadon.abelDatum]
      rw [hδr x hx, Work.OddRadon.radonProfile_eq_abelTrans' n hn hγeven hx.1]
      have hS : (2 * Work.OddRadon.sphereArea (2 * n - 2)) ≠ 0 :=
        mul_ne_zero (by norm_num) (ne_of_gt (Work.OddRadon.sphereArea_pos _))
      have hx0 : x ^ (2 * n - 2) ≠ 0 := pow_ne_zero _ (ne_of_gt hx.1)
      rw [show (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * x ^ (2 * n - 2) *
            (2 * Work.OddRadon.sphereArea (2 * n - 2) * (x ^ (2 * n - 2))⁻¹ *
              Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) γ x)
          = ((2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ *
              (2 * Work.OddRadon.sphereArea (2 * n - 2))) *
            (x ^ (2 * n - 2) * (x ^ (2 * n - 2))⁻¹) *
              Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) γ x by ring,
        inv_mul_cancel₀ hS, mul_inv_cancel₀ hx0]
      ring
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hγC
    have hrec := Work.OddVolterra.Free.abelReduceIter_abelTrans_local (β := (n : ℝ) - 3 / 2)
      (a₀ := a₀) (γ := γ) ha₀
      (hγC.mono (by intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
      ⟨M, fun s hs => by simpa [Real.norm_eq_abs] using hM s ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩
      (k := n - 1) hk
    have hcongr := Work.OddRadon.abelReduceIter_congr_open isOpen_Ioo (n - 1)
      ((n : ℝ) - 3 / 2) habel
    change Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
      (Work.OddRadon.abelDatum n δ) c = Θ c
    rw [hcongr hc, hrec hc, hexp, hΘdef]
  -- ### 2. bounds and continuity of the weight
  have hΘ_bound_open : ∀ c ∈ Set.Ioo (0 : ℝ) a₀, |Θ c| ≤ 2 * M := by
    intro c hc
    change |Work.OddRadon.abelTrans (-(1 / 2)) γ c| ≤ 2 * M
    exact Work.OddVolterra.Free.abelTrans_neg_half_bound hM (by norm_num : (0:ℝ) < 79/100)
      hc.1 (lt_trans hc.2 ha79) hγb
  have hΘ_cont : ContinuousOn Θ (Set.Icc 0 a₀) := by
    have h := Work.OddVolterra.Free.continuousOn_abelTrans_negHalf ha₀ hγC hγ0
    simpa [hΘdef] using h
  have hΘ_zero : Θ 0 = 0 := by
    change Work.OddRadon.abelTrans (-(1 / 2)) γ 0 = 0
    exact Work.OddRadon.abelTrans_zero _ _
  have hΘ_Icc : ∀ c ∈ Set.Icc 0 a₀, |Θ c| ≤ 2 * M := by
    intro c hc
    rcases eq_or_lt_of_le hc.1 with h | h
    · rw [← h, hΘ_zero, abs_zero]; linarith
    · have hc' : c < 79 / 100 := lt_of_le_of_lt hc.2 ha79
      change |Work.OddRadon.abelTrans (-(1 / 2)) γ c| ≤ 2 * M
      exact Work.OddVolterra.Free.abelTrans_neg_half_bound hM (by norm_num : (0:ℝ) < 79/100)
        h hc' hγb
  -- ### 3. the fixed-range Abel integral and its derivatives
  set J : ℝ → ℝ := fun v => ∫ c in (0 : ℝ)..a₀, c * Θ c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ))
    with hJdef
  set J1 : ℝ → ℝ := fun v => ∫ c in (0 : ℝ)..a₀, c * Θ c * (-v * (v ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ)))
    with hJ1def
  set J2 : ℝ → ℝ := fun v => ∫ c in (0 : ℝ)..a₀,
    c * Θ c * ((2 * v ^ 2 + c ^ 2) * (v ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ))) with hJ2def
  obtain ⟨hJd1, hJd2, -⟩ := Work.OddCurve.LowSlope.gapKernel_derivs (m := 0) (M' := a₀) (B := 2 * M)
    le_rfl ha₀.le ha79 hΘ_cont hΘ_Icc u ⟨by linarith [hu.1], hu11⟩
  have hd1 : HasDerivAt J (J1 u) u := by simpa [hJdef, hJ1def] using hJd1
  have hd2 : HasDerivAt J1 (J2 u) u := by simpa [hJ1def, hJ2def] using hJd2
  -- ### 4. the inversion is the derivative of the fixed-range integral
  set P : ℝ → ℝ := fun v => ∫ c in (0 : ℝ)..v, c * Th c / Real.sqrt (v ^ 2 - c ^ 2) with hPdef
  have hPJ : P =ᶠ[𝓝 u] J := by
    filter_upwards [isOpen_Ioi.mem_nhds hau] with v hv
    have h1 : P v = ∫ c in (0 : ℝ)..a₀, c * Th c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) := by
      rw [hPdef]
      exact abelIntegral_eq_supported_form (a₀ := a₀) (v := v) ha₀ hv
        (fun c hc => hTh_zero c hc)
    have h2 : (∫ c in (0 : ℝ)..a₀, c * Th c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)))
        = ∫ c in (0 : ℝ)..a₀, c * Θ c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne (volume : Measure ℝ) a₀] with c hcne hc
      rw [Set.uIoc_of_le ha₀.le] at hc
      have hclt : c < a₀ := lt_of_le_of_ne hc.2 hcne
      rw [hTh_eq c ⟨hc.1, hclt⟩]
    rw [h1, h2, hJdef]
  have hrad : ∀ v : ℝ, Work.OddRadon.radonInverse n δ v = (2 / Real.pi) * deriv P v := by
    intro v
    rw [Work.OddRadon.radonInverse_eq, ← hPdef]
  have hderivP : deriv P u = J1 u := by
    rw [hPJ.deriv_eq, hd1.deriv]
  have hderivJ : deriv J =ᶠ[𝓝 u] J1 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show u ∈ Set.Ioo (79 / 100 : ℝ) (11 / 10) from
      ⟨by linarith [hu.1], hu11⟩)] with v hv
    have h := Work.OddCurve.LowSlope.gapKernel_derivs (m := 0) (M' := a₀) (B := 2 * M)
      le_rfl ha₀.le ha79 hΘ_cont hΘ_Icc v hv
    simpa [hJdef, hJ1def] using h.1.deriv
  have hderiv2 : deriv (deriv P) u = J2 u := by
    have e1 : deriv P =ᶠ[𝓝 u] deriv J := hPJ.deriv
    rw [e1.deriv_eq, hderivJ.deriv_eq, hd2.deriv]
  -- ### 5. kernel bounds on the support
  have hbase : ∀ c ∈ Set.Icc (0 : ℝ) a₀, (31 / 1025 : ℝ) ≤ u ^ 2 - c ^ 2 := by
    intro c hc
    have hu45 : (4 / 5 : ℝ) ^ 2 ≤ u ^ 2 := by nlinarith [hu.1]
    have hc2 : c ^ 2 ≤ a₀ ^ 2 := by nlinarith [hc.1, hc.2, ha₀.le]
    have ha2 : a₀ ^ 2 ≤ Work.OddCurve.LowSlope.cStar ^ 2 := by
      nlinarith [ha₀c, ha₀.le, Work.OddCurve.LowSlope.cStar_pos]
    nlinarith [hu45, hc2, ha2, Work.OddVolterra.Free.four_fifths_sq_sub_cStar_sq]
  have hbase_pos : ∀ c ∈ Set.Icc (0 : ℝ) a₀, 0 < u ^ 2 - c ^ 2 := fun c hc => by
    linarith [hbase c hc]
  have hker3 : ∀ c ∈ Set.Icc (0 : ℝ) a₀, (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ)) ≤ 6 ^ 3 := by
    intro c hc
    have hpos := hbase_pos c hc
    have h1 : (u ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) ≤ 6 :=
      le_trans (Real.rpow_le_rpow_of_nonpos (by norm_num) (hbase c hc) (by norm_num))
        Work.OddVolterra.Free.cStarThm
    have h3 : (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ)) = ((u ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ))) ^ 3 := by
      rw [show (-(3 / 2) : ℝ) = (-(1 / 2)) * 3 by norm_num, Real.rpow_mul hpos.le]
      simp
    rw [h3]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) h1 3
  have hker5 : ∀ c ∈ Set.Icc (0 : ℝ) a₀, (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ)) ≤ 6 ^ 5 := by
    intro c hc
    have hpos := hbase_pos c hc
    have h1 : (u ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) ≤ 6 :=
      le_trans (Real.rpow_le_rpow_of_nonpos (by norm_num) (hbase c hc) (by norm_num))
        Work.OddVolterra.Free.cStarThm
    have h3 : (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ)) = ((u ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ))) ^ 5 := by
      rw [show (-(5 / 2) : ℝ) = (-(1 / 2)) * 5 by norm_num, Real.rpow_mul hpos.le]
      simp
    rw [h3]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) h1 5
  -- ### 6. the bounds on `radonInverse` and its derivative
  have hJ1bd : |J1 u| ≤ 2000 * M := by
    have hpt : ∀ c ∈ Set.Icc (0 : ℝ) a₀,
        |c * Θ c * (-u * (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ)))| ≤ 2000 * M := by
      intro c hc
      have hΘc := hΘ_Icc c hc
      have h1 : |c * Θ c| ≤ 1 * (2 * M) := by
        rw [abs_mul, abs_of_nonneg hc.1]
        exact mul_le_mul (by linarith [hc.2, ha45] : c ≤ 1) hΘc (abs_nonneg _) (by linarith)
      have hk0 : 0 ≤ (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_nonneg (le_of_lt (hbase_pos c hc)) _
      have h2 : |(-u) * (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ))| ≤ 1 * 6 ^ 3 := by
        rw [abs_mul, abs_neg, abs_of_nonneg hu0.le, abs_of_nonneg hk0]
        exact mul_le_mul hu.2 (hker3 c hc) hk0 (by norm_num)
      rw [abs_mul]
      calc |c * Θ c| * |(-u) * (u ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ))|
          ≤ (1 * (2 * M)) * (1 * 6 ^ 3) := mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
        _ ≤ 2000 * M := by nlinarith [hM]
    have h := abs_integral_le_of_pointwise ha₀.le hpt
    simp only [sub_zero] at h
    refine h.trans ?_
    nlinarith [hM, ha45]
  have hJ2bd : |J2 u| ≤ 10 ^ 5 * M := by
    have hpt : ∀ c ∈ Set.Icc (0 : ℝ) a₀,
        |c * Θ c * ((2 * u ^ 2 + c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ)))| ≤ 10 ^ 5 * M := by
      intro c hc
      have hΘc := hΘ_Icc c hc
      have h1 : |c * Θ c| ≤ 1 * (2 * M) := by
        rw [abs_mul, abs_of_nonneg hc.1]
        exact mul_le_mul (by linarith [hc.2, ha45] : c ≤ 1) hΘc (abs_nonneg _) (by linarith)
      have hk0 : 0 ≤ (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_nonneg (le_of_lt (hbase_pos c hc)) _
      have h2 : |(2 * u ^ 2 + c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ))| ≤ 3 * 6 ^ 5 := by
        have hpoly : |2 * u ^ 2 + c ^ 2| ≤ 3 := by
          rw [abs_of_nonneg (by positivity)]
          nlinarith [hu.2, hc.2, ha45, hc.1]
        rw [abs_mul, abs_of_nonneg hk0]
        exact mul_le_mul hpoly (hker5 c hc) hk0 (by norm_num)
      rw [abs_mul]
      calc |c * Θ c| * |(2 * u ^ 2 + c ^ 2) * (u ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ))|
          ≤ (1 * (2 * M)) * (3 * 6 ^ 5) := mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
        _ ≤ 10 ^ 5 * M := by nlinarith [hM]
    have h := abs_integral_le_of_pointwise ha₀.le hpt
    simp only [sub_zero] at h
    refine h.trans ?_
    nlinarith [hM, ha45]
  -- ### 7. conclusion
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : (2 / Real.pi) ≤ 1 := by
    rw [div_le_one hpi]
    linarith [Real.pi_gt_three]
  have hnn : 0 ≤ (2 / Real.pi) := by positivity
  have h2abs : |2 / Real.pi| ≤ 1 := by rw [abs_of_nonneg hnn]; exact h2pi
  have hInv : Work.OddRadon.radonInverse n δ u = (2 / Real.pi) * J1 u := by
    rw [hrad u, hderivP]
  have hfun : (fun v : ℝ => Work.OddRadon.radonInverse n δ v)
      = fun v : ℝ => (2 / Real.pi) * deriv P v := by
    funext v; exact hrad v
  have hdiffF : DifferentiableAt ℝ (deriv P) u := by
    have hev : deriv P =ᶠ[𝓝 u] J1 := hPJ.deriv.trans hderivJ
    exact (hd2.differentiableAt).congr_of_eventuallyEq hev
  refine ⟨?_, ?_, ?_⟩
  · rw [hInv, abs_mul]
    calc |2 / Real.pi| * |J1 u| ≤ 1 * |J1 u| :=
          mul_le_mul_of_nonneg_right h2abs (abs_nonneg _)
      _ ≤ 1 * (2000 * M) := mul_le_mul_of_nonneg_left hJ1bd zero_le_one
      _ ≤ 10 ^ 5 * M := by nlinarith [hM]
  · have hderiv : deriv (Work.OddRadon.radonInverse n δ) u = (2 / Real.pi) * J2 u := by
      have e : Work.OddRadon.radonInverse n δ = fun v : ℝ => (2 / Real.pi) * deriv P v := by
        funext v; exact hrad v
      rw [e, deriv_const_mul_uncond, hderiv2]
    rw [hderiv, abs_mul]
    calc |2 / Real.pi| * |J2 u| ≤ 1 * |J2 u| :=
          mul_le_mul_of_nonneg_right h2abs (abs_nonneg _)
      _ ≤ 1 * (10 ^ 5 * M) := mul_le_mul_of_nonneg_left hJ2bd zero_le_one
      _ ≤ 10 ^ 5 * M := by nlinarith [hM]
  · have h' : DifferentiableAt ℝ (fun v : ℝ => (2 / Real.pi) * deriv P v) u :=
      hdiffF.const_mul (2 / Real.pi)
    refine h'.congr_of_eventuallyEq ?_
    filter_upwards with v
    exact (hrad v).symm


/-! ## 3. The anchor combination: smoothness and derivative -/

/-- The anchor's power combination `v ↦ ρ v ^ m + ρ (-v) ^ m - 2` is `C^∞` on `(-1,1)`. -/
lemma contDiffOn_anchorCombo (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : ℝ => ρ v ^ m + ρ (-v) ^ m - 2) (Set.Ioo (-1 : ℝ) 1) := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => ρ v ^ m)
      (Set.Ioo (-1 : ℝ) 1) := hρ.pow m
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => ρ (-v) ^ m)
      (Set.Ioo (-1 : ℝ) 1) :=
    (hρ.comp (by fun_prop : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => -v)
      (Set.Ioo (-1 : ℝ) 1)) (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)).pow m
  exact (h1.add h2).sub contDiffOn_const

/-- The derivative of the anchor's power combination. -/
lemma deriv_anchorCombo (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) {u : ℝ}
    (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (fun v : ℝ => ρ v ^ m + ρ (-v) ^ m - 2) u
      = m * (ρ u ^ (m - 1) * deriv ρ u - ρ (-u) ^ (m - 1) * deriv ρ (-u)) := by
  have hu' : -u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hdu : DifferentiableAt ℝ ρ u :=
    (hρ.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hu)
  have hdu' : DifferentiableAt ℝ ρ (-u) :=
    (hρ.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hu')
  have hnegdiff : DifferentiableAt ℝ (fun v : ℝ => -v) u := differentiableAt_id.neg
  have hnegd : deriv (fun v : ℝ => -v) u = -1 := by
    simpa using (hasDerivAt_neg u).deriv
  have hB : deriv (fun v : ℝ => ρ (-v) ^ m) u
      = m * ρ (-u) ^ (m - 1) * deriv ρ (-u) * (-1) := by
    have hcomp := deriv_comp (x := u) (h := fun v : ℝ => -v) (h₂ := fun w : ℝ => ρ w ^ m)
      (hdu'.pow m) hnegdiff
    rw [show (fun v : ℝ => ρ (-v) ^ m)
        = ((fun w : ℝ => ρ w ^ m) ∘ (fun v : ℝ => -v)) from rfl, hcomp,
      deriv_fun_pow hdu' m, hnegd]
    try ring
  have hA : deriv (fun v : ℝ => ρ v ^ m) u = m * ρ u ^ (m - 1) * deriv ρ u :=
    deriv_fun_pow hdu m
  have hAdiff : DifferentiableAt ℝ (fun v : ℝ => ρ v ^ m) u := hdu.pow m
  have hBdiff : DifferentiableAt ℝ (fun v : ℝ => ρ (-v) ^ m) u :=
    (hdu'.comp u hnegdiff).pow m
  change deriv (((fun v : ℝ => ρ v ^ m) + (fun v : ℝ => ρ (-v) ^ m)) - (fun _ : ℝ => (2 : ℝ))) u
      = m * (ρ u ^ (m - 1) * deriv ρ u - ρ (-u) ^ (m - 1) * deriv ρ (-u))
  rw [deriv_sub (hAdiff.add hBdiff) (differentiableAt_const 2), deriv_add hAdiff hBdiff,
    deriv_const, hA, hB]
  try ring


/-- The derivative of the difference of the two odd power combinations. -/
lemma deriv_anchorDiff (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) {u : ℝ}
    (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (fun v : ℝ => ρ v ^ m - ρ (-v) ^ m) u
      = m * (ρ u ^ (m - 1) * deriv ρ u + ρ (-u) ^ (m - 1) * deriv ρ (-u)) := by
  have hu' : -u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hdu : DifferentiableAt ℝ ρ u :=
    (hρ.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hu)
  have hdu' : DifferentiableAt ℝ ρ (-u) :=
    (hρ.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hu')
  have hnegdiff : DifferentiableAt ℝ (fun v : ℝ => -v) u := differentiableAt_id.neg
  have hnegd : deriv (fun v : ℝ => -v) u = -1 := by
    simpa using (hasDerivAt_neg u).deriv
  have hB : deriv (fun v : ℝ => ρ (-v) ^ m) u
      = m * ρ (-u) ^ (m - 1) * deriv ρ (-u) * (-1) := by
    have hcomp := deriv_comp (x := u) (h := fun v : ℝ => -v) (h₂ := fun w : ℝ => ρ w ^ m)
      (hdu'.pow m) hnegdiff
    rw [show (fun v : ℝ => ρ (-v) ^ m)
        = ((fun w : ℝ => ρ w ^ m) ∘ (fun v : ℝ => -v)) from rfl, hcomp,
      deriv_fun_pow hdu' m, hnegd]
    try ring
  have hA : deriv (fun v : ℝ => ρ v ^ m) u = m * ρ u ^ (m - 1) * deriv ρ u :=
    deriv_fun_pow hdu m
  have hAdiff : DifferentiableAt ℝ (fun v : ℝ => ρ v ^ m) u := hdu.pow m
  have hBdiff : DifferentiableAt ℝ (fun v : ℝ => ρ (-v) ^ m) u :=
    (hdu'.comp u hnegdiff).pow m
  change deriv ((fun v : ℝ => ρ v ^ m) - (fun v : ℝ => ρ (-v) ^ m)) u
      = m * (ρ u ^ (m - 1) * deriv ρ u + ρ (-u) ^ (m - 1) * deriv ρ (-u))
  rw [deriv_sub hAdiff hBdiff, hA, hB]
  try ring

/-- The difference of the two odd power combinations is `C^∞` on `(-1,1)`. -/
lemma contDiffOn_anchorDiff (m : ℕ) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : ℝ => ρ v ^ m - ρ (-v) ^ m) (Set.Ioo (-1 : ℝ) 1) := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => ρ v ^ m)
      (Set.Ioo (-1 : ℝ) 1) := hρ.pow m
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => ρ (-v) ^ m)
      (Set.Ioo (-1 : ℝ) 1) :=
    (hρ.comp (by fun_prop : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => -v)
      (Set.Ioo (-1 : ℝ) 1)) (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)).pow m
  exact h1.sub h2

/-! ## 4. The two-power quotients: derivative formulas -/

/-- Derivative of `v ↦ 2 R v / v ^ 2` away from `0`. -/
lemma deriv_two_mul_div_sq {R : ℝ → ℝ} {u : ℝ} (hu : u ≠ 0)
    (hR : DifferentiableAt ℝ R u) :
    deriv (fun v : ℝ => 2 * R v / v ^ 2) u = 2 * deriv R u / u ^ 2 - 4 * R u / u ^ 3 := by
  have hnum : DifferentiableAt ℝ (fun v : ℝ => 2 * R v) u := (differentiableAt_const 2).mul hR
  have hden : DifferentiableAt ℝ (fun v : ℝ => v ^ 2) u := differentiableAt_id.pow 2
  have hne : (u : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hu3 : (u : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hu
  have hfun : (fun v : ℝ => 2 * R v / v ^ 2) = (fun v : ℝ => 2 * R v) / (fun v : ℝ => v ^ 2) := rfl
  rw [hfun, deriv_div hnum hden hne, deriv_const_mul 2 hR,
    deriv_fun_pow (f := fun v : ℝ => v) differentiableAt_id 2]
  simp only [deriv_id'']
  field_simp
  try ring

/-- Derivative of `v ↦ 2 R v / v` away from `0`. -/
lemma deriv_two_mul_div {R : ℝ → ℝ} {u : ℝ} (hu : u ≠ 0)
    (hR : DifferentiableAt ℝ R u) :
    deriv (fun v : ℝ => 2 * R v / v) u = 2 * deriv R u / u - 2 * R u / u ^ 2 := by
  have hnum : DifferentiableAt ℝ (fun v : ℝ => 2 * R v) u := (differentiableAt_const 2).mul hR
  have hden : DifferentiableAt ℝ (fun v : ℝ => v) u := differentiableAt_id
  have hu2 : (u : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hfun : (fun v : ℝ => 2 * R v / v) = (fun v : ℝ => 2 * R v) / (fun v : ℝ => v) := rfl
  rw [hfun, deriv_div hnum hden hu, deriv_const_mul 2 hR]
  simp only [deriv_id'']
  field_simp
  try ring


/-! ## 5. The two-power identities of the glued data -/

/-- **The glued first datum is the inverse of `deltaA`**, whenever `cos α ∈ (0,1)` is not the
junction. -/
lemma glueA_eq_deltaA (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) {α : ℝ}
    (hc0 : 0 < Real.cos α) (hc : Real.cos α ≠ 4 / 5) :
    Work.OddCurve.LowSlope.glueA n ρ α
      = 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) (Real.cos α)
          / Real.cos α ^ 2 := by
  exact Work.OddVolterra.Free.glueA_eq_inversion n hn hρ α hc0 hc

/-- **The glued second datum is the inverse of `deltaB` divided by `cos α`** (for `cos α > 0`). -/
lemma glueB_eq_deltaB (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) {α : ℝ}
    (hc0 : 0 < Real.cos α) :
    Work.OddCurve.LowSlope.glueB n ρ α
      = 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ) (Real.cos α)
          / Real.cos α := by
  by_cases hlt : Real.cos α < 4 / 5
  · have h1 : Work.OddCurve.LowSlope.glueB n ρ α
        = ρ (Real.cos α) ^ (2 * n + 1) - ρ (-(Real.cos α)) ^ (2 * n + 1) :=
      Work.OddCurve.LowSlope.glueB_of_lt hlt
    have h2 : Work.OddRadon.radonInverse n
        (Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u * ρ u ^ (2 * n + 1)))
        (Real.cos α) = Real.cos α / 2 * (ρ (Real.cos α) ^ (2 * n + 1)
          - ρ (-(Real.cos α)) ^ (2 * n + 1)) :=
      Work.OddRadon.radonInverse_radonPsi_local n hn (c₁ := 4 / 5) (by norm_num) hρ hc0 hlt
    have h3 : Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ) (Real.cos α)
        = Real.cos α / 2 * (ρ (Real.cos α) ^ (2 * n + 1)
          - ρ (-(Real.cos α)) ^ (2 * n + 1)) := by
      have h3a : Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueG n ρ) (Real.cos α)
          = Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.radonPsi n ρ) (Real.cos α) :=
        Work.OddCurve.LowSlope.radonInverse_GlueG_eq n hc0 hlt
      have h3b : Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.radonPsi n ρ) (Real.cos α)
          = Real.cos α / 2 * (ρ (Real.cos α) ^ (2 * n + 1)
            - ρ (-(Real.cos α)) ^ (2 * n + 1)) :=
        Work.OddRadon.radonInverse_radonPsi_local n hn (c₁ := 4 / 5) (by norm_num) hρ hc0 hlt
      exact h3a.trans h3b
    rw [h1, h3]
    field_simp
  · have hge : 4 / 5 ≤ Real.cos α := le_of_not_gt hlt
    rw [Work.OddCurve.LowSlope.glueB_of_ge hge]
    show Work.OddCurve.LowSlope.GluePsi n ρ α / Real.cos α
        = 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueG n ρ) (Real.cos α)
            / Real.cos α
    rw [Work.OddCurve.LowSlope.GluePsi]



/-! ## 6b. The inversion of a gap datum is `C^∞` above the gap -/

/-- **The inversion of a datum supported below `a₀` and equal to `radonProfile γ` there is `C^∞`
above `a₀`.** -/
theorem radonInverse_gap_smooth (n : ℕ) (hn : 1 ≤ n) {γ δ : ℝ → ℝ} {a₀ : ℝ}
    (ha₀ : 0 < a₀) (hγeven : Function.Even γ) (hγC : ContinuousOn γ (Set.Icc 0 a₀))
    (hγ0 : γ 0 = 0)
    (hδz : ∀ c : ℝ, a₀ < c → δ c = 0)
    (hδr : ∀ c ∈ Set.Ioo (0 : ℝ) a₀, δ c = Work.OddRadon.radonProfile (2 * n + 1) γ c) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : ℝ => Work.OddRadon.radonInverse n δ v) (Set.Ioi a₀) := by
  set Θ : ℝ → ℝ := fun c => Work.OddRadon.abelTrans (-(1 / 2)) γ c with hΘdef
  set Th : ℝ → ℝ := fun c => Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
      (Work.OddRadon.abelDatum n δ) c with hThdef
  have hΘc : ContinuousOn Θ (Set.Icc 0 a₀) := by
    have h := Work.OddVolterra.Free.continuousOn_abelTrans_negHalf ha₀ hγC hγ0
    simpa [hΘdef] using h
  have hk : (((n - 1 : ℕ)) : ℝ) - 1 < (n : ℝ) - 3 / 2 := by
    rw [Nat.cast_sub hn]; push_cast; linarith
  have hexp : ((n : ℝ) - 3 / 2) - (((n - 1 : ℕ)) : ℝ) = -(1 / 2) := by
    rw [Nat.cast_sub hn]; ring
  have hΘTh : ∀ c ∈ Set.Ioo (0 : ℝ) a₀, Th c = Θ c := by
    intro c hc
    have habel : Set.EqOn (Work.OddRadon.abelDatum n δ)
        (Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) γ) (Set.Ioo (0 : ℝ) a₀) := by
      intro x hx
      simp only [Work.OddRadon.abelDatum]
      rw [hδr x hx, Work.OddRadon.radonProfile_eq_abelTrans' n hn hγeven hx.1]
      have hS : (2 * Work.OddRadon.sphereArea (2 * n - 2)) ≠ 0 :=
        mul_ne_zero (by norm_num) (ne_of_gt (Work.OddRadon.sphereArea_pos _))
      have hx0 : x ^ (2 * n - 2) ≠ 0 := pow_ne_zero _ (ne_of_gt hx.1)
      rw [show (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * x ^ (2 * n - 2) *
            (2 * Work.OddRadon.sphereArea (2 * n - 2) * (x ^ (2 * n - 2))⁻¹ *
              Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) γ x)
          = ((2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ *
              (2 * Work.OddRadon.sphereArea (2 * n - 2))) *
            (x ^ (2 * n - 2) * (x ^ (2 * n - 2))⁻¹) *
              Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) γ x by ring,
        inv_mul_cancel₀ hS, mul_inv_cancel₀ hx0]
      ring
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hγC
    have hrec := Work.OddVolterra.Free.abelReduceIter_abelTrans_local (β := (n : ℝ) - 3 / 2)
      (a₀ := a₀) (γ := γ) ha₀
      (hγC.mono (by intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
      ⟨M, fun s hs => by simpa [Real.norm_eq_abs] using hM s ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩
      (k := n - 1) hk
    have hcongr := Work.OddRadon.abelReduceIter_congr_open isOpen_Ioo (n - 1)
      ((n : ℝ) - 3 / 2) habel
    change Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
      (Work.OddRadon.abelDatum n δ) c = Θ c
    rw [hcongr hc, hrec hc, hexp, hΘdef]
  have hTh0 : ∀ c : ℝ, a₀ < c → Th c = 0 := by
    intro c hc
    have habel : Set.EqOn (Work.OddRadon.abelDatum n δ) 0 (Set.Ioi a₀) := by
      intro x hx
      simp only [Pi.zero_apply, Work.OddRadon.abelDatum]
      rw [hδz x hx]
      ring
    have h := Work.OddRadon.abelReduceIter_congr_open isOpen_Ioi (n - 1) ((n : ℝ) - 3 / 2) habel
    show Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
      (Work.OddRadon.abelDatum n δ) c = 0
    rw [h hc, Work.OddVolterra.Free.abelReduceIter_zero]
    rfl
  have hJsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : ℝ => ∫ c in (0 : ℝ)..a₀, c * Θ c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)))
      (Set.Ioi a₀) :=
    Work.OddVolterra.Free.fixedRangeAbelSmooth ha₀ hΘc
  have hPJ : ∀ v ∈ Set.Ioi a₀,
      (∫ c in (0 : ℝ)..v, c * Th c / Real.sqrt (v ^ 2 - c ^ 2))
        = ∫ c in (0 : ℝ)..a₀, c * Θ c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) := by
    intro v hv
    rw [abelIntegral_eq_supported_form ha₀ hv (fun c hc => hTh0 c hc)]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) a₀] with c hcne hc
    rw [Set.uIoc_of_le ha₀.le] at hc
    have hclt : c < a₀ := lt_of_le_of_ne hc.2 hcne
    rw [hΘTh c ⟨hc.1, hclt⟩]
  have hderivJ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (deriv (fun v : ℝ => ∫ c in (0 : ℝ)..a₀, c * Θ c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ))))
      (Set.Ioi a₀) :=
    ContDiffOn.deriv_of_isOpen (𝕜 := ℝ) (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hJsm isOpen_Ioi
      (by simp)
  have hgoal := (contDiffOn_const (c := (2 / Real.pi))).mul hderivJ
  refine ContDiffOn.congr hgoal (fun v hv => ?_)
  have hfun : (fun u : ℝ => ∫ c in (0 : ℝ)..u, c * Th c / Real.sqrt (u ^ 2 - c ^ 2))
      =ᶠ[𝓝 v] (fun u : ℝ => ∫ c in (0 : ℝ)..a₀, c * Θ c * (u ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hv] with u hu
    exact hPJ u hu
  have hrad : Work.OddRadon.radonInverse n δ v
      = (2 / Real.pi) * deriv (fun u : ℝ => ∫ c in (0 : ℝ)..u,
          c * Th c / Real.sqrt (u ^ 2 - c ^ 2)) v := by
    rw [Work.OddRadon.radonInverse_eq]
  simp only [hrad, hfun.deriv_eq]

/-! ## 6c. Smoothness of the glued data on `(-1, π/2+1)` -/

/-- `cos` maps `(-1, π/2+1)` into `(-1,1)`: the lower bound. -/
lemma neg_one_lt_cos_of_mem (α : ℝ) (hα : α ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    -1 < Real.cos α := by
  have hπ : Real.pi / 2 + 1 < Real.pi := by linarith [Real.pi_gt_three]
  have hlt : |α| < Real.pi := by
    rw [abs_lt]
    exact ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2, hπ]⟩
  have h : Real.cos Real.pi < Real.cos |α| :=
    Real.strictAntiOn_cos ⟨abs_nonneg α, le_of_lt hlt⟩ ⟨Real.pi_pos.le, le_rfl⟩ hlt
  rw [Real.cos_abs, Real.cos_pi] at h
  linarith

/-- In the anchor branch (`cos α < 4/5`) one also has `cos α < 1`. -/
lemma cos_lt_one_of_cos_lt (α : ℝ) (hα : α ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))
    (h : Real.cos α < 4 / 5) : Real.cos α < 1 := by
  rcases lt_or_eq_of_le (Real.cos_le_one α) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff α).mp h1
    have hπ : Real.pi / 2 + 1 < Real.pi := by linarith [Real.pi_gt_three]
    have habs : |α| < 2 * Real.pi := by
      rw [abs_lt]
      exact ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2, hπ, Real.pi_pos]⟩
    rw [← hk, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at habs
    have hk1 : |(k : ℝ)| < 1 := by
      have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
      nlinarith [habs, abs_nonneg (k : ℝ), hpos]
    have hk0 : k = 0 := by
      have : |k| < 1 := by exact_mod_cast hk1
      exact Int.abs_lt_one_iff.mp this
    rw [hk0] at hk
    simp only [Int.cast_zero, zero_mul] at hk
    rw [← hk] at h
    norm_num at h

/-- **The glued first datum is `C^∞` on `(-1, π/2+1)`.** -/
lemma contDiffOn_glueA (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hRsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ) u)
      (Set.Ioo (0 : ℝ) 1))
    (hdAsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) u)
      (Set.Ioi Work.OddCurve.LowSlope.cStar)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.glueA n ρ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
  have hform : ∀ β : ℝ, 0 < Real.cos β → Work.OddCurve.LowSlope.glueA n ρ β
      = 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ) (Real.cos β)
          / Real.cos β ^ 2 - 2 := by
    intro β hβ
    by_cases hlt : Real.cos β < 4 / 5
    · have h1 : Work.OddCurve.LowSlope.glueA n ρ β
          = ρ (Real.cos β) ^ (2 * n + 2) + ρ (-(Real.cos β)) ^ (2 * n + 2) - 2 :=
        Work.OddCurve.LowSlope.glueA_of_lt hlt
      have h2 : Work.OddCurve.LowSlope.GlueA n ρ β
          = ρ (Real.cos β) ^ (2 * n + 2) + ρ (-(Real.cos β)) ^ (2 * n + 2) - 2 :=
        Work.OddCurve.LowSlope.GlueA_eq n hn hρsm (by linarith [hlt]) hlt
      rw [h1, ← h2]
      show Work.OddCurve.LowSlope.GlueA n ρ β
          = 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ) (Real.cos β)
              / Real.cos β ^ 2 - 2
      rw [Work.OddCurve.LowSlope.GlueA, Work.OddCurve.LowSlope.GluePhi]
    · rw [Work.OddCurve.LowSlope.glueA_of_ge (le_of_not_gt hlt), Work.OddCurve.LowSlope.GlueA,
        Work.OddCurve.LowSlope.GluePhi]
  have hformΔ : ∀ β : ℝ, 0 < Real.cos β → Real.cos β ≠ 4 / 5 →
      Work.OddCurve.LowSlope.glueA n ρ β
      = 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) (Real.cos β)
          / Real.cos β ^ 2 :=
    fun β hβ hne => glueA_eq_deltaA n hn hρsm hβ hne
  intro α hα
  rcases lt_trichotomy (Real.cos α) (4 / 5) with hlt | heq | hgt
  · -- the anchor branch
    have hcos1 : Real.cos α < 1 := cos_lt_one_of_cos_lt α hα hlt
    have hcosm1 : -1 < Real.cos α := neg_one_lt_cos_of_mem α hα
    have hev : Work.OddCurve.LowSlope.glueA n ρ =ᶠ[𝓝 α]
        (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 2) + ρ (-(Real.cos β)) ^ (2 * n + 2) - 2) := by
      have hopen : {β : ℝ | Real.cos β < 4 / 5} ∈ 𝓝 α :=
        (isOpen_lt Real.continuous_cos continuous_const).mem_nhds hlt
      filter_upwards [hopen] with β hβ
      rw [Work.OddCurve.LowSlope.glueA_of_lt hβ]
    have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 2) + ρ (-(Real.cos β)) ^ (2 * n + 2) - 2) α := by
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ => ρ (Real.cos β)) α :=
        (hρsm.contDiffAt (isOpen_Ioo.mem_nhds ⟨hcosm1, hcos1⟩)).comp α
          Real.contDiff_cos.contDiffAt
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ => ρ (-(Real.cos β))) α :=
        (hρsm.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).comp α
          Real.contDiff_cos.contDiffAt.neg
      exact ((h1.pow _).add (h2.pow _)).sub contDiffAt_const
    exact (hsm.congr_of_eventuallyEq hev).contDiffWithinAt
  · -- the junction (and `cos α ≥ 4/5` in general): the `GlueF`-form
    have hcos1 : Real.cos α < 1 := by rw [heq]; norm_num
    have hcos0 : 0 < Real.cos α := by rw [heq]; norm_num
    have hev : Work.OddCurve.LowSlope.glueA n ρ =ᶠ[𝓝 α]
        (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ)
          (Real.cos β) / Real.cos β ^ 2 - 2) := by
      have hopen : {β : ℝ | 0 < Real.cos β} ∈ 𝓝 α :=
        (isOpen_lt continuous_const Real.continuous_cos).mem_nhds hcos0
      filter_upwards [hopen] with β hβ
      exact hform β hβ
    have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ)
          (Real.cos β) / Real.cos β ^ 2 - 2) α := by
      have hR1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ) u)
          (Real.cos α) :=
        hRsm.contDiffAt (isOpen_Ioo.mem_nhds ⟨hcos0, hcos1⟩)
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun β : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ)
            (Real.cos β)) α := by
        exact hR1.comp α Real.contDiff_cos.contDiffAt
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ => Real.cos β ^ 2) α :=
        Real.contDiff_cos.contDiffAt.pow 2
      have h3 : (fun β : ℝ => Real.cos β ^ 2) α ≠ 0 := by
        simp only [Pi.pow_apply]; positivity
      exact ((contDiffAt_const (c := (2:ℝ))).mul h1).div h2 h3 |>.sub contDiffAt_const
    exact (hsm.congr_of_eventuallyEq hev).contDiffWithinAt
  · -- `cos α > 4/5`
    rcases lt_or_eq_of_le (Real.cos_le_one α) with hlt1 | heq1
    · -- `4/5 < cos α < 1`: the `GlueF`-form again
      have hcos0 : 0 < Real.cos α := by linarith
      have hev : Work.OddCurve.LowSlope.glueA n ρ =ᶠ[𝓝 α]
          (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ)
            (Real.cos β) / Real.cos β ^ 2 - 2) := by
        have hopen : {β : ℝ | 0 < Real.cos β} ∈ 𝓝 α :=
          (isOpen_lt continuous_const Real.continuous_cos).mem_nhds hcos0
        filter_upwards [hopen] with β hβ
        exact hform β hβ
      have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ)
            (Real.cos β) / Real.cos β ^ 2 - 2) α := by
        have hR1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun u : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ) u)
            (Real.cos α) :=
          hRsm.contDiffAt (isOpen_Ioo.mem_nhds ⟨hcos0, hlt1⟩)
        have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun β : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ)
              (Real.cos β)) α := by
          exact hR1.comp α Real.contDiff_cos.contDiffAt
        have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ => Real.cos β ^ 2) α :=
          Real.contDiff_cos.contDiffAt.pow 2
        have h3 : (fun β : ℝ => Real.cos β ^ 2) α ≠ 0 := by
          simp only [Pi.pow_apply]; positivity
        exact ((contDiffAt_const (c := (2:ℝ))).mul h1).div h2 h3 |>.sub contDiffAt_const
      exact (hsm.congr_of_eventuallyEq hev).contDiffWithinAt
    · -- `cos α = 1` forces `α = 0`: the `deltaA`-form
      have hα0 : α = 0 := by
        obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff α).mp heq1
        have hπ : Real.pi / 2 + 1 < Real.pi := by linarith [Real.pi_gt_three]
        have habs : |α| < 2 * Real.pi := by
          rw [abs_lt]
          exact ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2, hπ, Real.pi_pos]⟩
        rw [← hk, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at habs
        have hk1 : |(k : ℝ)| < 1 := by
          have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
          nlinarith [habs, abs_nonneg (k : ℝ), hpos]
        have hk0 : k = 0 := by
          have : |k| < 1 := by exact_mod_cast hk1
          exact Int.abs_lt_one_iff.mp this
        rw [hk0] at hk
        simpa using hk.symm
      subst hα0
      have hev : Work.OddCurve.LowSlope.glueA n ρ =ᶠ[𝓝 (0 : ℝ)]
          (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ)
            (Real.cos β) / Real.cos β ^ 2) := by
        have hopen₁ : {β : ℝ | Real.cos β ≠ 4 / 5} ∈ 𝓝 (0 : ℝ) :=
          (isOpen_ne.preimage Real.continuous_cos).mem_nhds (by
            show Real.cos 0 ≠ 4 / 5
            rw [Real.cos_zero]; norm_num)
        have hopen₂ : {β : ℝ | 0 < Real.cos β} ∈ 𝓝 (0 : ℝ) :=
          (isOpen_lt continuous_const Real.continuous_cos).mem_nhds (by
            show 0 < Real.cos 0
            rw [Real.cos_zero]; norm_num)
        filter_upwards [hopen₁, hopen₂] with β hβ hβpos
        exact hformΔ β hβpos hβ
      have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ)
            (Real.cos β) / Real.cos β ^ 2) (0 : ℝ) := by
        have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun β : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ)
              (Real.cos β)) 0 := by
          exact (hdAsm.contDiffAt (isOpen_Ioi.mem_nhds (by
            rw [Real.cos_zero]
            exact lt_trans Work.OddCurve.LowSlope.cStar_lt_four_fifths (by norm_num)))).comp 0
            Real.contDiff_cos.contDiffAt
        have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ => Real.cos β ^ 2) 0 :=
          Real.contDiff_cos.contDiffAt.pow 2
        have h3 : (fun β : ℝ => Real.cos β ^ 2) 0 ≠ 0 := by
          simp only [Pi.pow_apply, Real.cos_zero]; norm_num
        exact ((contDiffAt_const (c := (2:ℝ))).mul h1).div h2 h3
      exact (hsm.congr_of_eventuallyEq hev).contDiffWithinAt

/-- **The glued second datum is `C^∞` on `(-1, π/2+1)`.** -/
lemma contDiffOn_glueB (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hRBsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueG n ρ) u)
      (Set.Ioo (0 : ℝ) 1))
    (hdBsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ) u)
      (Set.Ioi Work.OddCurve.LowSlope.cStar)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.glueB n ρ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
  have hform : ∀ β : ℝ, 0 < Real.cos β → Work.OddCurve.LowSlope.glueB n ρ β
      = 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ) (Real.cos β)
          / Real.cos β := fun β hβ => glueB_eq_deltaB n hn hρsm (α := β) hβ
  have hformΔ : ∀ β : ℝ, 0 < Real.cos β → Work.OddCurve.LowSlope.glueB n ρ β
      = 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ) (Real.cos β)
          / Real.cos β := fun β hβ => glueB_eq_deltaB n hn hρsm (α := β) hβ
  intro α hα
  rcases lt_trichotomy (Real.cos α) (4 / 5) with hlt | heq | hgt
  · -- the anchor branch
    have hcos1 : Real.cos α < 1 := cos_lt_one_of_cos_lt α hα hlt
    have hcosm1 : -1 < Real.cos α := neg_one_lt_cos_of_mem α hα
    have hev : Work.OddCurve.LowSlope.glueB n ρ =ᶠ[𝓝 α]
        (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 1) - ρ (-(Real.cos β)) ^ (2 * n + 1)) := by
      have hopen : {β : ℝ | Real.cos β < 4 / 5} ∈ 𝓝 α :=
        (isOpen_lt Real.continuous_cos continuous_const).mem_nhds hlt
      filter_upwards [hopen] with β hβ
      rw [Work.OddCurve.LowSlope.glueB_of_lt hβ]
    have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 1) - ρ (-(Real.cos β)) ^ (2 * n + 1)) α := by
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ => ρ (Real.cos β)) α :=
        (hρsm.contDiffAt (isOpen_Ioo.mem_nhds ⟨hcosm1, hcos1⟩)).comp α
          Real.contDiff_cos.contDiffAt
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ => ρ (-(Real.cos β))) α :=
        (hρsm.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).comp α
          Real.contDiff_cos.contDiffAt.neg
      exact (h1.pow _).sub (h2.pow _)
    exact (hsm.congr_of_eventuallyEq hev).contDiffWithinAt
  · -- the junction: the `GlueG`-form
    have hcos1 : Real.cos α < 1 := by rw [heq]; norm_num
    have hcos0 : 0 < Real.cos α := by rw [heq]; norm_num
    have hev : Work.OddCurve.LowSlope.glueB n ρ =ᶠ[𝓝 α]
        (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
          (Real.cos β) / Real.cos β) := by
      have hopen : {β : ℝ | 0 < Real.cos β} ∈ 𝓝 α :=
        (isOpen_lt continuous_const Real.continuous_cos).mem_nhds hcos0
      filter_upwards [hopen] with β hβ
      exact hform β hβ
    have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
          (Real.cos β) / Real.cos β) α := by
      have hR1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ) u)
          (Real.cos α) :=
        hdBsm.contDiffAt (isOpen_Ioi.mem_nhds (by rw [heq]; exact Work.OddCurve.LowSlope.cStar_lt_four_fifths))
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun β : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
            (Real.cos β)) α := by
        exact hR1.comp α Real.contDiff_cos.contDiffAt
      exact ((contDiffAt_const (c := (2:ℝ))).mul h1).div Real.contDiff_cos.contDiffAt
        (ne_of_gt hcos0)
    exact (hsm.congr_of_eventuallyEq hev).contDiffWithinAt
  · -- `cos α > 4/5`
    rcases lt_or_eq_of_le (Real.cos_le_one α) with hlt1 | heq1
    · have hcos0 : 0 < Real.cos α := by linarith
      have hev : Work.OddCurve.LowSlope.glueB n ρ =ᶠ[𝓝 α]
          (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
            (Real.cos β) / Real.cos β) := by
        have hopen : {β : ℝ | 0 < Real.cos β} ∈ 𝓝 α :=
          (isOpen_lt continuous_const Real.continuous_cos).mem_nhds hcos0
        filter_upwards [hopen] with β hβ
        exact hform β hβ
      have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
            (Real.cos β) / Real.cos β) α := by
        have hR1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun u : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ) u)
            (Real.cos α) :=
          hdBsm.contDiffAt (isOpen_Ioi.mem_nhds
            (lt_trans Work.OddCurve.LowSlope.cStar_lt_four_fifths hgt))
        have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun β : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
              (Real.cos β)) α := by
          exact hR1.comp α Real.contDiff_cos.contDiffAt
        exact ((contDiffAt_const (c := (2:ℝ))).mul h1).div Real.contDiff_cos.contDiffAt
          (ne_of_gt hcos0)
      exact (hsm.congr_of_eventuallyEq hev).contDiffWithinAt
    · -- `cos α = 1` forces `α = 0`: the `deltaB`-form
      have hα0 : α = 0 := by
        obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff α).mp heq1
        have hπ : Real.pi / 2 + 1 < Real.pi := by linarith [Real.pi_gt_three]
        have habs : |α| < 2 * Real.pi := by
          rw [abs_lt]
          exact ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2, hπ, Real.pi_pos]⟩
        rw [← hk, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at habs
        have hk1 : |(k : ℝ)| < 1 := by
          have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
          nlinarith [habs, abs_nonneg (k : ℝ), hpos]
        have hk0 : k = 0 := by
          have : |k| < 1 := by exact_mod_cast hk1
          exact Int.abs_lt_one_iff.mp this
        rw [hk0] at hk
        simpa using hk.symm
      subst hα0
      have hev : Work.OddCurve.LowSlope.glueB n ρ =ᶠ[𝓝 (0 : ℝ)]
          (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
            (Real.cos β) / Real.cos β) := by
        have hopen₂ : {β : ℝ | 0 < Real.cos β} ∈ 𝓝 (0 : ℝ) :=
          (isOpen_lt continuous_const Real.continuous_cos).mem_nhds (by
            show 0 < Real.cos 0
            rw [Real.cos_zero]; norm_num)
        filter_upwards [hopen₂] with β hβpos
        exact hformΔ β hβpos
      have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
            (Real.cos β) / Real.cos β) (0 : ℝ) := by
        have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun β : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
              (Real.cos β)) 0 := by
          exact (hdBsm.contDiffAt (isOpen_Ioi.mem_nhds (by
            rw [Real.cos_zero]
            exact lt_trans Work.OddCurve.LowSlope.cStar_lt_four_fifths (by norm_num)))).comp 0
            Real.contDiff_cos.contDiffAt
        have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun β : ℝ => Real.cos β) 0 :=
          Real.contDiff_cos.contDiffAt
        exact ((contDiffAt_const (c := (2:ℝ))).mul h1).div h2 (by
          rw [Real.cos_zero]; norm_num)
      exact (hsm.congr_of_eventuallyEq hev).contDiffWithinAt

/-- A function that vanishes off a point and is continuous there vanishes in a full
neighbourhood. -/
lemma eventuallyEq_zero_of_eventuallyEq_nhdsNE_of_continuousAt {f : ℝ → ℝ} {x : ℝ}
    (h : f =ᶠ[𝓝[≠] x] 0) (hc : ContinuousAt f x) : f =ᶠ[𝓝 x] 0 := by
  have hfx : f x = 0 := by
    have h1 : Tendsto f (𝓝[≠] x) (𝓝 (f x)) := hc.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto f (𝓝[≠] x) (𝓝 0) := tendsto_const_nhds.congr' h.symm
    exact tendsto_nhds_unique h1 h2
  have hsum : 𝓝 x = 𝓝[≠] x ⊔ pure x := by
    rw [← nhdsWithin_singleton x, ← nhdsWithin_union, Set.compl_union_self, nhdsWithin_univ]
  rw [Filter.EventuallyEq, hsum, eventually_sup]
  exact ⟨h, by rw [Filter.eventually_pure]; exact hfx⟩

/-! ## 7. The main theorem -/

/-- **Smoothness and linear derivative bounds of the glued low-slope data of the odd case.**

For every `n ≥ 1` there is `K > 0` such that for every anchor (a curve `(X,Y)` satisfying the
moment equations outside the bump window, with radial function `ρ` whose deviation from `1` is
controlled by `C₁ε`) the two glued data `glueA n ρ`, `glueB n ρ` of the low-slope step are
`C^∞` on `(-1, π/2+1)` and their derivatives on `[0,π/2]` are `O((C₁+1)ε sin α)`. -/
theorem glueDataSmoothLinear (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ε C₁ : ℝ} {h X Y ρ : ℝ → ℝ},
      0 < ε → C₁ * ε ≤ 1 →
      Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h →
      h ≠ 0 →
      Work.OddEnvelope.IsEnvelopeCurve h X Y →
      Work.OddCurve.LowSlope.CloseToProfileX X →
      Work.OddCurve.LowSlope.CloseToProfileX Y →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
          Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
      Work.OddVolterra.Free.IsAnchorRadial h X Y ρ →
      (∀ u : ℝ, |u| < 4 / 5 →
        |ρ u - 1| ≤ C₁ * ε ∧ |deriv ρ u| ≤ C₁ * ε ∧ |deriv (deriv ρ) u| ≤ C₁ * ε) →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.glueA n ρ)
          (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.glueB n ρ)
          (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) ∧
        (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          |deriv (Work.OddCurve.LowSlope.glueA n ρ) α| ≤ K * (C₁ + 1) * ε * Real.sin α ∧
          |deriv (Work.OddCurve.LowSlope.glueB n ρ) α| ≤ K * (C₁ + 1) * ε * Real.sin α) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := radonInverse_gap_bound n hn
  set Kb : ℝ := (11 * C₀ + 1) * ((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2)
      + (6 * C₀ + 1) * ((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1) + 1 with hKbdef
  have hKbpos : 0 < Kb := by
    have h1 : (0 : ℝ) < 11 * C₀ + 1 := by linarith
    have h2 : (0 : ℝ) < 6 * C₀ + 1 := by linarith
    have h3 : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) := by positivity
    have h4 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
    have h5 : (0 : ℝ) < (2 : ℝ) ^ (2 * n + 2) := by positivity
    have h6 : (0 : ℝ) < (2 : ℝ) ^ (2 * n + 1) := by positivity
    rw [hKbdef]
    positivity
  refine ⟨Kb, hKbpos, ?_⟩
  intro ε C₁ h X Y ρ hε hCε hbump hhne hH hX hY hA hB hρ0 hdev
  have hanc := hρ0
  obtain ⟨hρpos, hρsm, hρmono, hgraph, hρ00⟩ := hρ0
  set M0 : ℝ := ((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2) * (C₁ * ε) with hM0def
  set M1 : ℝ := ((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1) * (C₁ * ε) with hM1def
  -- ### 0. the junction and the smoothness of the glued data
  have hjun := junctionWindow n hn hH hA hB hanc
  have hglue := glueDataContDiffOnIcc n hn hρsm hjun
  have hRsm := Work.OddRadon.contDiffOn_radonInverse n hn hglue.1
  have hRBsm := Work.OddRadon.contDiffOn_radonInverse n hn hglue.2
  -- ### 1. the deviation bounds
  have hC₁εnn : 0 ≤ C₁ * ε := by
    have h := (hdev 0 (by norm_num)).1
    rw [hρ00, sub_self, abs_zero] at h
    linarith
  have hεnn : (0 : ℝ) ≤ ε := le_of_lt hε
  have hC₁nn : (0 : ℝ) ≤ C₁ := by nlinarith [hC₁εnn, hε]
  have hρ2 : ∀ u : ℝ, |u| < 4 / 5 → |ρ u| ≤ 2 := by
    intro u hu
    have h1 := (hdev u hu).1
    calc |ρ u| = |(ρ u - 1) + 1| := by ring_nf
      _ ≤ |ρ u - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ C₁ * ε + 1 := by rw [abs_one]; linarith
      _ ≤ 2 := by linarith
  have hpow_bound : ∀ u : ℝ, |u| < 4 / 5 → ∀ m : ℕ,
      |ρ u ^ m - 1| ≤ (m : ℝ) * (C₁ * ε) * (2 : ℝ) ^ (m - 1) := by
    intro u hu m
    have h1 : |ρ u ^ m - 1 ^ m| ≤ |ρ u - 1| * (m : ℝ) * max |ρ u| |(1:ℝ)| ^ (m - 1) :=
      abs_pow_sub_pow_le (ρ u) 1 m
    rw [one_pow] at h1
    have h2 : |ρ u - 1| ≤ C₁ * ε := (hdev u hu).1
    have h3 : max |ρ u| |(1 : ℝ)| ≤ 2 := by
      rw [max_le_iff]
      exact ⟨hρ2 u hu, by norm_num⟩
    have h5 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h6 : (0 : ℝ) ≤ max |ρ u| |(1:ℝ)| ^ (m - 1) := by positivity
    have h7 : max |ρ u| |(1:ℝ)| ^ (m - 1) ≤ 2 ^ (m - 1) :=
      pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) h3 (m - 1)
    have h4 : |ρ u - 1| * (m : ℝ) * max |ρ u| |(1:ℝ)| ^ (m - 1)
        ≤ (C₁ * ε) * (m : ℝ) * max |ρ u| |(1:ℝ)| ^ (m - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 h5) h6
    have h4' : (C₁ * ε) * (m : ℝ) * max |ρ u| |(1:ℝ)| ^ (m - 1)
        ≤ (C₁ * ε) * (m : ℝ) * 2 ^ (m - 1) :=
      mul_le_mul_of_nonneg_left h7 (mul_nonneg hC₁εnn h5)
    linarith [h1, h4, h4']
  -- ### 2. the two bounds for the deviation profiles
  have hγdevb : ∀ u : ℝ, |u| < 79 / 100 →
      |Work.OddCurve.LowSlope.gammaDev n ρ u|
        ≤ ((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2) * (C₁ * ε) := by
    intro u hu
    have hu45 : |u| < 4 / 5 := lt_trans hu (by norm_num)
    have h1 := hpow_bound u hu45 (2 * n + 2)
    have h1' := hpow_bound (-u) (by rwa [abs_neg]) (2 * n + 2)
    have hexp : (2 * n + 2) - 1 = 2 * n + 1 := by omega
    rw [hexp] at h1 h1'
    have h2 : |(ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)) / 2 - 1|
        ≤ ((2 * n + 2 : ℕ) : ℝ) * (C₁ * ε) * (2 : ℝ) ^ (2 * n + 1) := by
      have hsum : (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)) / 2 - 1
          = (ρ u ^ (2 * n + 2) - 1) / 2 + (ρ (-u) ^ (2 * n + 2) - 1) / 2 := by ring
      have h3 : |(ρ u ^ (2 * n + 2) - 1) / 2| ≤ ((2 * n + 2 : ℕ) : ℝ) * (C₁ * ε)
          * (2 : ℝ) ^ (2 * n + 1) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        linarith [h1]
      have h3' : |(ρ (-u) ^ (2 * n + 2) - 1) / 2| ≤ ((2 * n + 2 : ℕ) : ℝ) * (C₁ * ε)
          * (2 : ℝ) ^ (2 * n + 1) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        linarith [h1']
      rw [hsum]
      calc |(ρ u ^ (2*n+2) - 1)/2 + (ρ (-u) ^ (2*n+2) - 1)/2|
          ≤ |(ρ u ^ (2*n+2) - 1)/2| + |(ρ (-u) ^ (2*n+2) - 1)/2| := abs_add_le _ _
        _ ≤ ((2*n+2 : ℕ):ℝ) * (C₁*ε) * 2^(2*n+1) / 2
              + ((2*n+2 : ℕ):ℝ) * (C₁*ε) * 2^(2*n+1) / 2 := by linarith [h3, h3']
        _ = ((2*n+2 : ℕ):ℝ) * (C₁*ε) * 2^(2*n+1) := by ring
    have h4 : Work.OddCurve.LowSlope.gammaDev n ρ u
        = u ^ 2 * ((ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)) / 2 - 1) := rfl
    rw [h4, abs_mul]
    calc |u ^ 2| * |(ρ u ^ (2*n+2) + ρ (-u) ^ (2*n+2))/2 - 1|
        ≤ 1 * (((2*n+2 : ℕ):ℝ) * (C₁*ε) * 2^(2*n+1)) := by
          refine mul_le_mul ?_ h2 (abs_nonneg _) (by norm_num)
          rw [abs_of_nonneg (sq_nonneg u)]
          have hsq : u ^ 2 = |u| ^ 2 := by rw [sq_abs]
          nlinarith [abs_nonneg u, hu, hsq]
      _ ≤ ((2*n+2 : ℕ):ℝ) * 2^(2*n+2) * (C₁*ε) := by
          have hpow : (2 : ℝ) ^ (2 * n + 2) = 2 * 2 ^ (2 * n + 1) := by
            rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]; ring
          rw [one_mul, hpow]
          have hX : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) * C₁ * ε * 2 ^ (2 * n + 1) := by positivity
          linarith
  have hγpsib : ∀ u : ℝ, |u| < 79 / 100 →
      |Work.OddCurve.LowSlope.gammaPsi n ρ u|
        ≤ ((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1) * (C₁ * ε) := by
    intro u hu
    have hu45 : |u| < 4 / 5 := lt_trans hu (by norm_num)
    have h1 := hpow_bound u hu45 (2 * n + 1)
    have h1' := hpow_bound (-u) (by rwa [abs_neg]) (2 * n + 1)
    have hexp : (2 * n + 1) - 1 = 2 * n := by omega
    rw [hexp] at h1 h1'
    have h2 : |ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)|
        ≤ 2 * (((2 * n + 1 : ℕ) : ℝ) * (C₁ * ε) * (2 : ℝ) ^ (2 * n)) := by
      have hsum : ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)
          = (ρ u ^ (2 * n + 1) - 1) - (ρ (-u) ^ (2 * n + 1) - 1) := by ring
      rw [hsum]
      calc |(ρ u ^ (2*n+1) - 1) - (ρ (-u) ^ (2*n+1) - 1)|
          ≤ |(ρ u ^ (2*n+1) - 1)| + |(ρ (-u) ^ (2*n+1) - 1)| := by
              have h := abs_sub_le (ρ u ^ (2*n+1) - 1) 0 (ρ (-u) ^ (2*n+1) - 1)
              rwa [sub_zero, zero_sub, abs_neg] at h
        _ ≤ ((2*n+1 : ℕ):ℝ) * (C₁*ε) * 2^(2*n) + ((2*n+1 : ℕ):ℝ) * (C₁*ε) * 2^(2*n) := by
            linarith [h1, h1']
        _ = 2 * (((2*n+1 : ℕ):ℝ) * (C₁*ε) * 2^(2*n)) := by ring
    have h4 : Work.OddCurve.LowSlope.gammaPsi n ρ u
        = u * (ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)) / 2 := rfl
    rw [h4, abs_div, abs_mul]
    have h5 : |u| ≤ 79 / 100 := le_of_lt hu
    calc |u| * |ρ u ^ (2*n+1) - ρ (-u) ^ (2*n+1)| / |(2:ℝ)|
        ≤ (79/100) * (2 * (((2*n+1 : ℕ):ℝ) * (C₁*ε) * 2^(2*n))) / 2 := by
          have hden : |(2:ℝ)| = 2 := abs_of_pos (by norm_num)
          rw [hden]
          exact div_le_div_of_nonneg_right
            (mul_le_mul h5 h2 (abs_nonneg _) (by norm_num)) (by norm_num)
      _ ≤ ((2*n+1 : ℕ):ℝ) * 2^(2*n+1) * (C₁*ε) := by
          have hpow : (2 : ℝ) ^ (2 * n + 1) = 2 * 2 ^ (2 * n) := by
            rw [show 2 * n + 1 = 2 * n + 1 from rfl, pow_succ]; ring
          rw [hpow]
          have hX : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) * C₁ * ε * 2 ^ (2 * n) := by positivity
          linarith
  -- ### 3. the gap bounds for the two deviations
  have hcStarpos : 0 < Work.OddCurve.LowSlope.cStar := Work.OddCurve.LowSlope.cStar_pos
  have hcStar45 : Work.OddCurve.LowSlope.cStar < 4 / 5 :=
    Work.OddCurve.LowSlope.cStar_lt_four_fifths
  have hγdevC : ContinuousOn (Work.OddCurve.LowSlope.gammaDev n ρ)
      (Set.Icc 0 Work.OddCurve.LowSlope.cStar) := by
    have hcont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.gammaDev n ρ)
        (Set.Ioo (-1 : ℝ) 1) := by
      have hfun : Work.OddCurve.LowSlope.gammaDev n ρ
          = fun u : ℝ => u ^ 2 * ((ρ u ^ (2*n+2) + ρ (-u) ^ (2*n+2)) / 2 - 1) := rfl
      rw [hfun]
      have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ρ u ^ (2*n+2))
          (Set.Ioo (-1:ℝ) 1) := hρsm.pow _
      have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ρ (-u) ^ (2*n+2))
          (Set.Ioo (-1:ℝ) 1) :=
        (hρsm.comp (by fun_prop) (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)).pow _
      exact ((contDiffOn_id.pow 2).mul ((h1.add h2).div_const 2 |>.sub contDiffOn_const))
    exact hcont.continuousOn.mono (fun x hx => ⟨by linarith [hx.1, hcStar45],
      lt_of_le_of_lt hx.2 (by linarith [hcStar45])⟩)
  have hγdev0 : Work.OddCurve.LowSlope.gammaDev n ρ 0 = 0 := by
    simp [Work.OddCurve.LowSlope.gammaDev]
  have hγpsi0 : Work.OddCurve.LowSlope.gammaPsi n ρ 0 = 0 := by
    simp [Work.OddCurve.LowSlope.gammaPsi]
  have hγpsiC : ContinuousOn (Work.OddCurve.LowSlope.gammaPsi n ρ)
      (Set.Icc 0 Work.OddCurve.LowSlope.cStar) := by
    have hcont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.gammaPsi n ρ)
        (Set.Ioo (-1 : ℝ) 1) := by
      have hfun : Work.OddCurve.LowSlope.gammaPsi n ρ
          = fun u : ℝ => u * (ρ u ^ (2*n+1) - ρ (-u) ^ (2*n+1)) / 2 := rfl
      rw [hfun]
      have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ρ u ^ (2*n+1))
          (Set.Ioo (-1:ℝ) 1) := hρsm.pow _
      have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ρ (-u) ^ (2*n+1))
          (Set.Ioo (-1:ℝ) 1) :=
        (hρsm.comp (by fun_prop) (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)).pow _
      exact ((contDiffOn_id.mul (h1.sub h2)).div_const 2)
    exact hcont.continuousOn.mono (fun x hx => ⟨by linarith [hx.1, hcStar45],
      lt_of_le_of_lt hx.2 (by linarith [hcStar45])⟩)
  -- the deviations vanish above the glue point
  have hδAz : ∀ c : ℝ, Work.OddCurve.LowSlope.cStar < c →
      Work.OddCurve.LowSlope.deltaA n ρ c = 0 := by
    intro c hc
    have hcpos : 0 < c := lt_trans hcStarpos hc
    by_cases hc45 : c < 4 / 5
    · have h := (junctionWindowCap n hn hH hA hB hanc c ⟨hc, hc45⟩).1
      have hG : Work.OddCurve.LowSlope.GlueF n ρ c = Work.OddCurve.LowSlope.radonPhi n ρ c := by
        simp only [Work.OddCurve.LowSlope.GlueF]
        rw [abs_of_pos hcpos]
        exact Work.OddCurve.LowSlope.gluedPhi_of_lt hcpos.le hc45
      rw [Work.OddCurve.LowSlope.deltaA_def, hG, h]
      ring
    · have hcge : 4 / 5 ≤ c := le_of_not_gt hc45
      have h1 : Work.OddCurve.LowSlope.GlueF n ρ c = Work.OddCurve.LowSlope.ballPhiData n c := by
        simp only [Work.OddCurve.LowSlope.GlueF]
        rw [abs_of_pos hcpos]
        exact Work.OddCurve.LowSlope.gluedPhi_of_ge hcpos.le hcge
      rw [Work.OddCurve.LowSlope.deltaA_def, h1]
      ring
  have hδBz : ∀ c : ℝ, Work.OddCurve.LowSlope.cStar < c →
      Work.OddCurve.LowSlope.deltaB n ρ c = 0 := by
    intro c hc
    have hcpos : 0 < c := lt_trans hcStarpos hc
    by_cases hc45 : c < 4 / 5
    · have h := (junctionWindowCap n hn hH hA hB hanc c ⟨hc, hc45⟩).2
      have hG : Work.OddCurve.LowSlope.GlueG n ρ c = Work.OddCurve.LowSlope.radonPsi n ρ c := by
        simp only [Work.OddCurve.LowSlope.GlueG]
        rw [abs_of_pos hcpos]
        exact Work.OddCurve.LowSlope.gluedPsi_of_lt hcpos.le hc45
      rw [Work.OddCurve.LowSlope.deltaB_def, hG, h]
    · have hcge : 4 / 5 ≤ c := le_of_not_gt hc45
      rw [Work.OddCurve.LowSlope.deltaB_def, Work.OddCurve.LowSlope.GlueG, abs_of_pos hcpos]
      exact Work.OddCurve.LowSlope.gluedPsi_of_ge hcpos.le hcge
  have hδAr : ∀ c ∈ Set.Ioo (0 : ℝ) Work.OddCurve.LowSlope.cStar,
      Work.OddCurve.LowSlope.deltaA n ρ c
        = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaDev n ρ) c :=
    fun c hc => (delta_cap_identity n hn hρsm c
      ⟨hc.1, lt_trans hc.2 hcStar45⟩).1
  have hδBr : ∀ c ∈ Set.Ioo (0 : ℝ) Work.OddCurve.LowSlope.cStar,
      Work.OddCurve.LowSlope.deltaB n ρ c
        = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaPsi n ρ) c :=
    fun c hc => (delta_cap_identity n hn hρsm c
      ⟨hc.1, lt_trans hc.2 hcStar45⟩).2
  have hgapA := hC₀ (Work.OddCurve.LowSlope.gammaDev n ρ) (Work.OddCurve.LowSlope.deltaA n ρ)
    Work.OddCurve.LowSlope.cStar
    M0
    hcStarpos le_rfl (by positivity) (Work.OddCurve.LowSlope.gammaDev_even n ρ) hγdevC hγdev0
    (fun c hc => hγdevb c (by
      rw [abs_lt]
      exact ⟨by linarith [hc.1], by linarith [hc.2]⟩))
    hδAz hδAr
  have hgapB := hC₀ (Work.OddCurve.LowSlope.gammaPsi n ρ) (Work.OddCurve.LowSlope.deltaB n ρ)
    Work.OddCurve.LowSlope.cStar
    M1
    hcStarpos le_rfl (by positivity) (Work.OddCurve.LowSlope.gammaPsi_even n ρ) hγpsiC hγpsi0
    (fun c hc => hγpsib c (by
      rw [abs_lt]
      exact ⟨by linarith [hc.1], by linarith [hc.2]⟩))
    hδBz hδBr
  -- shorthand for the bounds
  have hbA1 : ∀ u ∈ Set.Icc (4/5:ℝ) 1,
      |Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) u|
        ≤ C₀ * M0 :=
    fun u hu => (hgapA u hu).1
  have hbA2 : ∀ u ∈ Set.Icc (4/5:ℝ) 1,
      |deriv (fun v : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) v) u|
        ≤ C₀ * M0 :=
    fun u hu => (hgapA u hu).2.1
  have hbA3 : ∀ u ∈ Set.Icc (4/5:ℝ) 1,
      DifferentiableAt ℝ (Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ)) u :=
    fun u hu => (hgapA u hu).2.2
  have hbB1 : ∀ u ∈ Set.Icc (4/5:ℝ) 1,
      |Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ) u|
        ≤ C₀ * M1 :=
    fun u hu => (hgapB u hu).1
  have hbB2 : ∀ u ∈ Set.Icc (4/5:ℝ) 1,
      |deriv (fun v : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ) v) u|
        ≤ C₀ * M1 :=
    fun u hu => (hgapB u hu).2.1
  have hbB3 : ∀ u ∈ Set.Icc (4/5:ℝ) 1,
      DifferentiableAt ℝ (Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)) u :=
    fun u hu => (hgapB u hu).2.2
  have hMA : (0:ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2) * (C₁ * ε) := by positivity
  have hMB : (0:ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1) * (C₁ * ε) := by positivity
  -- ### 4. the smoothness of the two deviations above the glue point
  have hdAsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) u)
      (Set.Ioi Work.OddCurve.LowSlope.cStar) :=
    radonInverse_gap_smooth n hn hcStarpos (Work.OddCurve.LowSlope.gammaDev_even n ρ) hγdevC
      hγdev0 hδAz hδAr
  have hdBsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ) u)
      (Set.Ioi Work.OddCurve.LowSlope.cStar) :=
    radonInverse_gap_smooth n hn hcStarpos (Work.OddCurve.LowSlope.gammaPsi_even n ρ) hγpsiC
      hγpsi0 hδBz hδBr
  -- ### 5. smoothness of the two glued data
  have hglueAsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.glueA n ρ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    contDiffOn_glueA n hn hρsm hRsm hdAsm
  have hglueBsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.glueB n ρ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    contDiffOn_glueB n hn hρsm hRBsm hdBsm
  -- ### 6. the derivative bounds
  have hmemIoo : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), α ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    fun α hα => ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hsinN : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 0 ≤ Real.sin α :=
    fun α hα => Real.sin_nonneg_of_mem_Icc ⟨hα.1, by linarith [hα.2, Real.pi_pos]⟩
  have hcosN : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 0 ≤ Real.cos α :=
    fun α hα => Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2, Real.pi_pos]⟩
  -- Case A of `glueA`: the anchor branch (`cos α < 4 / 5`)
  have hA_lt : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), Real.cos α < 4 / 5 →
      |deriv (Work.OddCurve.LowSlope.glueA n ρ) α| ≤ Kb * (C₁ + 1) * ε * Real.sin α := by
    intro α hα hlt
    have hαIoo := hmemIoo α hα
    have hsin := hsinN α hα
    have hcos1 : Real.cos α < 1 := cos_lt_one_of_cos_lt α hαIoo hlt
    have hcosm1 : -1 < Real.cos α := neg_one_lt_cos_of_mem α hαIoo
    have hmem : Real.cos α ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hcosm1, hcos1⟩
    have hev : Work.OddCurve.LowSlope.glueA n ρ =ᶠ[𝓝 α]
        (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 2) + ρ (-(Real.cos β)) ^ (2 * n + 2) - 2) := by
      have hopen : {β : ℝ | Real.cos β < 4 / 5} ∈ 𝓝 α :=
        (isOpen_lt Real.continuous_cos continuous_const).mem_nhds hlt
      filter_upwards [hopen] with β hβ
      rw [Work.OddCurve.LowSlope.glueA_of_lt hβ]
    have hderiv : deriv (Work.OddCurve.LowSlope.glueA n ρ) α
        = deriv (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 2) + ρ (-(Real.cos β)) ^ (2 * n + 2) - 2) α :=
      hev.deriv_eq
    have hderiv2 : deriv (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 2)
          + ρ (-(Real.cos β)) ^ (2 * n + 2) - 2) α
        = deriv (fun u : ℝ => ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2) - 2) (Real.cos α)
          * (-Real.sin α) := by
      have hdF : DifferentiableAt ℝ
          (fun u : ℝ => ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2) - 2) (Real.cos α) :=
        ((contDiffOn_anchorCombo (2 * n + 2) (by omega) hρsm).differentiableOn
          (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hmem)
      have hcomp := deriv_comp (x := α) (h := Real.cos)
        (h₂ := fun u : ℝ => ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2) - 2)
        hdF Real.differentiableAt_cos
      rw [show (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 2) + ρ (-(Real.cos β)) ^ (2 * n + 2) - 2)
          = (fun u : ℝ => ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2) - 2) ∘ Real.cos from rfl]
      rw [hcomp, Real.deriv_cos]
      try ring
    have hbd : |deriv (fun u : ℝ => ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2) - 2) (Real.cos α)|
        ≤ ((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2) * (C₁ * ε) := by
      rw [deriv_anchorCombo (2 * n + 2) (by omega) hρsm hmem]
      rw [show 2 * n + 2 - 1 = 2 * n + 1 from by omega]
      have hcosnn : 0 ≤ Real.cos α :=
        Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2, Real.pi_pos]⟩
      have h1 : |ρ (Real.cos α)| ≤ 2 := hρ2 _ (by
        rw [abs_of_nonneg hcosnn]; exact hlt)
      have h2 : |ρ (-(Real.cos α))| ≤ 2 := hρ2 _ (by
        rw [abs_neg, abs_of_nonneg hcosnn]; exact hlt)
      have h3 : |deriv ρ (Real.cos α)| ≤ C₁ * ε := (hdev _ (by
        rw [abs_of_nonneg hcosnn]; exact hlt)).2.1
      have h4 : |deriv ρ (-(Real.cos α))| ≤ C₁ * ε := (hdev _ (by
        rw [abs_neg, abs_of_nonneg hcosnn]; exact hlt)).2.1
      have h5 : |ρ (Real.cos α)| ^ (2 * n + 1) ≤ (2 : ℝ) ^ (2 * n + 1) :=
        pow_le_pow_left₀ (abs_nonneg _) h1 _
      have h6 : |ρ (-(Real.cos α))| ^ (2 * n + 1) ≤ (2 : ℝ) ^ (2 * n + 1) :=
        pow_le_pow_left₀ (abs_nonneg _) h2 _
      have h8 : |ρ (Real.cos α) ^ (2 * n + 1) * deriv ρ (Real.cos α)|
          ≤ (2 : ℝ) ^ (2 * n + 1) * (C₁ * ε) := by
        rw [abs_mul, abs_pow]
        exact mul_le_mul h5 h3 (abs_nonneg _) (by positivity)
      have h9 : |ρ (-(Real.cos α)) ^ (2 * n + 1) * deriv ρ (-(Real.cos α))|
          ≤ (2 : ℝ) ^ (2 * n + 1) * (C₁ * ε) := by
        rw [abs_mul, abs_pow]
        exact mul_le_mul h6 h4 (abs_nonneg _) (by positivity)
      have h10 : |ρ (Real.cos α) ^ (2 * n + 1) * deriv ρ (Real.cos α)
            - ρ (-(Real.cos α)) ^ (2 * n + 1) * deriv ρ (-(Real.cos α))|
          ≤ 2 * ((2 : ℝ) ^ (2 * n + 1) * (C₁ * ε)) := by
        have hsub := abs_sub_le (ρ (Real.cos α) ^ (2 * n + 1) * deriv ρ (Real.cos α)) 0
          (ρ (-(Real.cos α)) ^ (2 * n + 1) * deriv ρ (-(Real.cos α)))
        rw [sub_zero, zero_sub, abs_neg] at hsub
        linarith
      have h11 : |((2 * n + 2 : ℕ) : ℝ) * (ρ (Real.cos α) ^ (2 * n + 1) * deriv ρ (Real.cos α)
            - ρ (-(Real.cos α)) ^ (2 * n + 1) * deriv ρ (-(Real.cos α)))|
          ≤ ((2 * n + 2 : ℕ) : ℝ) * (2 * ((2 : ℝ) ^ (2 * n + 1) * (C₁ * ε))) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ))]
        exact mul_le_mul_of_nonneg_left h10 (by positivity)
      have hexp2 : (2 : ℝ) ^ (2 * n + 2) = 2 * 2 ^ (2 * n + 1) := by
        rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]; ring
      calc |((2 * n + 2 : ℕ) : ℝ) * (ρ (Real.cos α) ^ (2 * n + 1) * deriv ρ (Real.cos α)
            - ρ (-(Real.cos α)) ^ (2 * n + 1) * deriv ρ (-(Real.cos α)))|
          ≤ ((2 * n + 2 : ℕ) : ℝ) * (2 * ((2 : ℝ) ^ (2 * n + 1) * (C₁ * ε))) := h11
        _ = ((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2) * (C₁ * ε) := by
            rw [hexp2]; ring
    calc |deriv (Work.OddCurve.LowSlope.glueA n ρ) α|
        = |deriv (fun u : ℝ => ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2) - 2) (Real.cos α)
            * (-Real.sin α)| := by rw [hderiv, hderiv2]
      _ = |deriv (fun u : ℝ => ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2) - 2) (Real.cos α)|
            * Real.sin α := by rw [abs_mul, abs_neg, abs_of_nonneg hsin]
      _ ≤ M0 * Real.sin α := by
          rw [hM0def]
          exact mul_le_mul_of_nonneg_right hbd hsin
      _ ≤ Kb * (C₁ + 1) * ε * Real.sin α := by
          have hKb1 : ((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2) ≤ Kb := by
            rw [hKbdef]
            have hA : (0:ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2) := by positivity
            have h1 : (1:ℝ) ≤ 11 * C₀ + 1 := by linarith
            have h2 : (0:ℝ) ≤ (6 * C₀ + 1) * (((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1)) :=
              by positivity
            have h3 := mul_le_mul_of_nonneg_right h1 hA
            linarith
          have h4 : C₁ * ε ≤ (C₁ + 1) * ε := by nlinarith [hε, hεnn]
          have h5 : M0 ≤ Kb * (C₁ + 1) * ε := by
            rw [hM0def]
            calc ((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2) * (C₁ * ε)
                ≤ Kb * (C₁ * ε) := mul_le_mul_of_nonneg_right hKb1 hC₁εnn
              _ ≤ Kb * ((C₁ + 1) * ε) := mul_le_mul_of_nonneg_left h4 hKbpos.le
              _ = Kb * (C₁ + 1) * ε := by ring
          calc M0 * Real.sin α
              ≤ (Kb * (C₁ + 1) * ε) * Real.sin α := mul_le_mul_of_nonneg_right h5 hsin
            _ = Kb * (C₁ + 1) * ε * Real.sin α := by ring
  -- Case B of `glueA`: the `deltaA`-form (`4 / 5 < cos α`)
  have hA_gt : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 4 / 5 < Real.cos α →
      |deriv (Work.OddCurve.LowSlope.glueA n ρ) α| ≤ Kb * (C₁ + 1) * ε * Real.sin α := by
    intro α hα hgt
    have hαIoo := hmemIoo α hα
    have hsin := hsinN α hα
    have hcosmem : Real.cos α ∈ Set.Icc (4 / 5 : ℝ) 1 := ⟨le_of_lt hgt, Real.cos_le_one α⟩
    have hcospos : 0 < Real.cos α := by linarith [hgt]
    have hev : Work.OddCurve.LowSlope.glueA n ρ =ᶠ[𝓝 α]
        (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ)
          (Real.cos β) / Real.cos β ^ 2) := by
      have hopen : {β : ℝ | 4 / 5 < Real.cos β} ∈ 𝓝 α :=
        (isOpen_lt continuous_const Real.continuous_cos).mem_nhds hgt
      filter_upwards [hopen] with β hβ
      exact glueA_eq_deltaA n hn hρsm (by linarith [hβ]) (ne_of_gt hβ)
    have hderiv : deriv (Work.OddCurve.LowSlope.glueA n ρ) α
        = deriv (fun β : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaA n ρ) (Real.cos β) / Real.cos β ^ 2) α :=
      hev.deriv_eq
    have hderiv2 : deriv (fun β : ℝ => 2 * Work.OddRadon.radonInverse n
          (Work.OddCurve.LowSlope.deltaA n ρ) (Real.cos β) / Real.cos β ^ 2) α
        = deriv (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaA n ρ) u / u ^ 2) (Real.cos α) * (-Real.sin α) := by
      have hdF : DifferentiableAt ℝ (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
          (Work.OddCurve.LowSlope.deltaA n ρ) u / u ^ 2) (Real.cos α) := by
        have hnum : DifferentiableAt ℝ (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaA n ρ) u) (Real.cos α) :=
          (differentiableAt_const (c := (2:ℝ))).mul (hbA3 _ hcosmem)
        have hden : DifferentiableAt ℝ (fun u : ℝ => u ^ 2) (Real.cos α) :=
          differentiableAt_id.pow 2
        have hfun : (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaA n ρ) u / u ^ 2)
            = (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
                (Work.OddCurve.LowSlope.deltaA n ρ) u) / (fun u : ℝ => u ^ 2) := rfl
        rw [hfun]
        exact hnum.div hden (pow_ne_zero 2 (ne_of_gt hcospos))
      have hcomp := deriv_comp (x := α) (h := Real.cos)
        (h₂ := fun u : ℝ => 2 * Work.OddRadon.radonInverse n
          (Work.OddCurve.LowSlope.deltaA n ρ) u / u ^ 2) hdF Real.differentiableAt_cos
      rw [show (fun β : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaA n ρ) (Real.cos β) / Real.cos β ^ 2)
          = (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
              (Work.OddCurve.LowSlope.deltaA n ρ) u / u ^ 2) ∘ Real.cos from rfl]
      rw [hcomp, Real.deriv_cos]
      try ring
    have hbd : |deriv (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
          (Work.OddCurve.LowSlope.deltaA n ρ) u / u ^ 2) (Real.cos α)|
        ≤ 11 * (C₀ * M0) := by
      have hQ0 : (0 : ℝ) ≤ C₀ * M0 := mul_nonneg hC₀pos.le hMA
      rw [deriv_two_mul_div_sq (ne_of_gt hcospos) (hbA3 _ hcosmem)]
      have h1 := hbA1 _ hcosmem
      have h2 := hbA2 _ hcosmem
      have hc2 : (4 / 5 : ℝ) ^ 2 ≤ Real.cos α ^ 2 :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4 / 5) hgt.le 2
      have hc3 : (4 / 5 : ℝ) ^ 3 ≤ Real.cos α ^ 3 :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4 / 5) hgt.le 3
      have hinv2 : (0 : ℝ) ≤ (Real.cos α ^ 2)⁻¹ := by positivity
      have hinv3 : (0 : ℝ) ≤ (Real.cos α ^ 3)⁻¹ := by positivity
      have hF : 2 * |deriv (fun v : ℝ => Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaA n ρ) v) (Real.cos α)| / Real.cos α ^ 2
          ≤ 25 / 8 * (C₀ * M0) := by
        have hm : 2 * |deriv (fun v : ℝ => Work.OddRadon.radonInverse n
              (Work.OddCurve.LowSlope.deltaA n ρ) v) (Real.cos α)| ≤ 2 * (C₀ * M0) := by
          linarith [h2]
        have hstep : 2 * |deriv (fun v : ℝ => Work.OddRadon.radonInverse n
              (Work.OddCurve.LowSlope.deltaA n ρ) v) (Real.cos α)| / Real.cos α ^ 2
            ≤ 2 * (C₀ * M0) / Real.cos α ^ 2 := mul_le_mul_of_nonneg_right hm hinv2
        have hstep2 : 2 * (C₀ * M0) / Real.cos α ^ 2
            ≤ 2 * (C₀ * M0) / (4 / 5 : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hc2
        have hstep3 : 2 * (C₀ * M0) / (4 / 5 : ℝ) ^ 2 = 25 / 8 * (C₀ * M0) := by ring
        linarith
      have hR : 4 * |Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ)
            (Real.cos α)| / Real.cos α ^ 3 ≤ 125 / 16 * (C₀ * M0) := by
        have hm : 4 * |Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ)
              (Real.cos α)| ≤ 4 * (C₀ * M0) := by linarith [h1]
        have hstep : 4 * |Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ)
              (Real.cos α)| / Real.cos α ^ 3 ≤ 4 * (C₀ * M0) / Real.cos α ^ 3 :=
          mul_le_mul_of_nonneg_right hm hinv3
        have hstep2 : 4 * (C₀ * M0) / Real.cos α ^ 3
            ≤ 4 * (C₀ * M0) / (4 / 5 : ℝ) ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hc3
        have hstep3 : 4 * (C₀ * M0) / (4 / 5 : ℝ) ^ 3 = 125 / 16 * (C₀ * M0) := by ring
        linarith
      have hA' : |2 * deriv (fun v : ℝ => Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaA n ρ) v) (Real.cos α) / Real.cos α ^ 2|
          ≤ 25 / 8 * (C₀ * M0) := by
        rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_pos (by positivity : (0 : ℝ) < Real.cos α ^ 2)]
        exact hF
      have hB' : |4 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ)
            (Real.cos α) / Real.cos α ^ 3| ≤ 125 / 16 * (C₀ * M0) := by
        rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
          abs_of_pos (by positivity : (0 : ℝ) < Real.cos α ^ 3)]
        exact hR
      have habs := abs_sub_le (2 * deriv (fun v : ℝ => Work.OddRadon.radonInverse n
          (Work.OddCurve.LowSlope.deltaA n ρ) v) (Real.cos α) / Real.cos α ^ 2) 0
        (4 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ)
          (Real.cos α) / Real.cos α ^ 3)
      rw [sub_zero, zero_sub, abs_neg] at habs
      refine (habs.trans (add_le_add hA' hB')).trans ?_
      nlinarith [hQ0]
    calc |deriv (Work.OddCurve.LowSlope.glueA n ρ) α|
        = |deriv (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaA n ρ) u / u ^ 2) (Real.cos α) * (-Real.sin α)| := by
          rw [hderiv, hderiv2]
      _ = |deriv (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaA n ρ) u / u ^ 2) (Real.cos α)| * Real.sin α := by
          rw [abs_mul, abs_neg, abs_of_nonneg hsin]
      _ ≤ (11 * (C₀ * M0)) * Real.sin α := mul_le_mul_of_nonneg_right hbd hsin
      _ ≤ Kb * (C₁ + 1) * ε * Real.sin α := by
          have hKb : 11 * (C₀ * M0) ≤ Kb * (C₁ + 1) * ε := by
            have hKb1 : 11 * C₀ * (((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2)) ≤ Kb := by
              rw [hKbdef]
              have hA : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2) := by positivity
              have h1 : 11 * C₀ ≤ 11 * C₀ + 1 := by linarith
              have h2 : (0 : ℝ) ≤ (6 * C₀ + 1)
                  * (((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1)) := by positivity
              have h3 := mul_le_mul_of_nonneg_right h1 hA
              linarith
            have h4 : C₁ * ε ≤ (C₁ + 1) * ε := by nlinarith [hε, hεnn]
            rw [hM0def]
            calc 11 * (C₀ * (((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2) * (C₁ * ε)))
                = (11 * C₀ * (((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2))) * (C₁ * ε) := by
                  ring
              _ ≤ Kb * (C₁ * ε) := mul_le_mul_of_nonneg_right hKb1 hC₁εnn
              _ ≤ Kb * ((C₁ + 1) * ε) := mul_le_mul_of_nonneg_left h4 hKbpos.le
              _ = Kb * (C₁ + 1) * ε := by ring
          calc (11 * (C₀ * M0)) * Real.sin α
              ≤ (Kb * (C₁ + 1) * ε) * Real.sin α := mul_le_mul_of_nonneg_right hKb hsin
            _ = Kb * (C₁ + 1) * ε * Real.sin α := by ring
  -- The two branches are joined at the single junction point `cos α = 4 / 5`
  have hbndA : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv (Work.OddCurve.LowSlope.glueA n ρ) α| ≤ Kb * (C₁ + 1) * ε * Real.sin α := by
    intro α hα
    rcases lt_trichotomy (Real.cos α) (4 / 5) with hlt | heq | hgt
    · exact hA_lt α hα hlt
    · -- the junction: squeeze from the left
      have hαpos : 0 < α := by
        rcases lt_or_eq_of_le hα.1 with h0 | h0
        · exact h0
        · exfalso
          have h1 : Real.cos α = 1 := by rw [← h0]; exact Real.cos_zero
          rw [h1] at heq
          norm_num at heq
      have hcont : ContinuousAt (fun β : ℝ => Kb * (C₁ + 1) * ε * Real.sin β
          - |deriv (Work.OddCurve.LowSlope.glueA n ρ) β|) α := by
        have hd : ContinuousAt (deriv (Work.OddCurve.LowSlope.glueA n ρ)) α :=
          (hglueAsm.continuousOn_deriv_of_isOpen isOpen_Ioo (WithTop.coe_le_coe.mpr le_top)).continuousAt
            (isOpen_Ioo.mem_nhds (hmemIoo α hα))
        exact (continuousAt_const.mul Real.continuous_sin.continuousAt).sub hd.abs
      have hev : ∀ᶠ β : ℝ in 𝓝[<] α, 0 ≤ Kb * (C₁ + 1) * ε * Real.sin β
          - |deriv (Work.OddCurve.LowSlope.glueA n ρ) β| := by
        filter_upwards [Ioo_mem_nhdsLT hαpos] with β hβ
        have hβIcc : β ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
          ⟨le_of_lt hβ.1, le_of_lt (lt_of_lt_of_le hβ.2 hα.2)⟩
        have hcosβ : Real.cos α < Real.cos β :=
          Real.strictAntiOn_cos ⟨hβIcc.1, by linarith [hβIcc.2, Real.pi_pos]⟩
            ⟨hα.1, by linarith [hα.2, Real.pi_pos]⟩ hβ.2
        exact sub_nonneg.mpr (hA_gt β hβIcc (by rw [← heq]; exact hcosβ))
      haveI : (𝓝[<] α).NeBot := nhdsLT_neBot α
      exact sub_nonneg.mp (ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev)
    · exact hA_gt α hα hgt
  -- Case A of `glueB`: the anchor branch (`cos α < 4 / 5`)
  have hB_lt : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), Real.cos α < 4 / 5 →
      |deriv (Work.OddCurve.LowSlope.glueB n ρ) α| ≤ Kb * (C₁ + 1) * ε * Real.sin α := by
    intro α hα hlt
    have hαIoo := hmemIoo α hα
    have hsin := hsinN α hα
    have hcosnn := hcosN α hα
    have hcos1 : Real.cos α < 1 := cos_lt_one_of_cos_lt α hαIoo hlt
    have hcosm1 : -1 < Real.cos α := neg_one_lt_cos_of_mem α hαIoo
    have hmem : Real.cos α ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hcosm1, hcos1⟩
    have hev : Work.OddCurve.LowSlope.glueB n ρ =ᶠ[𝓝 α]
        (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 1) - ρ (-(Real.cos β)) ^ (2 * n + 1)) := by
      have hopen : {β : ℝ | Real.cos β < 4 / 5} ∈ 𝓝 α :=
        (isOpen_lt Real.continuous_cos continuous_const).mem_nhds hlt
      filter_upwards [hopen] with β hβ
      exact Work.OddCurve.LowSlope.glueB_of_lt hβ
    have hderiv : deriv (Work.OddCurve.LowSlope.glueB n ρ) α
        = deriv (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 1)
            - ρ (-(Real.cos β)) ^ (2 * n + 1)) α :=
      hev.deriv_eq
    have hderiv2 : deriv (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 1)
          - ρ (-(Real.cos β)) ^ (2 * n + 1)) α
        = deriv (fun u : ℝ => ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)) (Real.cos α)
          * (-Real.sin α) := by
      have hdF : DifferentiableAt ℝ
          (fun u : ℝ => ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)) (Real.cos α) :=
        ((contDiffOn_anchorDiff (2 * n + 1) hρsm).differentiableOn
          (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hmem)
      have hcomp := deriv_comp (x := α) (h := Real.cos)
        (h₂ := fun u : ℝ => ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1))
        hdF Real.differentiableAt_cos
      rw [show (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 1) - ρ (-(Real.cos β)) ^ (2 * n + 1))
          = (fun u : ℝ => ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)) ∘ Real.cos from rfl]
      rw [hcomp, Real.deriv_cos]
      try ring
    have hbd : |deriv (fun u : ℝ => ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)) (Real.cos α)|
        ≤ M1 := by
      rw [deriv_anchorDiff (2 * n + 1) (by omega) hρsm hmem]
      rw [show 2 * n + 1 - 1 = 2 * n from by omega]
      have h1 : |ρ (Real.cos α)| ≤ 2 := hρ2 _ (by rw [abs_of_nonneg hcosnn]; exact hlt)
      have h2 : |ρ (-(Real.cos α))| ≤ 2 := hρ2 _ (by
        rw [abs_neg, abs_of_nonneg hcosnn]; exact hlt)
      have h3 : |deriv ρ (Real.cos α)| ≤ C₁ * ε :=
        (hdev _ (by rw [abs_of_nonneg hcosnn]; exact hlt)).2.1
      have h4 : |deriv ρ (-(Real.cos α))| ≤ C₁ * ε :=
        (hdev _ (by rw [abs_neg, abs_of_nonneg hcosnn]; exact hlt)).2.1
      have h5 : |ρ (Real.cos α)| ^ (2 * n) ≤ (2 : ℝ) ^ (2 * n) :=
        pow_le_pow_left₀ (abs_nonneg _) h1 _
      have h6 : |ρ (-(Real.cos α))| ^ (2 * n) ≤ (2 : ℝ) ^ (2 * n) :=
        pow_le_pow_left₀ (abs_nonneg _) h2 _
      have h7 : |ρ (Real.cos α) ^ (2 * n) * deriv ρ (Real.cos α)|
          ≤ (2 : ℝ) ^ (2 * n) * (C₁ * ε) := by
        rw [abs_mul, abs_pow]
        exact mul_le_mul h5 h3 (abs_nonneg _) (by positivity)
      have h8 : |ρ (-(Real.cos α)) ^ (2 * n) * deriv ρ (-(Real.cos α))|
          ≤ (2 : ℝ) ^ (2 * n) * (C₁ * ε) := by
        rw [abs_mul, abs_pow]
        exact mul_le_mul h6 h4 (abs_nonneg _) (by positivity)
      have hexp : (2 : ℝ) ^ (2 * n + 1) = 2 * 2 ^ (2 * n) := by
        rw [pow_succ]; ring
      have h9 : |((2 * n + 1 : ℕ) : ℝ) * (ρ (Real.cos α) ^ (2 * n) * deriv ρ (Real.cos α)
            + ρ (-(Real.cos α)) ^ (2 * n) * deriv ρ (-(Real.cos α)))|
          ≤ ((2 * n + 1 : ℕ) : ℝ) * (2 * (2 ^ (2 * n) * (C₁ * ε))) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ))]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (abs_add_le _ _).trans ?_
        linarith [h7, h8]
      rw [hM1def]
      calc |((2 * n + 1 : ℕ) : ℝ) * (ρ (Real.cos α) ^ (2 * n) * deriv ρ (Real.cos α)
            + ρ (-(Real.cos α)) ^ (2 * n) * deriv ρ (-(Real.cos α)))|
          ≤ ((2 * n + 1 : ℕ) : ℝ) * (2 * (2 ^ (2 * n) * (C₁ * ε))) := h9
        _ = ((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1) * (C₁ * ε) := by
            rw [hexp]; ring
    calc |deriv (Work.OddCurve.LowSlope.glueB n ρ) α|
        = |deriv (fun u : ℝ => ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)) (Real.cos α)
            * (-Real.sin α)| := by rw [hderiv, hderiv2]
      _ = |deriv (fun u : ℝ => ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)) (Real.cos α)|
            * Real.sin α := by rw [abs_mul, abs_neg, abs_of_nonneg hsin]
      _ ≤ M1 * Real.sin α := mul_le_mul_of_nonneg_right hbd hsin
      _ ≤ Kb * (C₁ + 1) * ε * Real.sin α := by
          have hKb1 : ((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1) ≤ Kb := by
            rw [hKbdef]
            have hA : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1) := by positivity
            have h1 : (1 : ℝ) ≤ 6 * C₀ + 1 := by linarith
            have h2 : (0 : ℝ) ≤ (11 * C₀ + 1)
                * (((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2)) := by positivity
            have h3 := mul_le_mul_of_nonneg_right h1 hA
            linarith
          have h4 : C₁ * ε ≤ (C₁ + 1) * ε := by nlinarith [hε, hεnn]
          have h5 : M1 ≤ Kb * (C₁ + 1) * ε := by
            rw [hM1def]
            calc ((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1) * (C₁ * ε)
                ≤ Kb * (C₁ * ε) := mul_le_mul_of_nonneg_right hKb1 hC₁εnn
              _ ≤ Kb * ((C₁ + 1) * ε) := mul_le_mul_of_nonneg_left h4 hKbpos.le
              _ = Kb * (C₁ + 1) * ε := by ring
          calc M1 * Real.sin α
              ≤ (Kb * (C₁ + 1) * ε) * Real.sin α := mul_le_mul_of_nonneg_right h5 hsin
            _ = Kb * (C₁ + 1) * ε * Real.sin α := by ring
  -- Case B of `glueB`: the `deltaB`-form (`4 / 5 ≤ cos α`)
  have hB_ge : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 4 / 5 ≤ Real.cos α →
      |deriv (Work.OddCurve.LowSlope.glueB n ρ) α| ≤ Kb * (C₁ + 1) * ε * Real.sin α := by
    intro α hα hge
    have hαIoo := hmemIoo α hα
    have hsin := hsinN α hα
    have hcosmem : Real.cos α ∈ Set.Icc (4 / 5 : ℝ) 1 := ⟨hge, Real.cos_le_one α⟩
    have hcospos : 0 < Real.cos α := by linarith [hge]
    have hev : Work.OddCurve.LowSlope.glueB n ρ =ᶠ[𝓝 α]
        (fun β : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
          (Real.cos β) / Real.cos β) := by
      have hopen : {β : ℝ | 0 < Real.cos β} ∈ 𝓝 α :=
        (isOpen_lt continuous_const Real.continuous_cos).mem_nhds hcospos
      filter_upwards [hopen] with β hβ
      exact glueB_eq_deltaB n hn hρsm hβ
    have hderiv : deriv (Work.OddCurve.LowSlope.glueB n ρ) α
        = deriv (fun β : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaB n ρ) (Real.cos β) / Real.cos β) α :=
      hev.deriv_eq
    have hderiv2 : deriv (fun β : ℝ => 2 * Work.OddRadon.radonInverse n
          (Work.OddCurve.LowSlope.deltaB n ρ) (Real.cos β) / Real.cos β) α
        = deriv (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaB n ρ) u / u) (Real.cos α) * (-Real.sin α) := by
      have hdF : DifferentiableAt ℝ (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
          (Work.OddCurve.LowSlope.deltaB n ρ) u / u) (Real.cos α) := by
        have hnum : DifferentiableAt ℝ (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaB n ρ) u) (Real.cos α) :=
          (differentiableAt_const (c := (2:ℝ))).mul (hbB3 _ hcosmem)
        have hfun : (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaB n ρ) u / u)
            = (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
                (Work.OddCurve.LowSlope.deltaB n ρ) u) / (fun u : ℝ => u) := rfl
        rw [hfun]
        exact hnum.div differentiableAt_id (ne_of_gt hcospos)
      have hcomp := deriv_comp (x := α) (h := Real.cos)
        (h₂ := fun u : ℝ => 2 * Work.OddRadon.radonInverse n
          (Work.OddCurve.LowSlope.deltaB n ρ) u / u) hdF Real.differentiableAt_cos
      rw [show (fun β : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaB n ρ) (Real.cos β) / Real.cos β)
          = (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
              (Work.OddCurve.LowSlope.deltaB n ρ) u / u) ∘ Real.cos from rfl]
      rw [hcomp, Real.deriv_cos]
      try ring
    have hbd : |deriv (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
          (Work.OddCurve.LowSlope.deltaB n ρ) u / u) (Real.cos α)| ≤ 6 * (C₀ * M1) := by
      have hQ0 : (0 : ℝ) ≤ C₀ * M1 := mul_nonneg hC₀pos.le hMB
      rw [deriv_two_mul_div (ne_of_gt hcospos) (hbB3 _ hcosmem)]
      have h1 := hbB1 _ hcosmem
      have h2 := hbB2 _ hcosmem
      have hc1 : (4 / 5 : ℝ) ≤ Real.cos α := hge
      have hc2 : (4 / 5 : ℝ) ^ 2 ≤ Real.cos α ^ 2 :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4 / 5) hge 2
      have hinv1 : (0 : ℝ) ≤ (Real.cos α)⁻¹ := by positivity
      have hinv2 : (0 : ℝ) ≤ (Real.cos α ^ 2)⁻¹ := by positivity
      have hF : 2 * |deriv (fun v : ℝ => Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaB n ρ) v) (Real.cos α)| / Real.cos α
          ≤ 5 / 2 * (C₀ * M1) := by
        have hm : 2 * |deriv (fun v : ℝ => Work.OddRadon.radonInverse n
              (Work.OddCurve.LowSlope.deltaB n ρ) v) (Real.cos α)| ≤ 2 * (C₀ * M1) := by
          linarith [h2]
        have hstep : 2 * |deriv (fun v : ℝ => Work.OddRadon.radonInverse n
              (Work.OddCurve.LowSlope.deltaB n ρ) v) (Real.cos α)| / Real.cos α
            ≤ 2 * (C₀ * M1) / Real.cos α := mul_le_mul_of_nonneg_right hm hinv1
        have hstep2 : 2 * (C₀ * M1) / Real.cos α ≤ 2 * (C₀ * M1) / (4 / 5 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hc1
        have hstep3 : 2 * (C₀ * M1) / (4 / 5 : ℝ) = 5 / 2 * (C₀ * M1) := by ring
        linarith
      have hR : 2 * |Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
            (Real.cos α)| / Real.cos α ^ 2 ≤ 25 / 8 * (C₀ * M1) := by
        have hm : 2 * |Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
              (Real.cos α)| ≤ 2 * (C₀ * M1) := by linarith [h1]
        have hstep : 2 * |Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
              (Real.cos α)| / Real.cos α ^ 2 ≤ 2 * (C₀ * M1) / Real.cos α ^ 2 :=
          mul_le_mul_of_nonneg_right hm hinv2
        have hstep2 : 2 * (C₀ * M1) / Real.cos α ^ 2
            ≤ 2 * (C₀ * M1) / (4 / 5 : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hc2
        have hstep3 : 2 * (C₀ * M1) / (4 / 5 : ℝ) ^ 2 = 25 / 8 * (C₀ * M1) := by ring
        linarith
      have hA' : |2 * deriv (fun v : ℝ => Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaB n ρ) v) (Real.cos α) / Real.cos α|
          ≤ 5 / 2 * (C₀ * M1) := by
        rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_pos hcospos]
        exact hF
      have hB' : |2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
            (Real.cos α) / Real.cos α ^ 2| ≤ 25 / 8 * (C₀ * M1) := by
        rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_pos (by positivity : (0 : ℝ) < Real.cos α ^ 2)]
        exact hR
      have habs := abs_sub_le (2 * deriv (fun v : ℝ => Work.OddRadon.radonInverse n
          (Work.OddCurve.LowSlope.deltaB n ρ) v) (Real.cos α) / Real.cos α) 0
        (2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaB n ρ)
          (Real.cos α) / Real.cos α ^ 2)
      rw [sub_zero, zero_sub, abs_neg] at habs
      refine (habs.trans (add_le_add hA' hB')).trans ?_
      nlinarith [hQ0]
    calc |deriv (Work.OddCurve.LowSlope.glueB n ρ) α|
        = |deriv (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaB n ρ) u / u) (Real.cos α) * (-Real.sin α)| := by
          rw [hderiv, hderiv2]
      _ = |deriv (fun u : ℝ => 2 * Work.OddRadon.radonInverse n
            (Work.OddCurve.LowSlope.deltaB n ρ) u / u) (Real.cos α)| * Real.sin α := by
          rw [abs_mul, abs_neg, abs_of_nonneg hsin]
      _ ≤ (6 * (C₀ * M1)) * Real.sin α := mul_le_mul_of_nonneg_right hbd hsin
      _ ≤ Kb * (C₁ + 1) * ε * Real.sin α := by
          have hKb : 6 * (C₀ * M1) ≤ Kb * (C₁ + 1) * ε := by
            have hKb1 : 6 * C₀ * (((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1)) ≤ Kb := by
              rw [hKbdef]
              have hA : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1) := by positivity
              have h1 : 6 * C₀ ≤ 6 * C₀ + 1 := by linarith
              have h2 : (0 : ℝ) ≤ (11 * C₀ + 1)
                  * (((2 * n + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 2)) := by positivity
              have h3 := mul_le_mul_of_nonneg_right h1 hA
              linarith
            have h4 : C₁ * ε ≤ (C₁ + 1) * ε := by nlinarith [hε, hεnn]
            rw [hM1def]
            calc 6 * (C₀ * (((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1) * (C₁ * ε)))
                = (6 * C₀ * (((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n + 1))) * (C₁ * ε) := by
                  ring
              _ ≤ Kb * (C₁ * ε) := mul_le_mul_of_nonneg_right hKb1 hC₁εnn
              _ ≤ Kb * ((C₁ + 1) * ε) := mul_le_mul_of_nonneg_left h4 hKbpos.le
              _ = Kb * (C₁ + 1) * ε := by ring
          calc (6 * (C₀ * M1)) * Real.sin α
              ≤ (Kb * (C₁ + 1) * ε) * Real.sin α := mul_le_mul_of_nonneg_right hKb hsin
            _ = Kb * (C₁ + 1) * ε * Real.sin α := by ring
  have hbndB : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv (Work.OddCurve.LowSlope.glueB n ρ) α| ≤ Kb * (C₁ + 1) * ε * Real.sin α := by
    intro α hα
    rcases lt_or_ge (Real.cos α) (4 / 5) with hlt | hge
    · exact hB_lt α hα hlt
    · exact hB_ge α hα hge
  exact ⟨hglueAsm, hglueBsm, fun α hα => ⟨hbndA α hα, hbndB α hα⟩⟩

end

end Work.OddVolterra.Free
