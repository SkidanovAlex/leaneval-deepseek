import Mathlib
import Submission.Work.OddCurve.LowSlope.waistData
import Submission.Work.OddCurve.LowSlope.waistRadial_eq_one
import Submission.Work.OddCurve.LowSlope.exists_radialFunction_of_strictConcaveProfile
import Submission.Work.OddEnvelope.Main

/-!
# The radial function of the anchor profile, and its data on the waist

For an envelope curve `(h, X, Y)` of the odd case (`Work.OddEnvelope.IsEnvelopeCurve`) the
profile `f = envelopeProfile h X Y` is strictly concave, positive inside, and vanishes at `±1`,
so it has a radial function `ρ` (`exists_radialFunction_of_strictConcaveProfile`).  Because the
profile *is* the unit semicircle on the waist `(-tStar, tStar)`, that radial function equals `1`
there (`waistRadial_eq_one`), and consequently both Radon data of the anchor coincide with the
ball's on `(0, tStar]` (`radonPhi_eq_ballPhiData_of_waist`, `radonPsi_eq_zero_of_waist`).

This file packages these facts in the form the reconstruction needs.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The radial function of the anchor profile**, with the waist identity. -/
theorem exists_radialFunction_anchor {h X Y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y) :
    ∃ ρ : ℝ → ℝ,
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) ∧ ρ 0 = 1 ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1) ∧
      StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) ∧
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1,
        ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)) ∧
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * u ∈ Set.Ioo (-1 : ℝ) 1) ∧
      (∀ u : ℝ, |u| < Work.OddEnvelope.tStar → ρ u = 1) := by
  obtain ⟨ρ, hρpos, hρsm, hρmono, hgraph, hρ0⟩ :=
    exists_radialFunction_of_strictConcaveProfile (Work.OddEnvelope.envelopeProfile h X Y)
      Work.OddEnvelope.envelopeProfile_zero (Work.OddEnvelope.continuousOn_envelopeProfile' H)
      Work.OddEnvelope.envelopeProfile_left_end Work.OddEnvelope.envelopeProfile_right_end
      (fun t ht => Work.OddEnvelope.envelopeProfile_pos H ht)
      ((Work.OddEnvelope.strictConcaveOn_envelopeProfile H).subset Set.Ioo_subset_Icc_self
        (convex_Ioo (-1 : ℝ) 1))
      (Work.OddEnvelope.envelopeProfile_contDiffOn H)
  -- the radial point stays inside `[-1,1]`
  have hbound : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * u ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro u hu
    have hspos : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.mpr (by nlinarith [hu.1, hu.2])
    have hfu : Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) = ρ u * Real.sqrt (1 - u ^ 2) :=
      (hgraph u hu).symm
    have hne : Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) ≠ 0 := by
      rw [hfu]; exact ne_of_gt (mul_pos (hρpos u hu) hspos)
    have hsupp : Function.support (Work.OddEnvelope.envelopeProfile h X Y) ⊆ Set.Icc (-1 : ℝ) 1 :=
      Work.OddEnvelope.envelopeProfile_support
    have hIcc : ρ u * u ∈ Set.Icc (-1 : ℝ) 1 := hsupp (Function.mem_support.mpr hne)
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hIcc.1 with hq | hq
      · exfalso
        rw [← hq, Work.OddEnvelope.envelopeProfile_left_end] at hfu
        exact absurd (mul_pos (hρpos u hu) hspos) (by rw [hfu]; norm_num)
      · exact hq
    · rcases eq_or_lt_of_le hIcc.2 with hq | hq
      · exfalso
        rw [hq, Work.OddEnvelope.envelopeProfile_right_end] at hfu
        exact absurd (mul_pos (hρpos u hu) hspos) (by rw [hfu]; norm_num)
      · exact hq
  exact ⟨ρ, hρpos, hρ0, hρsm, hρmono, hgraph, hbound,
    fun u hu => waistRadial_eq_one H hρpos hρ0 hgraph hbound hu⟩

/-- **The first datum of the anchor on the waist is the ball's.** -/
theorem radonPhi_anchor_waist {n : ℕ} {h X Y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y) :
    ∃ ρ : ℝ → ℝ, (∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) ∧ ρ 0 = 1 ∧
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1,
        ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)) ∧
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * u ∈ Set.Ioo (-1 : ℝ) 1) ∧
      (∀ c : ℝ, 0 < c → c < Work.OddEnvelope.tStar → radonPhi n ρ c = ballPhiData n c) ∧
      (∀ c : ℝ, 0 < c → c < Work.OddEnvelope.tStar → radonPsi n ρ c = 0) := by
  obtain ⟨ρ, hρpos, hρ0, -, -, hgraph, hbound, hwaist⟩ := exists_radialFunction_anchor H
  exact ⟨ρ, hρpos, hρ0, hgraph, hbound,
    fun c hc hcb => radonPhi_eq_ballPhiData_of_waist (fun u hu => hwaist u hu) hc hcb,
    fun c hc hcb => radonPsi_eq_zero_of_waist (fun u hu => hwaist u hu) hc hcb⟩

end

end Work.OddCurve.LowSlope
