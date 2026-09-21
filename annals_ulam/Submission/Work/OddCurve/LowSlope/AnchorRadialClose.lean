import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueIdent
import Submission.Work.OddCurve.LowSlope.Extension
import Submission.Work.OddCurve.LowSlope.chord_eq_radial
import Submission.Work.OddCurve.LowSlope.anchorData
import Submission.Work.OddCurve.LowSlope.step3_anchor_data

/-!
# Closeness of the anchor's radial function and vanishing of the deviations on the waist

Two consequences of the `C²`-closeness of the anchor's chord curve to the semicircle, used by the
low-slope reconstruction:

* `radialDev_le` — where the cutting line is centred (`h s = 0`), the chord endpoint `Y s` is the
  radial point `ρ c · c`, `c = (√(1+s²))⁻¹`, so `|Y s - profileX s| ≤ 1/100` gives
  `|ρ c - 1| ≤ 1 / (100 c)`;
* `GlueA_eq_zero_of_lt_tStar`, `GlueB_eq_zero_of_lt_tStar` — on the waist `|cos α| < tStar` the
  anchor's radial function is `1` (`waistRadial_eq_one`), hence the two deviations `GlueA`,
  `GlueB` of the two-power system vanish there.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- `tStar = profileX (1 - τ) < 4/5`. -/
lemma tStar_lt_four_fifths : Work.OddEnvelope.tStar < 4 / 5 := by
  have h : Work.OddEnvelope.tStar = (Real.sqrt (1 + (9 / 10 : ℝ) ^ 2))⁻¹ := by
    simp only [Work.OddEnvelope.tStar, Work.OddEnvelope.profileX, Work.OddEnvelope.tau]
    norm_num
  rw [h, inv_lt_iff_one_lt_mul₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 1 + (9/10)^2))]
  have h2 : Real.sqrt (1 + (9 / 10 : ℝ) ^ 2) ^ 2 = 1 + (9 / 10 : ℝ) ^ 2 :=
    Real.sq_sqrt (by norm_num)
  have h3 : (0:ℝ) ≤ Real.sqrt (1 + (9 / 10 : ℝ) ^ 2) := Real.sqrt_nonneg _
  nlinarith [h2, h3, sq_nonneg (Real.sqrt (1 + (9 / 10 : ℝ) ^ 2) - 5 / 4)]

/-- **Closeness of the anchor's radial function to `1`**, where the cutting line is centred. -/
theorem radialDev_le {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    (hcY : CloseToProfileX Y) {s : ℝ} (hs : 0 < s) (hz : h s = 0) :
    |ρ ((Real.sqrt (1 + s ^ 2))⁻¹) - 1|
      ≤ 1 / (100 * (Real.sqrt (1 + s ^ 2))⁻¹) := by
  obtain ⟨hY, -⟩ := envelope_chord_eq_radial H hs hz hpos hgraph
  have hY' : Y s = ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) := hY
  have h1 := (hcY s hs).1
  rw [Work.OddEnvelope.profileX, one_div] at h1
  rw [hY'] at h1
  have hcpos : 0 < (Real.sqrt (1 + s ^ 2))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have key : |ρ ((Real.sqrt (1 + s ^ 2))⁻¹) - 1| * ((Real.sqrt (1 + s ^ 2))⁻¹)
      = |ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹)
          - ((Real.sqrt (1 + s ^ 2))⁻¹)| := by
    rw [show ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹)
          - ((Real.sqrt (1 + s ^ 2))⁻¹)
        = (ρ ((Real.sqrt (1 + s ^ 2))⁻¹) - 1) * ((Real.sqrt (1 + s ^ 2))⁻¹) by ring,
      abs_mul, abs_of_pos hcpos]
  have h2 : |ρ ((Real.sqrt (1 + s ^ 2))⁻¹) - 1| * ((Real.sqrt (1 + s ^ 2))⁻¹) ≤ 1 / 100 := by
    rw [key]; exact h1
  rw [le_div_iff₀ (by positivity)]
  linarith [h2]

/-- **The first deviation vanishes on the waist.**  For `|cos α| < tStar` the anchor's radial
function is `1` (`waistRadial_eq_one`), so the two-power combination `GlueA` is `0`. -/
theorem GlueA_eq_zero_of_lt_tStar (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ} {α : ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hρone : ∀ u : ℝ, |u| < Work.OddEnvelope.tStar → ρ u = 1)
    (hc0 : 0 < Real.cos α) (hc : |Real.cos α| < Work.OddEnvelope.tStar) :
    GlueA n ρ α = 0 := by
  have hlt : Real.cos α < 4 / 5 := lt_trans (abs_lt.mp hc).2 tStar_lt_four_fifths
  rw [GlueA_eq n hn hρ hc0 hlt, hρone _ hc, hρone _ (by rwa [abs_neg])]
  norm_num

/-- **The second deviation vanishes on the waist.** -/
theorem GlueB_eq_zero_of_lt_tStar (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ} {α : ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hρone : ∀ u : ℝ, |u| < Work.OddEnvelope.tStar → ρ u = 1)
    (hc0 : 0 < Real.cos α) (hc : |Real.cos α| < Work.OddEnvelope.tStar) :
    GlueB n ρ α = 0 := by
  have hlt : Real.cos α < 4 / 5 := lt_trans (abs_lt.mp hc).2 tStar_lt_four_fifths
  rw [GlueB_eq n hn hρ hc0 hlt, hρone _ hc, hρone _ (by rwa [abs_neg])]
  norm_num

/-- **The first deviation is the anchor's radial function on the whole cap `(0,c*)`**,
`c* = (√(1+(7/10)²))⁻¹ ≈ 0.8192`: there the glued datum is the anchor's
(`gluedPhi_eq_anchorPhi_on_cap`), the junction `(0.7809, 0.8192)` being where the anchor's datum
is the ball's. -/
theorem GlueA_eq_cap (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ} {α : ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hagree : ∀ x ∈ Set.Ioo ((Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹)
      ((Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹),
      radonPhi n ρ x = ballPhiData n x ∧ radonPsi n ρ x = 0)
    (hc0 : 0 < Real.cos α)
    (hcc : Real.cos α < (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹) :
    GlueA n ρ α = ρ (Real.cos α) ^ (2 * n + 2) + ρ (-Real.cos α) ^ (2 * n + 2) - 2 := by
  have hc1 : (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by
      have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + (7 / 10) ^ 2)
      nlinarith [Real.sqrt_nonneg (1 + (7 / 10 : ℝ) ^ 2)])
  have hcongr : Work.OddRadon.radonInverse n (GlueF n ρ) (Real.cos α)
      = Work.OddRadon.radonInverse n (radonPhi n ρ) (Real.cos α) :=
    radonInverse_congr_of_eqOn (n := n) (u := Real.cos α)
      (b := (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹) hc0 hcc
      (fun c hcx => by
        simp only [GlueF]
        rw [abs_of_pos hcx.1]
        exact (gluedPhi_eq_anchorPhi_on_cap n hn hcx.1 hcx.2 hagree).1)
  rw [GlueA, GluePhi, hcongr,
    Work.OddRadon.radonInverse_radonPhi_local n hn
      (c₁ := (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹) hc1 hρ hc0 hcc]
  field_simp

/-- **The second deviation is the anchor's radial function on the whole cap `(0,c*)`.** -/
theorem GlueB_eq_cap (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ} {α : ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hagree : ∀ x ∈ Set.Ioo ((Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹)
      ((Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹),
      radonPhi n ρ x = ballPhiData n x ∧ radonPsi n ρ x = 0)
    (hc0 : 0 < Real.cos α)
    (hcc : Real.cos α < (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹) :
    GlueB n ρ α = ρ (Real.cos α) ^ (2 * n + 1) - ρ (-Real.cos α) ^ (2 * n + 1) := by
  have hc1 : (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by
      have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + (7 / 10) ^ 2)
      nlinarith [Real.sqrt_nonneg (1 + (7 / 10 : ℝ) ^ 2)])
  have hcongr : Work.OddRadon.radonInverse n (GlueG n ρ) (Real.cos α)
      = Work.OddRadon.radonInverse n (radonPsi n ρ) (Real.cos α) :=
    radonInverse_congr_of_eqOn (n := n) (u := Real.cos α)
      (b := (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹) hc0 hcc
      (fun c hcx => by
        simp only [GlueG]
        rw [abs_of_pos hcx.1]
        exact (gluedPhi_eq_anchorPhi_on_cap n hn hcx.1 hcx.2 hagree).2)
  rw [GlueB, GluePsi, hcongr,
    Work.OddRadon.radonInverse_radonPsi_local n hn
      (c₁ := (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹) hc1 hρ hc0 hcc]
  field_simp

end

end Work.OddCurve.LowSlope
