import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDataDefs
import Submission.Work.OddCurve.LowSlope.waistRadial_eq_one
import Submission.Work.OddVolterra.Free.FreeSetup

/-!
# The glued two-power data vanish on a neighbourhood of `α = π/2`

The two-power system of the low-slope reconstruction carries the data

`R^{2n+2} + r^{2n+2} = 2 + glueA n ρ α`,   `R^{2n+1} - r^{2n+1} = glueB n ρ α`.

Near `α = π/2` the cosine is small, `|cos α| ≤ |α - π/2|`, so for
`α ∈ (π/2 - 1/4, π/2 + 1/4)` we have `|cos α| < 1/4 < tStar` and in particular
`cos α < 4/5`, i.e. the first (anchor) branch of `glueA`/`glueB` is the active one.  There the
data are combinations of `ρ (±cos α)`, and on the waist `|u| < tStar` the anchor's radial
function is the constant `1` (`Work.OddCurve.LowSlope.waistRadial_eq_one`, applied to an
`IsAnchorRadial` package): the profile is the unit semicircle there, so the radial function of
the body is `1`.  Hence

`glueA n ρ α = 1 + 1 - 2 = 0`,   `glueB n ρ α = 1 - 1 = 0`,

exactly the endpoint condition `R (π/2) = r (π/2) = 1` of the two-power system.
-/

namespace Work.OddCurveB.Step3

open Set

/-- `tStar > 1/4`.  The waist of the anchor is wider than the interval `|u| < 1/4`, which is
what `|cos α| ≤ |α - π/2| < 1/4` for the angles considered here produces. -/
lemma one_fourth_lt_tStar : (1 : ℝ) / 4 < Work.OddEnvelope.tStar := by
  have h : Work.OddEnvelope.tStar = 1 / Real.sqrt (1 + (9 / 10 : ℝ) ^ 2) := by
    simp only [Work.OddEnvelope.tStar, Work.OddEnvelope.profileX, Work.OddEnvelope.tau]
    norm_num
  rw [h]
  have hs4 : Real.sqrt (1 + (9 / 10 : ℝ) ^ 2) < 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + (9 / 10) ^ 2),
      Real.sqrt_nonneg (1 + (9 / 10 : ℝ) ^ 2)]
  exact one_div_lt_one_div_of_lt (Real.sqrt_pos.mpr (by norm_num)) hs4

/-- The radial point of an anchor's radial function stays inside `(-1,1)`: the profile does not
vanish at `±1`, while it does not vanish at the radial point because the radial function is
positive there. -/
lemma anchorRadial_radial_point {h X Y ρ : ℝ → ℝ}
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)) :
    ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * u ∈ Set.Ioo (-1 : ℝ) 1 := by
  intro u hu
  have hspos : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.mpr (by nlinarith [hu.1, hu.2])
  have hfu : Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) = ρ u * Real.sqrt (1 - u ^ 2) :=
    (hgraph u hu).symm
  have hne : Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) ≠ 0 := by
    rw [hfu]; exact ne_of_gt (mul_pos (hρpos u hu) hspos)
  have hIcc : ρ u * u ∈ Set.Icc (-1 : ℝ) 1 :=
    Work.OddEnvelope.envelopeProfile_support (Function.mem_support.mpr hne)
  have hne1 : Work.OddEnvelope.envelopeProfile h X Y 1 = 0 := Work.OddEnvelope.envelopeProfile_right_end
  have hnem1 : Work.OddEnvelope.envelopeProfile h X Y (-1) = 0 := Work.OddEnvelope.envelopeProfile_left_end
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hIcc.1 with hq | hq
    · exfalso
      rw [← hq, hnem1] at hfu
      exact absurd (mul_pos (hρpos u hu) hspos) (by rw [hfu]; norm_num)
    · exact hq
  · rcases eq_or_lt_of_le hIcc.2 with hq | hq
    · exfalso
      rw [hq, hne1] at hfu
      exact absurd (mul_pos (hρpos u hu) hspos) (by rw [hfu]; norm_num)
    · exact hq

/-- **The waist of the anchor's radial function.**  For `|u| < tStar` the anchor's radial
function is the constant `1`: there the anchor's profile is the unit semicircle, whose radial
function is `1`, and the ray meets the graph at a unique point by strict concavity
(`Work.OddCurve.LowSlope.waistRadial_eq_one`). -/
lemma anchorRadial_waist {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hrad : Work.OddVolterra.Free.IsAnchorRadial h X Y ρ) :
    ∀ u : ℝ, |u| < Work.OddEnvelope.tStar → ρ u = 1 := by
  obtain ⟨hρpos, -, -, hgraph, hρ0⟩ := hrad
  exact fun u hu => Work.OddCurve.LowSlope.waistRadial_eq_one H hρpos hρ0 hgraph
    (anchorRadial_radial_point hρpos hgraph) hu

theorem glue_vanish_near_pi_div_two (n : ℕ) (hn : 1 ≤ n) {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hrad : Work.OddVolterra.Free.IsAnchorRadial h X Y ρ) :
    ∀ α ∈ Set.Ioo (Real.pi / 2 - 1 / 4) (Real.pi / 2 + 1 / 4),
      Work.OddCurve.LowSlope.glueA n ρ α = 0 ∧ Work.OddCurve.LowSlope.glueB n ρ α = 0 := by
  have hwaist := anchorRadial_waist H hrad
  intro α hα
  -- `|cos α| ≤ |α - π/2| < 1/4`
  have habs : |Real.cos α| < 1 / 4 := by
    have h1 : |α - Real.pi / 2| < 1 / 4 := by
      rw [abs_lt]
      exact ⟨by linarith [hα.1], by linarith [hα.2]⟩
    have h2 : Real.cos α = Real.sin (Real.pi / 2 - α) := by
      have hh := Real.cos_pi_div_two_sub (Real.pi / 2 - α)
      rw [sub_sub_cancel] at hh
      exact hh
    rw [h2]
    calc |Real.sin (Real.pi / 2 - α)| ≤ |Real.pi / 2 - α| := Real.abs_sin_le_abs
      _ = |α - Real.pi / 2| := abs_sub_comm _ _
      _ < 1 / 4 := h1
  have hlt : Real.cos α < 4 / 5 := by linarith [(abs_lt.mp habs).2]
  have htSt : |Real.cos α| < Work.OddEnvelope.tStar := lt_trans habs one_fourth_lt_tStar
  have hne : |(-Real.cos α)| < Work.OddEnvelope.tStar := by rwa [abs_neg]
  refine ⟨?_, ?_⟩
  · rw [Work.OddCurve.LowSlope.glueA_of_lt hlt,
      hwaist (Real.cos α) htSt, hwaist (-Real.cos α) hne]
    norm_num
  · rw [Work.OddCurve.LowSlope.glueB_of_lt hlt,
      hwaist (Real.cos α) htSt, hwaist (-Real.cos α) hne]
    norm_num

end Work.OddCurveB.Step3
