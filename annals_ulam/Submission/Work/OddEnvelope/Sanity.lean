import Submission.Work.OddEnvelope.Main
import Submission.Work.OddEnvelope.Close.isEnvelopeCurve_semicircle

/-!
# Sanity check: the unperturbed semicircle

The unperturbed data `h = 0`, `x = y = profileX` satisfies `IsEnvelopeCurve`
(`Work.OddEnvelope.Close.isEnvelopeCurve_semicircle`), so the `Work.OddEnvelope` interface is
non-vacuous, and the profile it produces is the semicircle `√(1-t²)`.

The last result of this file is the *non-degeneracy test* of the odd case on this example: there
are `s > 0` and `t` strictly between the two intersection points with
`f t ^ 2 - (s t + h s) ^ 2 > 0`, i.e. the cutting section is genuinely non-trivial (the radicand
is not everywhere `≤ 0`, which is the defect of the vacuous published odd witnesses).
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology ContDiff

theorem negH_zero : negH (fun _ : ℝ => 0) = fun _ => 0 := by
  funext s; simp [negH]

theorem envelopeRight_zero_eq (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    envelopeRight (fun _ : ℝ => 0) profileX u = semicircle u := by
  have hc : IsEnvelopeCurve (fun _ : ℝ => 0) profileX profileX :=
    Work.OddEnvelope.Close.isEnvelopeCurve_semicircle
  set σ := slopeRight profileX u with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact hc.toChordCurve_y.slopeRight_pos hu
  have hσ : profileX σ = u := by rw [hσdef]; exact hc.toChordCurve_y.slopeRight_eq hu
  have hgoal : envelopeRight (fun _ : ℝ => 0) profileX u = σ * u := by
    rw [envelopeRight, ← hσdef]
    simp
  rw [hgoal, ← hσ, mul_profileX_eq_semicircle hσpos]

/-- The profile of the unperturbed data is the semicircle. -/
theorem envelopeProfile_semicircle_eq {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    envelopeProfile (fun _ : ℝ => 0) profileX profileX t = semicircle t := by
  have ht1 : (-1 : ℝ) < t := ht.1
  have ht2 : t < 1 := ht.2
  rcases lt_trichotomy t 0 with h | h | h
  · rw [envelopeProfile_of_neg ⟨ht1, h⟩, envelopeLeft_eq_negH, negH_zero]
    rw [envelopeRight_zero_eq (-t) ⟨by linarith, by linarith⟩, semicircle_even]
  · rw [h, envelopeProfile_zero, semicircle]
    norm_num
  · rw [envelopeProfile_of_pos ⟨h, ht2⟩]
    exact envelopeRight_zero_eq t ⟨h, ht2⟩

/-- **Non-degeneracy test on the semicircle.**  For the slope `s = 1` the cutting line cuts the
unit disc in a genuine interval and the radicand is strictly positive strictly inside it. -/
theorem semicircle_section_nondegenerate :
    ∃ t : ℝ, t ∈ Set.Ioo (-(profileX 1)) (profileX 1) ∧
      0 < (envelopeProfile (fun _ : ℝ => 0) profileX profileX t) ^ 2 - (1 * t + 0) ^ 2 := by
  have hc := Work.OddEnvelope.Close.isEnvelopeCurve_semicircle
  refine ⟨0, ⟨by linarith [profileX_pos 1], profileX_pos 1⟩, ?_⟩
  have h := envelopeProfile_sub_sq_pos hc (concaveOn_envelopeProfile hc) (s := 1) (by norm_num) 0
    ⟨by linarith [profileX_pos 1], profileX_pos 1⟩
  simpa using h

end

end Work.OddEnvelope
