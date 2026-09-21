import Submission.Work.OddEnvelope.Profile
import Submission.Work.OddEnvelope.Smoothness.envelopeRight_contDiffOn
import Submission.Work.OddEnvelope.Semicircle.contDiffOn_semicircle

/-!
# Smoothness of the envelope profile

The right branch is smooth by the inverse function theorem
(`Work.OddEnvelope.Smoothness.envelopeRight_contDiffOn_smooth`), the left branch is the same
construction with the reflected perturbation `-h` and the curve `x`, and the two branches agree
with the semicircle near `t = 0`, so the glued profile is `C^∞` on `(-1,1)`.
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology ContDiff

variable {h x y : ℝ → ℝ}

lemma contDiffOn_neg_id : ContDiffOn ℝ ∞ (fun t : ℝ => -t) (Set.Ioo (-1 : ℝ) 0) := by fun_prop

/-- The left branch is `C^∞` where it is defined. -/
lemma contDiffOn_envelopeLeft (H : IsEnvelopeCurve h x y) :
    ContDiffOn ℝ ∞ (envelopeLeft h x) (Set.Ioo (-1 : ℝ) 0) := by
  have h1 : ContDiffOn ℝ ∞ (envelopeRight (negH h) x) (Set.Ioo (0 : ℝ) 1) :=
    Work.OddEnvelope.Smoothness.envelopeRight_contDiffOn_smooth H.smooth_x H.x_deriv_neg
      H.smooth_h.neg (fun t ht => H.toChordCurve_x.surj ht)
  have h2 : ContDiffOn ℝ ∞ (fun t => envelopeRight (negH h) x (-t)) (Set.Ioo (-1 : ℝ) 0) :=
    h1.comp contDiffOn_neg_id (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  refine h2.congr ?_
  intro t _
  exact envelopeLeft_eq_negH h x t

/-- The profile is `C^∞` on `(-1,1)`. -/
theorem envelopeProfile_contDiffOn (H : IsEnvelopeCurve h x y) :
    ContDiffOn ℝ ∞ (envelopeProfile h x y) (Set.Ioo (-1 : ℝ) 1) := by
  have hsemi : ContDiffOn ℝ ∞ semicircle (Set.Ioo (-1 : ℝ) 1) :=
    Work.OddEnvelope.Semicircle.contDiffOn_semicircle.of_le le_top
  intro t ht
  rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioo.mem_nhds ht)]
  rcases lt_trichotomy t 0 with hlt | heq | hgt
  · have hmem : t ∈ Set.Ioo (-1 : ℝ) 0 := ⟨ht.1, hlt⟩
    have hev : envelopeProfile h x y =ᶠ[𝓝 t] envelopeLeft h x := by
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
      exact envelopeProfile_of_neg hu
    exact ContDiffAt.congr_of_eventuallyEq
      ((contDiffOn_envelopeLeft H).contDiffAt (isOpen_Ioo.mem_nhds hmem)) hev
  · subst heq
    have hmem : (0 : ℝ) ∈ Set.Ioo (-tStar) tStar :=
      ⟨by linarith [tStar_pos], tStar_pos⟩
    have hev : envelopeProfile h x y =ᶠ[𝓝 (0 : ℝ)] semicircle := by
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
      exact envelopeProfile_eq_semicircle H hu
    exact ContDiffAt.congr_of_eventuallyEq
      (hsemi.contDiffAt (isOpen_Ioo.mem_nhds ⟨by norm_num, by norm_num⟩)) hev
  · have hmem : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨hgt, ht.2⟩
    have hev : envelopeProfile h x y =ᶠ[𝓝 t] envelopeRight h y := by
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
      exact envelopeProfile_of_pos hu
    have hb : ContDiffOn ℝ ∞ (envelopeRight h y) (Set.Ioo (0 : ℝ) 1) :=
      Work.OddEnvelope.Smoothness.envelopeRight_contDiffOn_smooth H.smooth_y H.y_deriv_neg
        H.smooth_h (fun t ht => H.toChordCurve_y.surj ht)
    exact ContDiffAt.congr_of_eventuallyEq (hb.contDiffAt (isOpen_Ioo.mem_nhds hmem)) hev

end

end Work.OddEnvelope
