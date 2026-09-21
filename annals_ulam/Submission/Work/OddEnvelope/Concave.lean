import Submission.Work.OddEnvelope.Smooth
import Submission.Work.OddEnvelope.Smoothness.envelopeRight_deriv_Cinf
import Submission.Work.OddEnvelope.Shape.kSlope_strictMonoOn_Cinf
import Submission.Work.OddEnvelope.Semicircle.deriv_semicircle

/-!
# Strict concavity of the envelope profile

The logarithmic derivative of the right branch, `kSlope h y`, is strictly increasing (that is
exactly the second-order shape condition `IsEnvelopeCurve.shape_y`), and the inverse slope
`slopeRight y` is strictly decreasing, so `deriv f = kSlope h y ∘ slopeRight y` is strictly
decreasing on `(0,1)`; the mirror statement holds on `(-1,0)`, and `deriv f 0 = 0` because the
profile is the semicircle near `0`.  Hence `deriv f` is strictly decreasing on `(-1,1)` and, by
`StrictAntiOn.strictConcaveOn_of_deriv`, the profile is strictly concave on `[-1,1]`.
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology ContDiff

variable {h x y : ℝ → ℝ}

lemma kSlope_strictMonoOn_of_isEnvelopeCurve (H : IsEnvelopeCurve h x y) :
    StrictMonoOn (kSlope h y) (Set.Ioi 0) :=
  Work.OddEnvelope.Shape.kSlope_strictMonoOn_Cinf H.smooth_y H.y_deriv_neg H.smooth_h H.shape_y

lemma kSlope_negH_strictMonoOn (H : IsEnvelopeCurve h x y) :
    StrictMonoOn (kSlope (negH h) x) (Set.Ioi 0) := by
  refine Work.OddEnvelope.Shape.kSlope_strictMonoOn_Cinf H.smooth_x H.x_deriv_neg
    H.smooth_h.neg ?_
  intro s hs
  have h1 : deriv (negH h) s = -deriv h s := by rw [deriv_negH]
  have h2 : deriv (deriv (negH h)) s = -deriv (deriv h) s := by rw [deriv_deriv_negH]
  rw [h1, h2]
  nlinarith [H.shape_x s hs]

/-! ### The derivative of the profile on the two branches -/

lemma deriv_envelopeProfile_of_pos (H : IsEnvelopeCurve h x y) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (envelopeProfile h x y) t = kSlope h y (slopeRight y t) := by
  have hev : envelopeProfile h x y =ᶠ[𝓝 t] envelopeRight h y := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact envelopeProfile_of_pos hu
  rw [Filter.EventuallyEq.deriv_eq hev]
  exact Work.OddEnvelope.Smoothness.envelopeRight_deriv_Cinf H.smooth_y H.y_deriv_neg H.smooth_h
    (fun t ht => H.toChordCurve_y.surj ht) t ht

lemma deriv_envelopeProfile_of_neg (H : IsEnvelopeCurve h x y) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    deriv (envelopeProfile h x y) t = -kSlope (negH h) x (slopeRight x (-t)) := by
  have hev : envelopeProfile h x y =ᶠ[𝓝 t] (fun u => envelopeRight (negH h) x (-u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    rw [envelopeProfile_of_neg hu, envelopeLeft_eq_negH]
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_comp_neg]
  congr 1
  exact Work.OddEnvelope.Smoothness.envelopeRight_deriv_Cinf H.smooth_x H.x_deriv_neg
    H.smooth_h.neg (fun t ht => H.toChordCurve_x.surj ht) (-t)
    ⟨by linarith [ht.2], by linarith [ht.1]⟩

lemma deriv_envelopeProfile_zero (H : IsEnvelopeCurve h x y) :
    deriv (envelopeProfile h x y) 0 = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Ioo (-tStar) tStar :=
    ⟨by linarith [tStar_pos], tStar_pos⟩
  have hev : envelopeProfile h x y =ᶠ[𝓝 (0 : ℝ)] semicircle := by
    filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
    exact envelopeProfile_eq_semicircle H hu
  rw [Filter.EventuallyEq.deriv_eq hev,
    Work.OddEnvelope.Semicircle.deriv_semicircle ⟨by norm_num, by norm_num⟩]
  simp

/-! ### The derivative is strictly decreasing -/

/-- On `(0,1)` the derivative of the profile is negative. -/
lemma deriv_envelopeProfile_neg (H : IsEnvelopeCurve h x y) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) : deriv (envelopeProfile h x y) t < 0 := by
  rw [deriv_envelopeProfile_of_pos H ht]
  exact (H.isEnvelopeBranch_right).kSlope_neg (H.toChordCurve_y.slopeRight_pos ht)

/-- On `(-1,0)` the derivative of the profile is positive. -/
lemma deriv_envelopeProfile_pos (H : IsEnvelopeCurve h x y) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) : 0 < deriv (envelopeProfile h x y) t := by
  rw [deriv_envelopeProfile_of_neg H ht]
  have hσ : 0 < slopeRight x (-t) :=
    H.toChordCurve_x.slopeRight_pos ⟨by linarith [ht.2], by linarith [ht.1]⟩
  linarith [(H.isEnvelopeBranch_left).kSlope_neg hσ]

theorem strictAntiOn_deriv_envelopeProfile (H : IsEnvelopeCurve h x y) :
    StrictAntiOn (deriv (envelopeProfile h x y)) (Set.Ioo (-1 : ℝ) 1) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  have ht1a : (-1 : ℝ) < t₁ := ht₁.1
  have ht1b : t₁ < 1 := ht₁.2
  have ht2a : (-1 : ℝ) < t₂ := ht₂.1
  have ht2b : t₂ < 1 := ht₂.2
  rcases lt_trichotomy t₁ 0 with h1neg | h1zero | h1pos
  · rcases lt_trichotomy t₂ 0 with h2neg | h2zero | h2pos
    · have ht1' : t₁ ∈ Set.Ioo (-1 : ℝ) 0 := ⟨ht1a, h1neg⟩
      have ht2' : t₂ ∈ Set.Ioo (-1 : ℝ) 0 := ⟨ht2a, h2neg⟩
      have hu1 : -t₁ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hu2 : -t₂ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      set κ₁ := slopeRight x (-t₁) with hκ₁
      set κ₂ := slopeRight x (-t₂) with hκ₂
      have hm₁ : 0 < κ₁ := by rw [hκ₁]; exact H.toChordCurve_x.slopeRight_pos hu1
      have hm₂ : 0 < κ₂ := by rw [hκ₂]; exact H.toChordCurve_x.slopeRight_pos hu2
      have hanti : κ₁ < κ₂ := by
        rw [hκ₁, hκ₂]
        exact H.toChordCurve_x.slopeRight_strictAntiOn hu2 hu1 (by linarith)
      have hK := kSlope_negH_strictMonoOn H hm₁ hm₂ hanti
      rw [deriv_envelopeProfile_of_neg H ht1', deriv_envelopeProfile_of_neg H ht2',
        ← hκ₁, ← hκ₂]
      linarith
    · rw [h2zero, deriv_envelopeProfile_zero H]
      exact deriv_envelopeProfile_pos H ⟨ht1a, h1neg⟩
    · exact lt_trans (deriv_envelopeProfile_neg H ⟨h2pos, ht2b⟩)
        (deriv_envelopeProfile_pos H ⟨ht1a, h1neg⟩)
  · rw [h1zero, deriv_envelopeProfile_zero H]
    exact deriv_envelopeProfile_neg H ⟨by linarith, ht2b⟩
  · have ht1' : t₁ ∈ Set.Ioo (0 : ℝ) 1 := ⟨h1pos, ht1b⟩
    have ht2' : t₂ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, ht2b⟩
    rw [deriv_envelopeProfile_of_pos H ht1', deriv_envelopeProfile_of_pos H ht2']
    have hanti : slopeRight y t₂ < slopeRight y t₁ :=
      H.toChordCurve_y.slopeRight_strictAntiOn ht1' ht2' hlt
    exact kSlope_strictMonoOn_of_isEnvelopeCurve H
      (H.toChordCurve_y.slopeRight_pos ht2') (H.toChordCurve_y.slopeRight_pos ht1') hanti

end

end Work.OddEnvelope
