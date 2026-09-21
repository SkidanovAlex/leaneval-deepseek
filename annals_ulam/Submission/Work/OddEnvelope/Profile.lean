import Submission.Work.OddEnvelope.Branch

/-!
# The envelope profile: support, positivity, roots and the unperturbed part

This file assembles the profile `envelopeProfile h x y` from the two branches and proves the
structural properties needed by the cap/centroid lemmas of the odd-dimensional Ulam problem:

* `envelopeProfile_support`, `envelopeProfile_left_end`, `envelopeProfile_right_end` : the
  profile is supported on `[-1,1]` and vanishes at the ends;
* `envelopeProfile_pos` : the profile is positive on `(-1,1)`;
* `envelopeProfile_root_right`, `envelopeProfile_root_left` : the two intersection conditions
  `f (y s) = s * y s + h s` and `f (-(x s)) = -(s * (-(x s)) + h s)`;
* `envelopeProfile_mem_Ioo` : `-(x s), y s ∈ (-1,1)`;
* `envelopeProfile_eq_semicircle` : on the unperturbed part `(-tStar, tStar)` the profile is the
  semicircle `√(1-t²)`.
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology ContDiff

variable {h x y : ℝ → ℝ}

/-- The chord-curve predicate extracted from `IsEnvelopeCurve h x y` for the curve `y`. -/
lemma IsEnvelopeCurve.toChordCurve_y (H : IsEnvelopeCurve h x y) : IsChordCurve y where
  smooth := H.smooth_y
  deriv_neg := H.y_deriv_neg
  tendsto_one := H.y_tendsto_one
  tail := H.y_tail

/-- The chord-curve predicate extracted from `IsEnvelopeCurve h x y` for the curve `x`. -/
lemma IsEnvelopeCurve.toChordCurve_x (H : IsEnvelopeCurve h x y) : IsChordCurve x where
  smooth := H.smooth_x
  deriv_neg := H.x_deriv_neg
  tendsto_one := H.x_tendsto_one
  tail := H.x_tail

/-- The left branch of the profile is the right-branch construction with the reflected
perturbation `-h` and the curve `x`. -/
lemma envelopeLeft_eq_negH (h x : ℝ → ℝ) (t : ℝ) :
    envelopeLeft h x t = envelopeRight (negH h) x (-t) := by
  simp only [envelopeLeft, envelopeRight, negH, slopeRight, slopeLeft]
  ring

lemma deriv_negH (h : ℝ → ℝ) : deriv (negH h) = fun s => -deriv h s := by
  funext s
  by_cases hd : DifferentiableAt ℝ h s
  · exact hd.hasDerivAt.neg.deriv
  · have hd' : ¬ DifferentiableAt ℝ (negH h) s := by
      intro hcon
      refine hd ?_
      have hc : DifferentiableAt ℝ (fun u => -(negH h u)) s := hcon.neg
      have hfun : (fun u => -(negH h u)) = h := by
        funext u; simp [negH]
      rwa [hfun] at hc
    rw [deriv_zero_of_not_differentiableAt hd', deriv_zero_of_not_differentiableAt hd, neg_zero]

lemma deriv_deriv_negH (h : ℝ → ℝ) :
    deriv (deriv (negH h)) = fun s => -deriv (deriv h) s := by
  rw [deriv_negH]
  exact deriv_negH (deriv h)

/-- The right branch of an envelope curve. -/
lemma IsEnvelopeCurve.isEnvelopeBranch_right (H : IsEnvelopeCurve h x y) :
    IsEnvelopeBranch h y where
  smooth := H.smooth_y
  deriv_neg := H.y_deriv_neg
  tendsto_one := H.y_tendsto_one
  tail := H.y_tail
  smooth_p := H.smooth_h
  pos_c := fun s hs => H.toChordCurve_y.pos hs
  vanish_p := by
    intro s hs hslt
    by_contra hne
    exact absurd (H.h_support hne).1 (not_le.mpr hslt)
  vanish_p_tail := by
    intro s hgt
    by_contra hne
    exact absurd (H.h_support hne).2 (not_le.mpr hgt)
  mono := H.mono_y
  shape := H.shape_y

/-- The left branch of an envelope curve. -/
lemma IsEnvelopeCurve.isEnvelopeBranch_left (H : IsEnvelopeCurve h x y) :
    IsEnvelopeBranch (negH h) x where
  smooth := H.smooth_x
  deriv_neg := H.x_deriv_neg
  tendsto_one := H.x_tendsto_one
  tail := H.x_tail
  smooth_p := H.smooth_h.neg
  pos_c := fun s hs => H.toChordCurve_x.pos hs
  vanish_p := by
    intro s hs hslt
    simp only [negH, neg_eq_zero]
    by_contra hne
    exact absurd (H.h_support hne).1 (not_le.mpr hslt)
  vanish_p_tail := by
    intro s hgt
    simp only [negH, neg_eq_zero]
    by_contra hne
    exact absurd (H.h_support hne).2 (not_le.mpr hgt)
  mono := by
    intro s hs
    have h1 : deriv (negH h) s = -deriv h s := by rw [deriv_negH]
    rw [h1]
    linarith [H.mono_x s hs]
  shape := by
    intro s hs
    have h1 : deriv (negH h) s = -deriv h s := by rw [deriv_negH]
    have h2 : deriv (deriv (negH h)) s = -deriv (deriv h) s := by rw [deriv_deriv_negH]
    rw [h1, h2]
    nlinarith [H.shape_x s hs]

/-! ### Evaluating the profile -/

@[simp] lemma envelopeProfile_of_pos {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    envelopeProfile h x y t = envelopeRight h y t := by
  have h1 : ¬ (t ∈ Set.Ioo (-1 : ℝ) 0) := by
    intro hc; exact absurd ht.1 (not_lt.mpr hc.2.le)
  have h2 : t ≠ 0 := ne_of_gt ht.1
  rw [envelopeProfile]
  simp [h1, h2, ht]

@[simp] lemma envelopeProfile_of_neg {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    envelopeProfile h x y t = envelopeLeft h x t := by
  have h1 : ¬ (t ∈ Set.Ioo (0 : ℝ) 1) := by
    intro hc; exact absurd ht.2 (not_lt.mpr hc.1.le)
  have h2 : t ≠ 0 := ne_of_lt ht.2
  rw [envelopeProfile]
  simp [h1, h2, ht]

@[simp] lemma envelopeProfile_zero : envelopeProfile h x y 0 = 1 := by
  rw [envelopeProfile]; simp

lemma envelopeProfile_eq_zero {t : ℝ} (h2 : ¬ (t ∈ Set.Ioo (0 : ℝ) 1))
    (h3 : ¬ (t ∈ Set.Ioo (-1 : ℝ) 0)) (h4 : t ≠ 0) : envelopeProfile h x y t = 0 := by
  rw [envelopeProfile]
  simp [h2, h3, h4]

/-! ### Support and endpoints -/

lemma envelopeProfile_support : Function.support (envelopeProfile h x y) ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro t ht
  by_contra hcon
  have h1 : ¬ (t ∈ Set.Ioo (0 : ℝ) 1) := fun hc =>
    hcon ⟨le_of_lt (by linarith [hc.1]), le_of_lt hc.2⟩
  have h2 : ¬ (t ∈ Set.Ioo (-1 : ℝ) 0) := fun hc =>
    hcon ⟨le_of_lt hc.1, le_of_lt (by linarith [hc.2])⟩
  have h3 : t ≠ 0 := fun hc => hcon (by rw [hc]; norm_num)
  exact ht (envelopeProfile_eq_zero h1 h2 h3)

@[simp] lemma envelopeProfile_left_end : envelopeProfile h x y (-1) = 0 := by
  have h2 : ¬ ((-1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1) := by simp
  have h3 : ¬ ((-1 : ℝ) ∈ Set.Ioo (-1 : ℝ) 0) := by simp
  exact envelopeProfile_eq_zero h2 h3 (by norm_num)

@[simp] lemma envelopeProfile_right_end : envelopeProfile h x y 1 = 0 := by
  have h2 : ¬ ((1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1) := by simp
  have h3 : ¬ ((1 : ℝ) ∈ Set.Ioo (-1 : ℝ) 0) := by simp
  exact envelopeProfile_eq_zero h2 h3 (by norm_num)

/-! ### Positivity -/

lemma envelopeProfile_pos (H : IsEnvelopeCurve h x y) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < envelopeProfile h x y t := by
  have ht1 : (-1 : ℝ) < t := ht.1
  have ht2 : t < 1 := ht.2
  rcases lt_trichotomy t 0 with hneg | heq | hpos
  · rw [envelopeProfile_of_neg ⟨ht1, hneg⟩, envelopeLeft_eq_negH]
    exact (H.isEnvelopeBranch_left).envelopeRight_pos
      ⟨by linarith, by linarith⟩
  · rw [heq, envelopeProfile_zero]; norm_num
  · rw [envelopeProfile_of_pos ⟨hpos, ht2⟩]
    exact (H.isEnvelopeBranch_right).envelopeRight_pos ⟨hpos, ht2⟩

/-! ### The root conditions -/

lemma envelopeProfile_root_right (H : IsEnvelopeCurve h x y) {s : ℝ} (hs : 0 < s) :
    envelopeProfile h x y (y s) = s * y s + h s := by
  have hy1 : y s < 1 := H.toChordCurve_y.lt_one hs
  have hy0 : 0 < y s := H.toChordCurve_y.pos hs
  rw [envelopeProfile_of_pos ⟨hy0, hy1⟩, envelopeRight]
  have h1 : slopeRight y (y s) = s :=
    (H.toChordCurve_y.slopeRight_eq_of ⟨hy0, hy1⟩ hs rfl).symm
  rw [h1]

lemma envelopeProfile_root_left (H : IsEnvelopeCurve h x y) {s : ℝ} (hs : 0 < s) :
    envelopeProfile h x y (-(x s)) = -(s * (-(x s)) + h s) := by
  have hx1 : x s < 1 := H.toChordCurve_x.lt_one hs
  have hx0 : 0 < x s := H.toChordCurve_x.pos hs
  have hsl : slopeLeft x (-(x s)) = slopeRight x (x s) := by
    rw [slopeLeft, slopeRight, neg_neg]
  have hmem : -(x s) ∈ Set.Ioo (-1 : ℝ) 0 := ⟨by linarith, by linarith⟩
  rw [envelopeProfile_of_neg hmem, envelopeLeft, hsl]
  have h1 : slopeRight x (x s) = s :=
    (H.toChordCurve_x.slopeRight_eq_of ⟨hx0, hx1⟩ hs rfl).symm
  rw [h1]

lemma envelopeProfile_mem_Ioo (H : IsEnvelopeCurve h x y) {s : ℝ} (hs : 0 < s) :
    -(x s) ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1 :=
  ⟨⟨by have := H.toChordCurve_x.lt_one hs; linarith,
    by have := H.toChordCurve_x.pos hs; linarith⟩,
   ⟨by have := H.toChordCurve_y.pos hs; linarith, H.toChordCurve_y.lt_one hs⟩⟩

/-! ### The unperturbed part -/

/-- On the unperturbed part the profile is the semicircle. -/
lemma envelopeProfile_eq_semicircle (H : IsEnvelopeCurve h x y) {t : ℝ}
    (ht : t ∈ Set.Ioo (-tStar) tStar) : envelopeProfile h x y t = semicircle t := by
  have ht1 : -tStar < t := ht.1
  have ht2 : t < tStar := ht.2
  rcases lt_trichotomy t 0 with hneg | heq | hpos
  · have hmem : t ∈ Set.Ioo (-1 : ℝ) 0 := ⟨by linarith [tStar_lt_one], hneg⟩
    rw [envelopeProfile_of_neg hmem, envelopeLeft_eq_negH]
    rw [(H.isEnvelopeBranch_left).envelopeRight_eq_semicircle
      ⟨by linarith, by linarith⟩, semicircle_even]
  · rw [heq, envelopeProfile_zero, semicircle]
    norm_num
  · rw [envelopeProfile_of_pos ⟨hpos, lt_trans ht2 tStar_lt_one⟩]
    exact (H.isEnvelopeBranch_right).envelopeRight_eq_semicircle ⟨by linarith, ht2⟩

end

end Work.OddEnvelope
