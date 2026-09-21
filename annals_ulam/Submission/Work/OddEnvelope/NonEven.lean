import Submission.Work.OddEnvelope.Profile

/-!
# When is the envelope profile even?

The profile is even exactly when the chord-endpoint curve satisfies the *tuning relation*

  `y u * (σ u - u) = h (σ u) + h u`   for all `u > 0`,   where `σ u = slopeRight x (y u)`,

i.e. where `σ u` is the slope whose chord meets the left boundary at first coordinate `-y u`
(`x (σ u) = y u`).  Indeed, `f (y u) = u y u + h u` while `f (-(y u)) = σ u y u - h (σ u)`, so
evenness at `t = y u` is precisely this relation (and evenness for every `t` is equivalent to it,
because `y` is a bijection `(0,∞) → (0,1)` and both sides vanish outside `[-1,1]`).

Consequences:

* `envelopeProfile_even_iff` : the exact characterisation;
* `envelopeProfile_even_iff_eq_of_h_eq_zero` : if `h ≡ 0` then evenness is equivalent to
  `x = y` on `(0,∞)`;
* `not_even_of_h_eq_zero` : if `h ≡ 0` and `x s ≠ y s` for some `s > 0`, the profile is not even;
* `not_even_of_tuning_fails` : the general (and sharp) sufficient condition for non-evenness.

**Warning.** The naive statement "if `¬ ∀ s > 0, x s = y s` then `f` is not even" is *false*, even
when `h ≠ 0` is a bump supported in `[1-2τ, 1-τ]`.  For example take the chord curve of the
*semicircle* for the given `h`, namely `x s = (s h s + √(1+s²-h s²))/(1+s²)` and
`y s = (-s h s + √(1+s²-h s²))/(1+s²)`, so that `x s - y s = 2 s h s/(1 + s²) ≠ 0` exactly where
`h ≠ 0`.  The induced profile is `√(1-t²)` (even), and for small bumps this curve satisfies all
the shape conditions (`IsEnvelopeCurve`), so the tuning relation above holds even though
`x ≠ y`.  Non-evenness therefore does **not** follow from `x ≠ y`: it is the tuning relation that
is responsible, and for the genuine construction of the odd case it is the perturbed moment
equations that fail to satisfy it.
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology ContDiff

variable {h x y : ℝ → ℝ}

lemma slopeLeft_eq_slopeRight_neg (x : ℝ → ℝ) (t : ℝ) :
    slopeLeft x (t) = slopeRight x (-t) := rfl

/-- `f (-(y u)) = σ y u - h σ` where `σ = slopeRight x (y u)`. -/
lemma envelopeProfile_neg_root (H : IsEnvelopeCurve h x y) {u : ℝ} (hu : 0 < u) :
    envelopeProfile h x y (-(y u)) =
      slopeRight x (y u) * y u - h (slopeRight x (y u)) := by
  have hy0 : 0 < y u := H.toChordCurve_y.pos hu
  have hy1 : y u < 1 := H.toChordCurve_y.lt_one hu
  have hneg : -(y u) ∈ Set.Ioo (-1 : ℝ) 0 := ⟨by linarith, by linarith⟩
  have hsl : slopeLeft x (-(y u)) = slopeRight x (y u) := by
    simp only [slopeLeft, slopeRight, neg_neg]
  rw [envelopeProfile_of_neg hneg, envelopeLeft, hsl]
  ring

/-- If the tuning relation holds, the profile takes the same value at `v` and at `-v` for
`v ∈ (0,1)`. -/
lemma envelopeProfile_neg_eq_of_mem (H : IsEnvelopeCurve h x y)
    (hrel : ∀ u : ℝ, 0 < u →
      y u * (slopeRight x (y u) - u) - h (slopeRight x (y u)) - h u = 0)
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1) :
    envelopeProfile h x y (-v) = envelopeProfile h x y v := by
  obtain ⟨u, hu, hspec⟩ := H.toChordCurve_y.surj hv
  have h1 := envelopeProfile_root_right H hu
  have h2 := envelopeProfile_neg_root H hu
  have h3 := hrel u hu
  rw [hspec] at h1 h2 h3
  rw [h2, h1]
  linarith

/-- **Evenness of the profile is exactly the tuning relation.** -/
theorem envelopeProfile_even_iff (H : IsEnvelopeCurve h x y) :
    ((∀ t : ℝ, envelopeProfile h x y (-t) = envelopeProfile h x y t) ↔
      ∀ u : ℝ, 0 < u →
        y u * (slopeRight x (y u) - u) - h (slopeRight x (y u)) - h u = 0) := by
  constructor
  · intro heven u hu
    have h1 := envelopeProfile_root_right H hu
    have h2 := envelopeProfile_neg_root H hu
    have h3 := heven (-(y u))
    rw [neg_neg] at h3
    rw [h1, h2] at h3
    linarith
  · intro hrel t
    have hvan : ∀ w : ℝ, 1 ≤ |w| → envelopeProfile h x y w = 0 := by
      intro w hw
      have hcases : (1 : ℝ) ≤ w ∨ w ≤ -1 := by
        rcases lt_trichotomy w 0 with h | h | h
        · right; rw [abs_of_neg h] at hw; linarith
        · left; rw [h] at hw; norm_num at hw
        · left; rw [abs_of_pos h] at hw; exact hw
      have h1 : ¬ (w ∈ Set.Ioo (0 : ℝ) 1) := by
        intro hc
        rcases hcases with h | h
        · linarith [hc.2]
        · linarith [hc.1]
      have h2 : ¬ (w ∈ Set.Ioo (-1 : ℝ) 0) := by
        intro hc
        rcases hcases with h | h
        · linarith [hc.2]
        · linarith [hc.1]
      exact envelopeProfile_eq_zero h1 h2 (by rintro rfl; norm_num at hcases)
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · rcases lt_trichotomy (-t) 1 with h1 | h1 | h1
      · simpa using (envelopeProfile_neg_eq_of_mem H hrel ⟨by linarith, h1⟩).symm
      · have ht : t = -1 := by linarith
        rw [h1, ht, envelopeProfile_right_end, envelopeProfile_left_end]
      · rw [hvan t (by rw [abs_of_neg hlt]; linarith), hvan (-t) (by rw [abs_neg, abs_of_neg hlt]; linarith)]
    · rw [heq, neg_zero]
    · rcases lt_trichotomy t 1 with h1 | h1 | h1
      · exact envelopeProfile_neg_eq_of_mem H hrel ⟨hgt, h1⟩
      · rw [h1, envelopeProfile_right_end, envelopeProfile_left_end]
      · rw [hvan t (by rw [abs_of_pos hgt]; linarith),
          hvan (-t) (by rw [abs_neg, abs_of_pos hgt]; linarith)]

/-- With `h ≡ 0`, evenness of the profile is equivalent to `x = y` on `(0,∞)`. -/
theorem envelopeProfile_even_iff_eq_of_h_eq_zero (H : IsEnvelopeCurve h x y)
    (hh : ∀ s, h s = 0) :
    ((∀ t : ℝ, envelopeProfile h x y (-t) = envelopeProfile h x y t) ↔
      ∀ s : ℝ, 0 < s → x s = y s) := by
  rw [envelopeProfile_even_iff H]
  constructor
  · intro hrel s hs
    have hy0 : 0 < y s := H.toChordCurve_y.pos hs
    have hy1 : y s < 1 := H.toChordCurve_y.lt_one hs
    have h1 := hrel s hs
    rw [hh s, hh (slopeRight x (y s))] at h1
    have h2 : slopeRight x (y s) = s := by
      have h3 : y s * (slopeRight x (y s) - s) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 (ne_of_gt hy0)
      · linarith
    have h5 : x (slopeRight x (y s)) = y s :=
      H.toChordCurve_x.slopeRight_eq ⟨hy0, hy1⟩
    rw [h2] at h5
    exact h5
  · intro hxy u hu
    have hy0 : 0 < y u := H.toChordCurve_y.pos hu
    have hy1 : y u < 1 := H.toChordCurve_y.lt_one hu
    have hσ : slopeRight x (y u) = u :=
      (H.toChordCurve_x.slopeRight_eq_of ⟨hy0, hy1⟩ hu (hxy u hu)).symm
    rw [hσ, hh u]
    ring

/-- If `h ≡ 0` and `x s ≠ y s` for some `s > 0`, the profile is not even. -/
theorem not_even_of_h_eq_zero (H : IsEnvelopeCurve h x y) (hh : ∀ s, h s = 0)
    (hne : ∃ s : ℝ, 0 < s ∧ x s ≠ y s) :
    ¬ ∀ t : ℝ, envelopeProfile h x y (-t) = envelopeProfile h x y t := by
  intro heven
  obtain ⟨s, hs, hne'⟩ := hne
  exact hne' ((envelopeProfile_even_iff_eq_of_h_eq_zero H hh).mp heven s hs)

/-- The sharp sufficient condition for non-evenness: the tuning relation fails somewhere. -/
theorem not_even_of_tuning_fails (H : IsEnvelopeCurve h x y)
    (hbad : ∃ u : ℝ, 0 < u ∧
      y u * (slopeRight x (y u) - u) - h (slopeRight x (y u)) - h u ≠ 0) :
    ¬ ∀ t : ℝ, envelopeProfile h x y (-t) = envelopeProfile h x y t := by
  intro heven
  obtain ⟨u, hu, hne⟩ := hbad
  exact hne ((envelopeProfile_even_iff H).mp heven u hu)

end

end Work.OddEnvelope
