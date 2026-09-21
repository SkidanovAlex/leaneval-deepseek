import Submission.Work.OddEnvelope.Defs

/-!
# The chord-endpoint curve API

A *chord curve* is a strictly decreasing smooth function `c : (0,∞) → (0,1)` with
`c σ → 1` as `σ → 0⁺` and which agrees with the semicircle chord function `profileX` for
`σ ≥ 1 - τ`.  Such a `c` is a bijection `(0,∞) → (0,1)` and its inverse is `slopeRight c`.

This file proves the basic API: surjectivity onto `(0,1)`, the specification/characterisation of
`slopeRight`, strict antitonicity of `slopeRight`, and the quantitative statement that
`t ↦ slopeRight c t` takes values `≥ 1 - τ` on the unperturbed part `(0, tStar)`.
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology ContDiff

/-! ### The chord function of the semicircle -/

lemma profileX_pos (s : ℝ) : 0 < profileX s := by
  rw [profileX]; positivity

lemma tau_pos : 0 < tau := by norm_num [tau]

lemma one_sub_tau_pos : 0 < 1 - tau := by norm_num [tau]

lemma one_sub_two_tau_pos : 0 < 1 - 2 * tau := by norm_num [tau]

lemma profileX_sq (s : ℝ) : profileX s ^ 2 = 1 / (1 + s ^ 2) := by
  rw [profileX, div_pow, one_pow, Real.sq_sqrt (by positivity)]

lemma profileX_lt_one {s : ℝ} (hs : 0 < s) : profileX s < 1 := by
  rw [profileX, div_lt_one (Real.sqrt_pos.mpr (by positivity))]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by nlinarith [sq_pos_of_pos hs])

lemma profileX_strictAntiOn : StrictAntiOn profileX (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  rw [profileX, profileX]
  refine one_div_lt_one_div_of_lt (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_lt_sqrt (by positivity) ?_)
  nlinarith [mul_pos (sub_pos.mpr hab) (by linarith : (0:ℝ) < b + a)]

/-- The semicircle chord identity: `σ * profileX σ = √(1 - profileX σ ^ 2)`. -/
lemma mul_profileX_eq_semicircle {σ : ℝ} (hσ : 0 < σ) :
    σ * profileX σ = semicircle (profileX σ) := by
  have h1 : 1 - 1 / (1 + σ ^ 2) = σ ^ 2 / (1 + σ ^ 2) := by
    field_simp
    ring
  rw [semicircle, profileX_sq, h1, Real.sqrt_div (by positivity), Real.sqrt_sq hσ.le]
  rw [profileX, mul_one_div, ← Real.sqrt_sq hσ.le, ← Real.sqrt_div (by positivity)]

lemma semicircle_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) : 0 ≤ semicircle t :=
  Real.sqrt_nonneg _

lemma semicircle_even (t : ℝ) : semicircle (-t) = semicircle t := by
  rw [semicircle, semicircle, neg_sq]

/-! ### A monotone limit bound -/

/-- A strictly antitone function on `(0,∞)` whose limit at `0⁺` is `L` stays strictly below
`L`.  (The limit of a monotone function at an endpoint is a supremum, so a value equal to `L`
would force all smaller arguments to exceed `L`.) -/
theorem lt_of_tendsto_of_strictAntiOn_Ioi {f : ℝ → ℝ} {L : ℝ}
    (hanti : StrictAntiOn f (Set.Ioi 0)) (hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∀ s, 0 < s → f s < L := by
  have hloc : ∀ᶠ σ in 𝓝[>] (0 : ℝ), f σ < L + 1 :=
    hlim.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ σ, 0 < σ → σ < δ → f σ < L + 1 := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hloc
    exact ⟨ε, hε, fun σ hσ hσlt =>
      hεsub ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ]; exact hσlt, hσ⟩⟩
  have hδ2 : f (δ / 2) < L + 1 := hδ _ (show (0 : ℝ) < δ / 2 by linarith)
    (show δ / 2 < δ by linarith)
  have hbdd : BddAbove (f '' Set.Ioi 0) := by
    refine ⟨L + 1, ?_⟩
    rintro u ⟨σ, hσ, rfl⟩
    rcases lt_trichotomy σ δ with h | h | h
    · exact le_of_lt (hδ σ hσ h)
    · rw [h]
      exact le_of_lt (lt_of_lt_of_le
        (hanti (show (0 : ℝ) < δ / 2 by linarith) hδpos (show δ / 2 < δ by linarith)) hδ2.le)
    · exact le_of_lt (lt_of_lt_of_le
        (hanti (show (0 : ℝ) < δ / 2 by linarith) hσ (show δ / 2 < σ by linarith)) hδ2.le)
  intro s hs
  have hbdd' : BddAbove (f '' Set.Ioo 0 s) := hbdd.mono (Set.image_mono Set.Ioo_subset_Ioi_self)
  have hsSup : sSup (f '' Set.Ioo 0 s) = L := by
    have h₁ : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (sSup (f '' Set.Ioo 0 s))) :=
      ((hanti.antitoneOn).mono Set.Ioo_subset_Ioi_self).tendsto_nhdsWithin_Ioo_right
        ⟨s / 2, ⟨show (0 : ℝ) < s / 2 by linarith, show s / 2 < s by linarith⟩⟩ hbdd'
    exact tendsto_nhds_unique h₁ hlim
  have hmem : f (s / 2) ∈ f '' Set.Ioo 0 s :=
    ⟨s / 2, ⟨show (0 : ℝ) < s / 2 by linarith, show s / 2 < s by linarith⟩, rfl⟩
  have hle : f (s / 2) ≤ L := by rw [← hsSup]; exact le_csSup hbdd' hmem
  have hlt : f s < f (s / 2) :=
    hanti (show (0 : ℝ) < s / 2 by linarith) hs (show s / 2 < s by linarith)
  exact lt_of_lt_of_le hlt hle

/-! ### The chord-curve predicate and its basic API -/

/-- A chord curve: the right (or left) chord-endpoint function of the profile. -/
structure IsChordCurve (c : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ c (Set.Ioi 0)
  deriv_neg : ∀ s, 0 < s → deriv c s < 0
  tendsto_one : Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 1)
  tail : ∀ s, 1 - tau ≤ s → c s = profileX s

variable {c : ℝ → ℝ}

lemma IsChordCurve.strictAntiOn (hc : IsChordCurve c) : StrictAntiOn c (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) hc.smooth.continuousOn ?_
  intro s hs
  rw [interior_Ioi] at hs
  exact hc.deriv_neg s hs

lemma IsChordCurve.pos (hc : IsChordCurve c) {s : ℝ} (hs : 0 < s) : 0 < c s := by
  rcases lt_trichotomy s (1 - tau) with hlt | heq | hgt
  · have h₁ : c (1 - tau) < c s := hc.strictAntiOn hs one_sub_tau_pos hlt
    rw [hc.tail (1 - tau) le_rfl] at h₁
    exact lt_trans (profileX_pos _) h₁
  · rw [heq, hc.tail (1 - tau) le_rfl]; exact profileX_pos _
  · rw [hc.tail s hgt.le]; exact profileX_pos s

lemma IsChordCurve.lt_one (hc : IsChordCurve c) {s : ℝ} (hs : 0 < s) : c s < 1 :=
  lt_of_tendsto_of_strictAntiOn_Ioi hc.strictAntiOn hc.tendsto_one s hs

/-- Every chord curve is surjective onto `(0,1)`. -/
lemma IsChordCurve.surj (hc : IsChordCurve c) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ σ, 0 < σ ∧ c σ = t := by
  have hsmall : ∀ᶠ σ in 𝓝[>] (0 : ℝ), t < c σ :=
    hc.tendsto_one.eventually (Ioi_mem_nhds ht.2)
  obtain ⟨σ₁, hσ₁pos, hσ₁⟩ : ∃ σ₁, 0 < σ₁ ∧ t < c σ₁ := by
    obtain ⟨σ₁, h₁, h₂⟩ := hsmall.and (show ∀ᶠ σ in 𝓝[>] (0 : ℝ), σ ∈ Set.Ioi (0 : ℝ)
      from self_mem_nhdsWithin) |>.exists
    exact ⟨σ₁, h₂, h₁⟩
  have htpos : 0 < t := ht.1
  obtain ⟨σ₂, hσ₂ge, hσ₂lt⟩ : ∃ σ₂ : ℝ, 1 - tau ≤ σ₂ ∧ profileX σ₂ < t := by
    refine ⟨max (1 - tau) (Real.sqrt (1 / t ^ 2 + 1)), le_max_left _ _, ?_⟩
    rw [profileX, div_lt_iff₀ (Real.sqrt_pos.mpr (by positivity))]
    have hle : Real.sqrt (1 / t ^ 2 + 1) ≤ max (1 - tau) (Real.sqrt (1 / t ^ 2 + 1)) :=
      le_max_right _ _
    have hnn : 0 ≤ max (1 - tau) (Real.sqrt (1 / t ^ 2 + 1)) :=
      le_trans (Real.sqrt_nonneg _) hle
    have hsq : 1 / t ^ 2 + 1 ≤ (max (1 - tau) (Real.sqrt (1 / t ^ 2 + 1))) ^ 2 := by
      have hsq' := (sq_le_sq₀ (a := Real.sqrt (1 / t ^ 2 + 1))
        (b := max (1 - tau) (Real.sqrt (1 / t ^ 2 + 1))) (Real.sqrt_nonneg _) hnn).mpr hle
      rwa [Real.sq_sqrt (by positivity)] at hsq'
    have hmain : 1 / t <
        Real.sqrt (1 + (max (1 - tau) (Real.sqrt (1 / t ^ 2 + 1))) ^ 2) := by
      have h3 : (1 / t) ^ 2 < 1 + (max (1 - tau) (Real.sqrt (1 / t ^ 2 + 1))) ^ 2 := by
        rw [div_pow, one_pow]; linarith
      calc 1 / t = Real.sqrt ((1 / t) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ < Real.sqrt (1 + (max (1 - tau) (Real.sqrt (1 / t ^ 2 + 1))) ^ 2) :=
            Real.sqrt_lt_sqrt (by positivity) h3
    have hthis := mul_lt_mul_of_pos_left hmain htpos
    rw [mul_one_div, div_self (ne_of_gt htpos)] at hthis
    linarith
  have hσ₂pos : 0 < σ₂ := lt_of_lt_of_le one_sub_tau_pos hσ₂ge
  have hcσ₂ : c σ₂ < t := by
    rw [hc.tail σ₂ hσ₂ge]; exact hσ₂lt
  have hσ₁σ₂ : σ₁ < σ₂ := by
    rcases lt_trichotomy σ₁ σ₂ with h | h | h
    · exact h
    · rw [h] at hσ₁; linarith
    · have h' : c σ₁ < c σ₂ := hc.strictAntiOn hσ₂pos hσ₁pos h
      linarith
  have hsub : Set.Icc σ₁ σ₂ ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hσ₁pos hx.1
  have hmem : -t ∈ Set.Icc ((fun σ => -c σ) σ₁) ((fun σ => -c σ) σ₂) :=
    ⟨show -(c σ₁) ≤ -t by linarith, show -t ≤ -(c σ₂) by linarith⟩
  obtain ⟨σ, hσ, hσeq⟩ :=
    intermediate_value_Icc hσ₁σ₂.le (hc.smooth.continuousOn.mono hsub).neg hmem
  exact ⟨σ, lt_of_lt_of_le hσ₁pos hσ.1, by simpa using hσeq⟩

/-! ### The inverse `slopeRight` of a chord curve -/

lemma IsChordCurve.slopeRight_mem (hc : IsChordCurve c) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    slopeRight c t ∈ Set.Ioi 0 ∧ c (slopeRight c t) = t :=
  Function.invFunOn_pos (hc.surj ht)

lemma IsChordCurve.slopeRight_pos (hc : IsChordCurve c) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 < slopeRight c t := (hc.slopeRight_mem ht).1

lemma IsChordCurve.slopeRight_eq (hc : IsChordCurve c) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    c (slopeRight c t) = t := (hc.slopeRight_mem ht).2

lemma IsChordCurve.slopeRight_eq_of (hc : IsChordCurve c) {t σ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hσ : 0 < σ) (h : c σ = t) : σ = slopeRight c t :=
  hc.strictAntiOn.injOn hσ (hc.slopeRight_pos ht)
    (h.trans (hc.slopeRight_eq ht).symm)

/-- The inverse of a chord curve is strictly antitone. -/
lemma IsChordCurve.slopeRight_strictAntiOn (hc : IsChordCurve c) :
    StrictAntiOn (slopeRight c) (Set.Ioo (0 : ℝ) 1) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  by_contra hcon
  have hcon' : slopeRight c t₁ ≤ slopeRight c t₂ := le_of_not_gt hcon
  rcases eq_or_lt_of_le hcon' with heq | hlt'
  · have h₁ := hc.slopeRight_eq ht₂
    rw [← heq] at h₁
    rw [hc.slopeRight_eq ht₁] at h₁
    exact hlt.ne h₁
  · have h := hc.strictAntiOn (hc.slopeRight_pos ht₁) (hc.slopeRight_pos ht₂) hlt'
    rw [hc.slopeRight_eq ht₁, hc.slopeRight_eq ht₂] at h
    exact absurd h (not_lt.mpr hlt.le)

/-! ### The unperturbed part -/

lemma tStar_pos : 0 < tStar := profileX_pos _

lemma tStar_lt_one : tStar < 1 := profileX_lt_one one_sub_tau_pos

/-- On the unperturbed part the inverse slope is at least `1 - τ`. -/
lemma IsChordCurve.slopeRight_ge_tail (hc : IsChordCurve c) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) tStar) : 1 - tau ≤ slopeRight c t := by
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, lt_trans ht.2 tStar_lt_one⟩
  have hc' : c (1 - tau) = tStar := hc.tail (1 - tau) le_rfl
  by_contra hcon
  have hcon' : slopeRight c t < 1 - tau := lt_of_not_ge hcon
  have h₁ : c (slopeRight c t) < c (1 - tau) := by
    rw [hc.slopeRight_eq ht', hc']
    exact ht.2
  have h₂ : c (1 - tau) < c (slopeRight c t) :=
    hc.strictAntiOn (hc.slopeRight_pos ht') one_sub_tau_pos hcon'
  linarith

end

end Work.OddEnvelope
