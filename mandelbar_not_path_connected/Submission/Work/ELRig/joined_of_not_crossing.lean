import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

/-- Norm of a nonnegative real, viewed in `ℂ`. -/
lemma norm_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x := by
  have h : ‖(x : ℂ)‖ = |x| := by simp
  rw [h, abs_of_nonneg hx]

/-- Given `0 < t < r` and two forbidden values, there is `ρ ∈ (t,r)` differing from both. -/
lemma exists_rho_between {t r dL dR : ℝ} (ht : 0 < t) (htr : t < r) :
    ∃ ρ : ℝ, t < ρ ∧ ρ < r ∧ ρ ≠ dL ∧ ρ ≠ dR := by
  have hr : 0 < r := ht.trans htr
  have key : ∀ d : ℝ, (if d < r then d else 0) < r := by
    intro d
    split_ifs with h
    · exact h
    · exact hr
  have huL : (if dL < r then dL else 0) < r := key dL
  have huR : (if dR < r then dR else 0) < r := key dR
  have hmr : max (max (if dL < r then dL else 0) (if dR < r then dR else 0)) t < r :=
    max_lt (max_lt huL huR) htr
  have htm : t ≤ max (max (if dL < r then dL else 0) (if dR < r then dR else 0)) t :=
    le_max_right _ _
  refine ⟨(max (max (if dL < r then dL else 0) (if dR < r then dR else 0)) t + r) / 2,
    by linarith, by linarith, ?_, ?_⟩
  · by_cases h : dL < r
    · have h1 : dL ≤ max (max (if dL < r then dL else 0) (if dR < r then dR else 0)) t := by
        rw [if_pos h]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      exact ne_of_gt (by linarith)
    · have h2 : r ≤ dL := not_lt.mp h
      exact ne_of_lt (by linarith)
  · by_cases h : dR < r
    · have h1 : dR ≤ max (max (if dL < r then dL else 0) (if dR < r then dR else 0)) t := by
        rw [if_pos h]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      exact ne_of_gt (by linarith)
    · have h2 : r ≤ dR := not_lt.mp h
      exact ne_of_lt (by linarith)

/-- If `A` reaches the horizontal line through `p` inside `Icc sL sR`, it equals `p` there. -/
lemma eq_p_of_im_eq {p : ℂ} {A : ℝ → ℂ} {sL sR : ℝ}
    (hline : ∀ s ∈ Set.Icc sL sR, A s ≠ p → (A s).im ≠ p.im)
    {s : ℝ} (hs : s ∈ Set.Icc sL sR) (h : (A s).im = p.im) : A s = p := by
  by_contra hne
  exact hline s hs hne h

/-- "Below" case: a point of `A '' Icc sL sR` at height `≥ p.im` is `p` or an endpoint value. -/
lemma trichotomy_below {p : ℂ} {A : ℝ → ℂ} {sL sR s₀ : ℝ}
    (hAp : A s₀ = p)
    (hL : ∀ s ∈ Set.Ioo sL s₀, (A s).im < p.im)
    (hR : ∀ s ∈ Set.Ioo s₀ sR, (A s).im < p.im)
    {s : ℝ} (hs : s ∈ Set.Icc sL sR) (hge : p.im ≤ (A s).im) :
    A s = p ∨ A s = A sL ∨ A s = A sR := by
  rcases eq_or_lt_of_le hs.1 with hseq | hltL
  · exact Or.inr (Or.inl (by rw [← hseq]))
  · rcases eq_or_lt_of_le hs.2 with hseqR | hltR
    · exact Or.inr (Or.inr (by rw [hseqR]))
    · rcases lt_trichotomy s s₀ with hlt | heq | hgt
      · exact absurd (hL s ⟨hltL, hlt⟩) (not_lt.mpr hge)
      · exact Or.inl (by rw [heq, hAp])
      · exact absurd (hR s ⟨hgt, hltR⟩) (not_lt.mpr hge)

/-- "Above" case: a point of `A '' Icc sL sR` at height `≤ p.im` is `p` or an endpoint value. -/
lemma trichotomy_above {p : ℂ} {A : ℝ → ℂ} {sL sR s₀ : ℝ}
    (hAp : A s₀ = p)
    (hL : ∀ s ∈ Set.Ioo sL s₀, p.im < (A s).im)
    (hR : ∀ s ∈ Set.Ioo s₀ sR, p.im < (A s).im)
    {s : ℝ} (hs : s ∈ Set.Icc sL sR) (hle : (A s).im ≤ p.im) :
    A s = p ∨ A s = A sL ∨ A s = A sR := by
  rcases eq_or_lt_of_le hs.1 with hseq | hltL
  · exact Or.inr (Or.inl (by rw [← hseq]))
  · rcases eq_or_lt_of_le hs.2 with hseqR | hltR
    · exact Or.inr (Or.inr (by rw [hseqR]))
    · rcases lt_trichotomy s s₀ with hlt | heq | hgt
      · exact absurd (hL s ⟨hltL, hlt⟩) (not_lt.mpr hle)
      · exact Or.inl (by rw [heq, hAp])
      · exact absurd (hR s ⟨hgt, hltR⟩) (not_lt.mpr hle)

/-- `sin (π u) ≥ 0` on the unit interval. -/
lemma sin_pi_mul_nonneg {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ Real.sin (Real.pi * u) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩
  · exact mul_nonneg (le_of_lt Real.pi_pos) hu.1
  · calc Real.pi * u ≤ Real.pi * 1 :=
          mul_le_mul_of_nonneg_left hu.2 (le_of_lt Real.pi_pos)
      _ = Real.pi := mul_one _

/-- Joining `p + t` to `p + ρ` by the radial segment along the real axis through `p`. -/
lemma joined_radial_pos {p : ℂ} {r t ρ : ℝ} {A : ℝ → ℂ} {sL sR : ℝ}
    (hline : ∀ s ∈ Set.Icc sL sR, A s ≠ p → (A s).im ≠ p.im)
    (ht : 0 < t) (htρ : t < ρ) (hρr : ρ < r) :
    JoinedIn (Metric.ball p r \ (A '' Set.Icc sL sR)) (p + (t : ℂ)) (p + (ρ : ℂ)) := by
  refine JoinedIn.ofLine (f := fun u : ℝ => p + (((t + u * (ρ - t)) : ℝ) : ℂ)) ?_ ?_ ?_ ?_
  · fun_prop
  · simp
  · have h : t + 1 * (ρ - t) = ρ := by ring
    rw [h]
  · rintro y ⟨u, hu, rfl⟩
    have hu0 : (0 : ℝ) ≤ u := hu.1
    have hu1 : u ≤ 1 := hu.2
    have hs0 : 0 < t + u * (ρ - t) := by nlinarith [ht, htρ, hu0, hu1]
    have hsr : t + u * (ρ - t) ≤ ρ := by nlinarith [ht, htρ, hu0, hu1]
    rw [Set.mem_sdiff]
    constructor
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
        norm_ofReal_of_nonneg (le_of_lt hs0)]
      exact lt_of_le_of_lt hsr hρr
    · rintro ⟨s', hs', hAs'⟩
      have him : (A s').im = p.im := by
        rw [hAs', Complex.add_im, Complex.ofReal_im, add_zero]
      have hp := eq_p_of_im_eq hline hs' him
      rw [hAs'] at hp
      have hzero : t + u * (ρ - t) = 0 := by
        have hc := congrArg Complex.re hp
        simp at hc
        linarith
      linarith

/-- Joining `p - ρ` to `p - t` by the radial segment along the real axis through `p`. -/
lemma joined_radial_neg {p : ℂ} {r t ρ : ℝ} {A : ℝ → ℂ} {sL sR : ℝ}
    (hline : ∀ s ∈ Set.Icc sL sR, A s ≠ p → (A s).im ≠ p.im)
    (ht : 0 < t) (htρ : t < ρ) (hρr : ρ < r) :
    JoinedIn (Metric.ball p r \ (A '' Set.Icc sL sR)) (p - (ρ : ℂ)) (p - (t : ℂ)) := by
  refine JoinedIn.ofLine (f := fun u : ℝ => p - (((ρ + u * (t - ρ)) : ℝ) : ℂ)) ?_ ?_ ?_ ?_
  · fun_prop
  · simp
  · have h : ρ + 1 * (t - ρ) = t := by ring
    rw [h]
  · rintro y ⟨u, hu, rfl⟩
    have hu0 : (0 : ℝ) ≤ u := hu.1
    have hu1 : u ≤ 1 := hu.2
    have htn : t - ρ ≤ 0 := le_of_lt (sub_neg.mpr htρ)
    have hs_ge : t ≤ ρ + u * (t - ρ) := by
      have hmul : (t - ρ) ≤ u * (t - ρ) := by
        have := mul_le_mul_of_nonpos_right hu1 htn
        simpa using this
      linarith
    have hs_le : ρ + u * (t - ρ) ≤ ρ := by
      have : u * (t - ρ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0 htn
      linarith
    have hs0 : 0 < ρ + u * (t - ρ) := lt_of_lt_of_le ht hs_ge
    rw [Set.mem_sdiff]
    constructor
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 : p - (((ρ + u * (t - ρ)) : ℝ) : ℂ) - p =
          -(((ρ + u * (t - ρ)) : ℝ) : ℂ) := by ring
      rw [h1, norm_neg, norm_ofReal_of_nonneg (le_of_lt hs0)]
      exact lt_of_le_of_lt hs_le hρr
    · rintro ⟨s', hs', hAs'⟩
      have him : (A s').im = p.im := by
        rw [hAs', Complex.sub_im, Complex.ofReal_im, sub_zero]
      have hp := eq_p_of_im_eq hline hs' him
      rw [hAs'] at hp
      have hzero : ρ + u * (t - ρ) = 0 := by
        have hc := congrArg Complex.re hp
        simp at hc
        linarith
      linarith

/-- The upper semicircle from `p + ρ` to `p - ρ`, in the "below" case. -/
lemma joined_arc_below {p : ℂ} {r ρ : ℝ} {A : ℝ → ℂ} {sL sR s₀ : ℝ}
    (hAp : A s₀ = p)
    (hL : ∀ s ∈ Set.Ioo sL s₀, (A s).im < p.im)
    (hR : ∀ s ∈ Set.Ioo s₀ sR, (A s).im < p.im)
    (hρ0 : 0 < ρ) (hρr : ρ < r)
    (hdL : ρ ≠ dist (A sL) p) (hdR : ρ ≠ dist (A sR) p) :
    JoinedIn (Metric.ball p r \ (A '' Set.Icc sL sR)) (p + (ρ : ℂ)) (p - (ρ : ℂ)) := by
  have hρnorm : ‖(ρ : ℂ)‖ = ρ := norm_ofReal_of_nonneg (le_of_lt hρ0)
  refine JoinedIn.ofLine
    (f := fun u : ℝ => p + (ρ : ℂ) * Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I))
    ?_ ?_ ?_ ?_
  · fun_prop
  · simp
  · have hexp : Complex.exp (((Real.pi * 1 : ℝ) : ℂ) * Complex.I) = -1 := by
      simp [Complex.exp_pi_mul_I]
    rw [hexp]
    ring
  · rintro y ⟨u, hu, rfl⟩
    have hf : (p + (ρ : ℂ) * Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I)).im
        = p.im + ρ * Real.sin (Real.pi * u) := by
      rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_im]
      ring
    have hFdist : dist (p + (ρ : ℂ) * Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I)) p
        = ρ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
        mul_one, hρnorm]
    have hFne : p + (ρ : ℂ) * Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) ≠ p :=
      dist_pos.mp (by rw [hFdist]; exact hρ0)
    rw [Set.mem_sdiff]
    constructor
    · rw [Metric.mem_ball, hFdist]
      exact hρr
    · rintro ⟨s, hs, hAs⟩
      dsimp only at hAs
      have him : p.im ≤ (A s).im := by
        rw [hAs, hf]
        have hsin := sin_pi_mul_nonneg hu
        have : 0 ≤ ρ * Real.sin (Real.pi * u) := mul_nonneg (le_of_lt hρ0) hsin
        linarith
      rcases trichotomy_below hAp hL hR hs him with h1 | h2 | h3
      · exact hFne (by rw [← hAs, h1])
      · have : ρ = dist (A sL) p := by rw [← hFdist, ← hAs, h2]
        exact hdL this
      · have : ρ = dist (A sR) p := by rw [← hFdist, ← hAs, h3]
        exact hdR this

/-- The lower semicircle from `p + ρ` to `p - ρ`, in the "above" case. -/
lemma joined_arc_above {p : ℂ} {r ρ : ℝ} {A : ℝ → ℂ} {sL sR s₀ : ℝ}
    (hAp : A s₀ = p)
    (hL : ∀ s ∈ Set.Ioo sL s₀, p.im < (A s).im)
    (hR : ∀ s ∈ Set.Ioo s₀ sR, p.im < (A s).im)
    (hρ0 : 0 < ρ) (hρr : ρ < r)
    (hdL : ρ ≠ dist (A sL) p) (hdR : ρ ≠ dist (A sR) p) :
    JoinedIn (Metric.ball p r \ (A '' Set.Icc sL sR)) (p + (ρ : ℂ)) (p - (ρ : ℂ)) := by
  have hρnorm : ‖(ρ : ℂ)‖ = ρ := norm_ofReal_of_nonneg (le_of_lt hρ0)
  refine JoinedIn.ofLine
    (f := fun u : ℝ => p + (ρ : ℂ) * Complex.exp ((((-(Real.pi * u)) : ℝ) : ℂ) * Complex.I))
    ?_ ?_ ?_ ?_
  · fun_prop
  · simp
  · have hexp : Complex.exp ((((-(Real.pi * 1)) : ℝ) : ℂ) * Complex.I) = -1 := by
      rw [Complex.ext_iff]
      constructor
      · rw [Complex.exp_ofReal_mul_I_re]; simp [Real.cos_neg, Real.cos_pi]
      · rw [Complex.exp_ofReal_mul_I_im]; simp [Real.sin_neg, Real.sin_pi]
    rw [hexp]
    ring
  · rintro y ⟨u, hu, rfl⟩
    have hf : (p + (ρ : ℂ) * Complex.exp ((((-(Real.pi * u)) : ℝ) : ℂ) * Complex.I)).im
        = p.im + ρ * Real.sin (-(Real.pi * u)) := by
      rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_im]
      ring
    have hFdist : dist (p + (ρ : ℂ) * Complex.exp ((((-(Real.pi * u)) : ℝ) : ℂ) * Complex.I)) p
        = ρ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
        mul_one, hρnorm]
    have hFne : p + (ρ : ℂ) * Complex.exp ((((-(Real.pi * u)) : ℝ) : ℂ) * Complex.I) ≠ p :=
      dist_pos.mp (by rw [hFdist]; exact hρ0)
    rw [Set.mem_sdiff]
    constructor
    · rw [Metric.mem_ball, hFdist]
      exact hρr
    · rintro ⟨s, hs, hAs⟩
      dsimp only at hAs
      have him : (A s).im ≤ p.im := by
        rw [hAs, hf]
        have hsin : Real.sin (-(Real.pi * u)) ≤ 0 := by
          rw [Real.sin_neg]
          have := sin_pi_mul_nonneg hu
          linarith
        have : ρ * Real.sin (-(Real.pi * u)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hρ0) hsin
        linarith
      rcases trichotomy_above hAp hL hR hs him with h1 | h2 | h3
      · exact hFne (by rw [← hAs, h1])
      · have : ρ = dist (A sL) p := by rw [← hFdist, ← hAs, h2]
        exact hdL this
      · have : ρ = dist (A sR) p := by rw [← hFdist, ← hAs, h3]
        exact hdR this

/-- The mandelbar "not crossing" configuration joins `p + t` and `p - t` inside the
punctured ball. -/
theorem joined_of_not_crossing {p : ℂ} {r : ℝ} (hr : 0 < r) {A : ℝ → ℂ} {sL sR s₀ : ℝ}
    (hsL : sL < s₀) (hsR : s₀ < sR)
    (hAc : ContinuousOn A (Set.Icc sL sR)) (hAp : A s₀ = p)
    (hline : ∀ s ∈ Set.Icc sL sR, A s ≠ p → (A s).im ≠ p.im)
    (hsame : ((∀ s ∈ Set.Ioo sL s₀, (A s).im < p.im) ∧ (∀ s ∈ Set.Ioo s₀ sR, (A s).im < p.im)) ∨
      ((∀ s ∈ Set.Ioo sL s₀, p.im < (A s).im) ∧ (∀ s ∈ Set.Ioo s₀ sR, p.im < (A s).im))) :
    ∀ t : ℝ, 0 < t → t < r →
      JoinedIn (Metric.ball p r \ (A '' Set.Icc sL sR)) (p + (t : ℂ)) (p - (t : ℂ)) := by
  intro t ht0 htr
  obtain ⟨ρ, htρ, hρr, hdL, hdR⟩ :=
    exists_rho_between (t := t) (r := r) (dL := dist (A sL) p) (dR := dist (A sR) p) ht0 htr
  have hρ0 : 0 < ρ := lt_trans ht0 htρ
  rcases hsame with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · exact (joined_radial_pos hline ht0 htρ hρr).trans
      ((joined_arc_below hAp hL hR hρ0 hρr hdL hdR).trans
        (joined_radial_neg hline ht0 htρ hρr))
  · exact (joined_radial_pos hline ht0 htρ hρr).trans
      ((joined_arc_above hAp hL hR hρ0 hρr hdL hdR).trans
        (joined_radial_neg hline ht0 htρ hρr))

end Work.ELRig
