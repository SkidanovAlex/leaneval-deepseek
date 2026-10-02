import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Metric

noncomputable section

/-- `sin (π u) ≥ 0` on `[0,1]`. -/
private lemma sin_pi_mul_nonneg {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ Real.sin (Real.pi * u) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩
  · exact mul_nonneg (le_of_lt Real.pi_pos) hu.1
  · calc Real.pi * u ≤ Real.pi * 1 :=
        mul_le_mul_of_nonneg_left hu.2 (le_of_lt Real.pi_pos)
      _ = Real.pi := mul_one _

/-- The lower semicircle `u ↦ 1 + δ exp (-(π u) i)` from `1 + δ` to `1 - δ`, which has
nonpositive imaginary part on `[0,1]`. -/
private def lowerArc (δ u : ℝ) : ℂ :=
  1 + (δ : ℂ) * Complex.exp ((((-(Real.pi * u)) : ℝ) : ℂ) * Complex.I)

/-- The upper semicircle `u ↦ 1 + δ exp ((π u) i)` from `1 + δ` to `1 - δ`, which has
nonnegative imaginary part on `[0,1]`. -/
private def upperArc (δ u : ℝ) : ℂ :=
  1 + (δ : ℂ) * Complex.exp ((((Real.pi * u) : ℝ) : ℂ) * Complex.I)

private lemma lowerArc_continuous (δ : ℝ) : Continuous (lowerArc δ) := by
  unfold lowerArc; fun_prop

private lemma lowerArc_zero (δ : ℝ) : lowerArc δ 0 = 1 + (δ : ℂ) := by
  unfold lowerArc; simp

private lemma lowerArc_one (δ : ℝ) : lowerArc δ 1 = 1 - (δ : ℂ) := by
  unfold lowerArc
  have harg : ((((-(Real.pi * 1)) : ℝ) : ℂ)) * Complex.I = -(↑Real.pi * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_neg_pi_mul_I]
  ring

private lemma lowerArc_dist (δ u : ℝ) (hδ : 0 ≤ δ) : dist (lowerArc δ u) 1 = δ := by
  unfold lowerArc
  rw [dist_eq_norm]
  have hsub : 1 + (δ : ℂ) * Complex.exp ((((-(Real.pi * u)) : ℝ) : ℂ) * Complex.I) - 1
      = (δ : ℂ) * Complex.exp ((((-(Real.pi * u)) : ℝ) : ℂ) * Complex.I) := by ring
  rw [hsub, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hδ]

private lemma lowerArc_im (δ u : ℝ) :
    (lowerArc δ u).im = -(δ * Real.sin (Real.pi * u)) := by
  unfold lowerArc
  simp only [Complex.add_im, Complex.one_im, zero_add, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  ring

private lemma upperArc_continuous (δ : ℝ) : Continuous (upperArc δ) := by
  unfold upperArc; fun_prop

private lemma upperArc_zero (δ : ℝ) : upperArc δ 0 = 1 + (δ : ℂ) := by
  unfold upperArc; simp

private lemma upperArc_one (δ : ℝ) : upperArc δ 1 = 1 - (δ : ℂ) := by
  unfold upperArc
  have hπ : Real.pi * 1 = Real.pi := mul_one _
  rw [hπ, Complex.exp_pi_mul_I]
  ring

private lemma upperArc_dist (δ u : ℝ) (hδ : 0 ≤ δ) : dist (upperArc δ u) 1 = δ := by
  unfold upperArc
  rw [dist_eq_norm]
  have hsub : 1 + (δ : ℂ) * Complex.exp ((((Real.pi * u) : ℝ) : ℂ) * Complex.I) - 1
      = (δ : ℂ) * Complex.exp ((((Real.pi * u) : ℝ) : ℂ) * Complex.I) := by ring
  rw [hsub, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hδ]

private lemma upperArc_im (δ u : ℝ) :
    (upperArc δ u).im = δ * Real.sin (Real.pi * u) := by
  unfold upperArc
  simp only [Complex.add_im, Complex.one_im, zero_add, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]

/-- A path `f` inside the circle of radius `δ` about `1`, whose imaginary part never agrees on
`Ioo a b \ {0}` with that of the crosscut `v`, avoids `v '' Icc a b` and stays in the disc. -/
private lemma joined_of_im_ne {v : ℝ → ℂ} {ρ a b δ : ℝ} {f : ℝ → ℂ}
    (_hρ : 0 < ρ) (hv0 : v 0 = 1)
    (hvspha : v a ∈ Metric.sphere (1:ℂ) ρ) (hvsphb : v b ∈ Metric.sphere (1:ℂ) ρ)
    (hδ0 : 0 < δ) (hδρ : δ < ρ)
    (hfcont : ContinuousOn f (Set.Icc (0:ℝ) 1)) (hf0 : f 0 = 1 + (δ:ℂ))
    (hf1 : f 1 = 1 - (δ:ℂ)) (hfd : ∀ u ∈ Set.Icc (0:ℝ) 1, dist (f u) 1 = δ)
    (himne : ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Ioo a b, s ≠ 0 → (f u).im ≠ (v s).im) :
    JoinedIn (Metric.ball (1:ℂ) ρ \ v '' Set.Icc a b) (1 + (δ:ℂ)) (1 - (δ:ℂ)) := by
  refine JoinedIn.ofLine hfcont hf0 hf1 ?_
  rintro y ⟨u, hu, rfl⟩
  rw [Set.mem_sdiff]
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, hfd u hu]
    exact hδρ
  · rintro ⟨s, hs, hvs⟩
    rcases le_or_gt s a with hsa | hsa
    · have hsa' : s = a := le_antisymm hsa hs.1
      have h1 : dist (f u) 1 = ρ := by
        rw [← hvs, hsa']
        exact Metric.mem_sphere.mp hvspha
      rw [hfd u hu] at h1
      exact absurd h1 (ne_of_lt hδρ)
    · rcases le_or_gt b s with hbs | hbs
      · have hsb' : s = b := le_antisymm hs.2 hbs
        have h1 : dist (f u) 1 = ρ := by
          rw [← hvs, hsb']
          exact Metric.mem_sphere.mp hvsphb
        rw [hfd u hu] at h1
        exact absurd h1 (ne_of_lt hδρ)
      · by_cases hs0 : s = 0
        · subst hs0
          rw [hv0] at hvs
          have hdz : dist (f u) 1 = 0 := by rw [← hvs]; simp
          rw [hfd u hu] at hdz
          exact absurd hdz (ne_of_gt hδ0)
        · exact himne u hu s ⟨hsa, hbs⟩ hs0 (congrArg Complex.im hvs.symm)

/-- The arc `v` has strictly positive imaginary part on `Ioo a b \ {0}`: the lower semicircle
joins `1 + δ` and `1 - δ` inside the disc avoiding it. -/
private lemma joined_of_arc_pos {v : ℝ → ℂ} {ρ a b : ℝ} (hρ : 0 < ρ) (hv0 : v 0 = 1)
    (hvspha : v a ∈ Metric.sphere (1:ℂ) ρ) (hvsphb : v b ∈ Metric.sphere (1:ℂ) ρ)
    (harc : ∀ t ∈ Set.Ioo a b, t ≠ 0 → 0 < (v t).im) :
    ∀ δ : ℝ, 0 < δ → δ < ρ →
      JoinedIn (Metric.ball (1:ℂ) ρ \ v '' Set.Icc a b) (1 + (δ:ℂ)) (1 - (δ:ℂ)) := by
  intro δ hδ0 hδρ
  refine joined_of_im_ne hρ hv0 hvspha hvsphb hδ0 hδρ
    (lowerArc_continuous δ).continuousOn (lowerArc_zero δ) (lowerArc_one δ) ?_ ?_
  · intro u hu
    exact lowerArc_dist δ u (le_of_lt hδ0)
  · intro u hu s hs hs0 hcontra
    have h1 : 0 < (v s).im := harc s hs hs0
    rw [← hcontra] at h1
    have h2 : (lowerArc δ u).im ≤ 0 := by
      rw [lowerArc_im]
      have hsp := sin_pi_mul_nonneg hu
      nlinarith [hδ0, hsp]
    linarith

/-- The arc `v` has strictly negative imaginary part on `Ioo a b \ {0}`: the upper semicircle
joins `1 + δ` and `1 - δ` inside the disc avoiding it. -/
private lemma joined_of_arc_neg {v : ℝ → ℂ} {ρ a b : ℝ} (hρ : 0 < ρ) (hv0 : v 0 = 1)
    (hvspha : v a ∈ Metric.sphere (1:ℂ) ρ) (hvsphb : v b ∈ Metric.sphere (1:ℂ) ρ)
    (harc : ∀ t ∈ Set.Ioo a b, t ≠ 0 → (v t).im < 0) :
    ∀ δ : ℝ, 0 < δ → δ < ρ →
      JoinedIn (Metric.ball (1:ℂ) ρ \ v '' Set.Icc a b) (1 + (δ:ℂ)) (1 - (δ:ℂ)) := by
  intro δ hδ0 hδρ
  refine joined_of_im_ne hρ hv0 hvspha hvsphb hδ0 hδρ
    (upperArc_continuous δ).continuousOn (upperArc_zero δ) (upperArc_one δ) ?_ ?_
  · intro u hu
    exact upperArc_dist δ u (le_of_lt hδ0)
  · intro u hu s hs hs0 hcontra
    have h1 : (v s).im < 0 := harc s hs hs0
    rw [← hcontra] at h1
    have h2 : 0 ≤ (upperArc δ u).im := by
      rw [upperArc_im]
      have hsp := sin_pi_mul_nonneg hu
      nlinarith [hδ0, hsp]
    linarith

end

/-- If the crosscut `v` of the disc `ball 1 ρ` through `1` stays on one side of the real axis then
`1 + δ` and `1 - δ` can be joined inside the disc avoiding the arc.  Route: the path
`t ↦ ⟨1 + δ * Real.cos (π * t), - δ * Real.sin (π * t)⟩` from `1 + δ` to `1 - δ` stays in the open
ball (`δ < ρ`) and has nonpositive imaginary part, vanishing only at the two endpoints; `hsame`
(first disjunct) gives strictly positive imaginary part on the arc away from `t = 0`, `hv0` handles
`t = 0`, and `hvspha`/`hvsphb` handle the arc's endpoints (on the sphere, hence outside the ball).
The second disjunct is the mirror image. -/
theorem joined_of_arc_one_side {v : ℝ → ℂ} {ρ a b : ℝ} (hρ : 0 < ρ) (hv0 : v 0 = 1)
    (hvspha : v a ∈ Metric.sphere (1:ℂ) ρ) (hvsphb : v b ∈ Metric.sphere (1:ℂ) ρ)
    (hsame : (∀ t ∈ Set.Ioo a b, t ≠ 0 → 0 < (v t).im) ∨
             (∀ t ∈ Set.Ioo a b, t ≠ 0 → (v t).im < 0)) :
    ∀ δ : ℝ, 0 < δ → δ < ρ →
      JoinedIn (Metric.ball (1:ℂ) ρ \ v '' Set.Icc a b) (1 + (δ:ℂ)) (1 - (δ:ℂ)) := by
  rcases hsame with h | h
  · exact joined_of_arc_pos hρ hv0 hvspha hvsphb h
  · exact joined_of_arc_neg hρ hv0 hvspha hvsphb h

end Work.ELRig
