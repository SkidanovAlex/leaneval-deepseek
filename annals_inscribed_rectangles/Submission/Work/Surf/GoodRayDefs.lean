import Mathlib
import Submission.Work.Drive.ParityDegreeDefs
import Submission.Work.Drive.CrossingDefs

/-!
# Vocabulary for the existence of a good ray direction

We want a direction `u ≠ 0` such that the boundary curve `t ↦ F (sqBoxLoop t)` of the square meets
the *ray* `{c • u : 0 < c}` only in finitely many points, never at the four corners `0, 1, 2, 3`,
and always *transversally*.

This file collects the elementary vocabulary of the construction.  The bad directions are:

* the *tangent cone* `tangentCone F`: the union of the lines `ℝ ∙ F (sqBoxLoop t)` over the times
  `t ≠ 1, 2, 3` at which the boundary curve is tangent to its own radial direction
  (`cross2 (F (sqBoxLoop t)) (deriv (fun s => F (sqBoxLoop s)) t) = 0`); this is the image of
  `(t, c) ↦ c • F (sqBoxLoop t)` on the critical set, a null set by the equal-dimension Sard lemma;

* the *corner lines* `cornerLines F`: the four lines `ℝ ∙ F (sqBoxLoop j)`, `j = 0, 1, 2, 3`.
-/

namespace Work.Surf

open Work.Drive

open scoped Topology

noncomputable section

/-- The value of the boundary curve at the `j`-th corner of the square, `j = 0, 1, 2, 3`. -/
def cornerVal (F : ℝ × ℝ → ℝ × ℝ) (j : Fin 4) : ℝ × ℝ := F (sqBoxLoop ((j : ℕ) : ℝ))

/-- The times, away from the three intermediate corners `1, 2, 3`, at which the boundary curve
`t ↦ F (sqBoxLoop t)` is tangent to its own radial direction. -/
def critTimes (F : ℝ × ℝ → ℝ × ℝ) : Set ℝ :=
  {t : ℝ | t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧
    cross2 (F (sqBoxLoop t)) (deriv (fun s : ℝ => F (sqBoxLoop s)) t) = 0}

/-- The tangent cone: the union of the lines `ℝ ∙ F (sqBoxLoop t)` over the critical times `t`. -/
def tangentCone (F : ℝ × ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ => p.2 • F (sqBoxLoop p.1)) '' (critTimes F ×ˢ Set.univ)

/-- The four lines through the corner values `F (sqBoxLoop j)`, `j = 0, 1, 2, 3`. -/
def cornerLines (F : ℝ × ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  ⋃ j : Fin 4, Set.range (fun a : ℝ => a • cornerVal F j)

/-- The set of bad directions: the tangent cone together with the four corner lines. -/
def badSet (F : ℝ × ℝ → ℝ × ℝ) : Set (ℝ × ℝ) := tangentCone F ∪ cornerLines F

/-- The boundary curve `s ↦ F (sqBoxLoop s)` is differentiable at every parameter `t` which is not
one of the corner parameters `1, 2, 3`. -/
theorem differentiableAt_boundaryCurve (F : ℝ × ℝ → ℝ × ℝ) (hF : ContDiff ℝ 1 F) {t : ℝ}
    (h1 : t ≠ 1) (h2 : t ≠ 2) (h3 : t ≠ 3) :
    DifferentiableAt ℝ (fun s : ℝ => F (sqBoxLoop s)) t := by
  have hFd : DifferentiableAt ℝ F (sqBoxLoop t) :=
    (hF.differentiable (by norm_num)).differentiableAt
  refine hFd.comp t ?_
  rcases lt_or_gt_of_ne h1 with h1' | h1'
  · have hev : (fun s : ℝ => ((s, 0) : ℝ × ℝ)) =ᶠ[𝓝 t] sqBoxLoop := by
      filter_upwards [Iio_mem_nhds h1'] with s hs
      rw [Set.mem_Iio] at hs
      simp only [sqBoxLoop, if_pos (le_of_lt hs)]
    exact hev.differentiableAt_iff.mp (by fun_prop)
  · rcases lt_or_gt_of_ne h2 with h2' | h2'
    · have hev : (fun s : ℝ => ((1, s - 1) : ℝ × ℝ)) =ᶠ[𝓝 t] sqBoxLoop := by
        filter_upwards [Ioi_mem_nhds h1', Iic_mem_nhds h2'] with s hs1 hs2
        rw [Set.mem_Ioi] at hs1
        rw [Set.mem_Iic] at hs2
        simp only [sqBoxLoop, if_neg (not_le.mpr hs1), if_pos hs2]
      exact hev.differentiableAt_iff.mp (by fun_prop)
    · rcases lt_or_gt_of_ne h3 with h3' | h3'
      · have hev : (fun s : ℝ => ((3 - s, 1) : ℝ × ℝ)) =ᶠ[𝓝 t] sqBoxLoop := by
          filter_upwards [Ioi_mem_nhds h1', Ioi_mem_nhds h2', Iic_mem_nhds h3']
            with s hs1 hs2 hs3
          rw [Set.mem_Ioi] at hs1
          rw [Set.mem_Ioi] at hs2
          rw [Set.mem_Iic] at hs3
          simp only [sqBoxLoop, if_neg (not_le.mpr hs1), if_neg (not_le.mpr hs2), if_pos hs3]
        exact hev.differentiableAt_iff.mp (by fun_prop)
      · have hev : (fun s : ℝ => ((0, 4 - s) : ℝ × ℝ)) =ᶠ[𝓝 t] sqBoxLoop := by
          filter_upwards [Ioi_mem_nhds h1', Ioi_mem_nhds h2', Ioi_mem_nhds h3']
            with s hs1 hs2 hs3
          rw [Set.mem_Ioi] at hs1
          rw [Set.mem_Ioi] at hs2
          rw [Set.mem_Ioi] at hs3
          simp only [sqBoxLoop, if_neg (not_le.mpr hs1), if_neg (not_le.mpr hs2),
            if_neg (not_le.mpr hs3)]
        exact hev.differentiableAt_iff.mp (by fun_prop)

/-- The boundary loop at the four corners: each of `0, 1, 2, 3` is the image of a `Fin 4`. -/
lemma exists_fin_of_mem_corners {t : ℝ} (ht : t ∈ ({0, 1, 2, 3} : Set ℝ)) :
    ∃ i : Fin 4, ((i : ℕ) : ℝ) = t := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with h | h | h | h
  · exact ⟨0, by norm_num [h]⟩
  · exact ⟨1, by norm_num [h]⟩
  · exact ⟨2, by norm_num [h]⟩
  · exact ⟨3, by norm_num [h]⟩

/-- The loop closes up at the fourth corner. -/
lemma sqBoxLoop_four : sqBoxLoop (4 : ℝ) = sqBoxLoop 0 := by
  have h1 : sqBoxLoop (4 : ℝ) = (0, 0) := by norm_num [sqBoxLoop]
  have h2 : sqBoxLoop (0 : ℝ) = (0, 0) := by norm_num [sqBoxLoop]
  rw [h1, h2]

/-- The loop stays on the boundary of the square for `t ∈ [0, 4]`. -/
lemma sqBoxLoop_mem_sqBoxBdry {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 4) :
    sqBoxLoop t ∈ sqBoxBdry := by
  obtain ⟨ht0, ht4⟩ := ht
  rcases le_or_gt t 1 with h1 | h1
  · have h : sqBoxLoop t = (t, 0) := by simp only [sqBoxLoop, if_pos h1]
    rw [h, sqBoxBdry, sqBox]
    exact ⟨⟨⟨ht0, h1⟩, ⟨le_refl 0, zero_le_one⟩⟩, Or.inr (Or.inr (Or.inl rfl))⟩
  · rcases le_or_gt t 2 with h2 | h2
    · have h : sqBoxLoop t = (1, t - 1) := by
        simp only [sqBoxLoop, if_neg (not_le.mpr h1), if_pos h2]
      rw [h, sqBoxBdry, sqBox]
      exact ⟨⟨⟨zero_le_one, le_refl 1⟩, ⟨by linarith, by linarith⟩⟩, Or.inr (Or.inl rfl)⟩
    · rcases le_or_gt t 3 with h3 | h3
      · have h : sqBoxLoop t = (3 - t, 1) := by
          simp only [sqBoxLoop, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2), if_pos h3]
        rw [h, sqBoxBdry, sqBox]
        exact ⟨⟨⟨by linarith, by linarith⟩, ⟨zero_le_one, le_refl 1⟩⟩,
          Or.inr (Or.inr (Or.inr rfl))⟩
      · have h : sqBoxLoop t = (0, 4 - t) := by
          simp only [sqBoxLoop, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2),
            if_neg (not_le.mpr h3)]
        rw [h, sqBoxBdry, sqBox]
        exact ⟨⟨⟨le_refl 0, zero_le_one⟩, ⟨by linarith, by linarith⟩⟩, Or.inl rfl⟩

/-- The boundary curve `s ↦ F (sqBoxLoop s)` is continuous. -/
theorem continuous_comp_sqBoxLoop (F : ℝ × ℝ → ℝ × ℝ) (hF : Continuous F) :
    Continuous (fun s : ℝ => F (sqBoxLoop s)) := by
  have h3 : Continuous (fun t : ℝ => (if t ≤ 3 then ((3 - t, 1) : ℝ × ℝ) else (0, 4 - t))) := by
    refine Continuous.if ?_ (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : t ∈ frontier (Set.Iic 3) := ht
    rw [frontier_Iic] at ht'
    rw [ht']
    norm_num
  have h2 : Continuous (fun t : ℝ => (if t ≤ 2 then ((1, t - 1) : ℝ × ℝ) else
      (if t ≤ 3 then ((3 - t, 1) : ℝ × ℝ) else (0, 4 - t)))) := by
    refine Continuous.if ?_ (by fun_prop) h3
    intro t ht
    have ht' : t ∈ frontier (Set.Iic 2) := ht
    rw [frontier_Iic] at ht'
    rw [ht']
    norm_num
  have h1 : Continuous (fun t : ℝ => (if t ≤ 1 then ((t, 0) : ℝ × ℝ) else
      (if t ≤ 2 then ((1, t - 1) : ℝ × ℝ) else
        (if t ≤ 3 then ((3 - t, 1) : ℝ × ℝ) else (0, 4 - t))))) := by
    refine Continuous.if ?_ (by fun_prop) h2
    intro t ht
    have ht' : t ∈ frontier (Set.Iic 1) := ht
    rw [frontier_Iic] at ht'
    rw [ht']
    norm_num
  have hfun : (fun s : ℝ => F (sqBoxLoop s)) = fun t : ℝ => F (if t ≤ 1 then ((t, 0) : ℝ × ℝ)
      else (if t ≤ 2 then ((1, t - 1) : ℝ × ℝ) else
        (if t ≤ 3 then ((3 - t, 1) : ℝ × ℝ) else (0, 4 - t)))) := rfl
  rw [hfun]
  exact hF.comp h1

/-- The bad set is a union of lines through the origin, hence invariant under scaling. -/
lemma smul_mem_badSet (F : ℝ × ℝ → ℝ × ℝ) (c : ℝ) {x : ℝ × ℝ} (hx : x ∈ badSet F) :
    c • x ∈ badSet F := by
  rw [badSet, Set.mem_union] at hx ⊢
  rcases hx with hx | hx
  · left
    rw [tangentCone, Set.mem_image] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨(p.1, c * p.2), ⟨hp.1, Set.mem_univ _⟩, by simp only [smul_smul]⟩
  · right
    rw [cornerLines, Set.mem_iUnion] at hx ⊢
    obtain ⟨j, hx⟩ := hx
    refine ⟨j, ?_⟩
    rw [Set.mem_range] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    exact ⟨c * a, by simp only [smul_smul]⟩
/-- **A `C¹` curve crossing a line transversally stays off it nearby.**  If `g` lies on the line
`ℝ ∙ u` at `t₀` and its derivative there is not parallel to the direction of the line, then `g` meets
that line only at `t₀` in a punctured neighbourhood of `t₀`. -/
theorem eventually_not_parallel_of_hasDerivAt (g : ℝ → ℝ × ℝ) {t₀ : ℝ} {u : ℝ × ℝ}
    (hu : u ≠ 0) (hd : HasDerivAt g (deriv g t₀) t₀) (hpar : ∃ r : ℝ, g t₀ = r • u)
    (hcr : cross2 (g t₀) (deriv g t₀) ≠ 0) :
    ∀ᶠ t in nhdsWithin t₀ ({t₀}ᶜ), ¬ ∃ r : ℝ, g t = r • u := by
  -- the linear functional `v ↦ cross2 v u`
  set L : (ℝ × ℝ) →L[ℝ] ℝ :=
    u.2 • ContinuousLinearMap.fst ℝ ℝ ℝ - u.1 • ContinuousLinearMap.snd ℝ ℝ ℝ with hL
  have hLapp : ∀ v : ℝ × ℝ, L v = cross2 v u := by
    intro v
    simp only [hL, cross2]
    simp
    ring
  have hdL : HasDerivAt (fun t : ℝ => cross2 (g t) u) (cross2 (deriv g t₀) u) t₀ := by
    have h1 : HasFDerivAt (fun v : ℝ × ℝ => L v) L (g t₀) := L.hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => L (g t)) (L (deriv g t₀)) t₀ := by
      simpa only [Function.comp_def] using h1.comp_hasDerivAt t₀ hd
    simpa only [hLapp] using h2
  obtain ⟨r₀, hr₀⟩ := hpar
  have hval : cross2 (g t₀) u = 0 := by
    rw [hr₀, cross2_smul_left, cross2_self, mul_zero]
  have hder_ne : cross2 (deriv g t₀) u ≠ 0 := by
    intro h0
    have h1 : cross2 u (deriv g t₀) = 0 := by rw [cross2_skew, h0, neg_zero]
    rw [hr₀, cross2_smul_left, h1, mul_zero] at hcr
    exact hcr rfl
  have hev : ∀ᶠ t in nhdsWithin t₀ ({t₀}ᶜ),
      slope (fun t : ℝ => cross2 (g t) u) t₀ t ≠ 0 :=
    hdL.tendsto_slope.eventually_ne hder_ne
  filter_upwards [hev] with t ht
  rintro ⟨r, hr⟩
  refine ht ?_
  have hz : cross2 (g t) u = 0 := by
    rw [hr, cross2_smul_left, cross2_self, mul_zero]
  rw [slope_def_field, hz, hval, sub_self, zero_div]

end

end Work.Surf
