import Mathlib

namespace Work.HornSC.JC

/-- Auxiliary: if there is a direction `d ≠ 0` such that every point of `S` lies strictly on the
`d`-negative side of `z` (in the sense that `Re((w - z) * conj d) < 0`), then the ray
`{z + t·d | t ≥ 0}` avoids `S`, joins `z` to infinity, and hence the component of `z` in `Sᶜ` is
unbounded. -/
private lemma not_isBounded_of_direction {S : Set ℂ} {z d : ℂ} (hd : d ≠ 0)
    (havoid : ∀ w ∈ S, ((w - z) * star d).re < 0) :
    ¬ Bornology.IsBounded (connectedComponentIn Sᶜ z) := by
  have hcont : Continuous (fun t : ℝ => z + (t : ℂ) * d) := by fun_prop
  have hpre : IsPreconnected ((fun t : ℝ => z + (t : ℂ) * d) '' Set.Ici 0) :=
    isPreconnected_Ici.image _ hcont.continuousOn
  have hz : z ∈ (fun t : ℝ => z + (t : ℂ) * d) '' Set.Ici 0 := ⟨0, by simp, by simp⟩
  have hsub : (fun t : ℝ => z + (t : ℂ) * d) '' Set.Ici 0 ⊆ Sᶜ := by
    rintro w ⟨t, ht, rfl⟩
    simp only [Set.mem_compl_iff]
    intro hwS
    have h1 := havoid _ hwS
    have h2 : ((z + (t:ℂ)*d - z) * star d).re = t * Complex.normSq d := by
      rw [add_sub_cancel_left, Complex.star_def, mul_assoc, Complex.mul_conj]
      simp
    rw [h2] at h1
    have h3 : 0 ≤ t * Complex.normSq d := mul_nonneg ht (Complex.normSq_nonneg d)
    linarith
  have hcomp := hpre.subset_connectedComponentIn hz hsub
  intro hB
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall z).1 hB
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  set t : ℝ := (|r| + 1) / ‖d‖ with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hmem := hcomp ⟨t, ht0, rfl⟩
  have hmemcl := hr hmem
  rw [Metric.mem_closedBall] at hmemcl
  have hdist : dist (z + (t:ℂ)*d) z = |r| + 1 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, ht,
      div_mul_cancel₀ _ (ne_of_gt hdpos)]
  rw [hdist] at hmemcl
  have := le_abs_self r
  linarith

/-- **A set all of whose points lie strictly on one side of a point has an unbounded complementary
component there.** Equivalently: the point `z` is joined to infinity by a ray avoiding `S`. -/
theorem componentIn_unbounded_of_halfplane {S : Set ℂ} {z : ℂ}
    (h : (∀ w ∈ S, w.re < z.re) ∨ (∀ w ∈ S, z.re < w.re) ∨ (∀ w ∈ S, w.im < z.im)
      ∨ (∀ w ∈ S, z.im < w.im)) :
    ¬ Bornology.IsBounded (connectedComponentIn Sᶜ z) := by
  rcases h with h1 | h2 | h3 | h4
  · exact not_isBounded_of_direction one_ne_zero (by
      intro w hw
      have hw' := h1 w hw
      have : ((w - z) * star (1:ℂ)).re = w.re - z.re := by simp
      linarith)
  · refine not_isBounded_of_direction (d := -1) (by norm_num) (by
      intro w hw
      have hw' := h2 w hw
      have : ((w - z) * star (-1:ℂ)).re = z.re - w.re := by simp
      linarith)
  · refine not_isBounded_of_direction (d := Complex.I) Complex.I_ne_zero (by
      intro w hw
      have hw' := h3 w hw
      have : ((w - z) * star Complex.I).re = w.im - z.im := by simp
      linarith)
  · refine not_isBounded_of_direction (d := -Complex.I) (by simp) (by
      intro w hw
      have hw' := h4 w hw
      have : ((w - z) * star (-Complex.I)).re = z.im - w.im := by simp
      linarith)

end Work.HornSC.JC
