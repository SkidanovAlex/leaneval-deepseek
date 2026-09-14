import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Commons.Analysis.Calculus.mean_value_inequality_absolutelyContinuous

namespace Commons.Analysis.Calculus

/-- Corrected form of `hasDerivAt_of_ae_deriv_eq_continuousOn`: with the additional assumption that
the codomain `F` is finite dimensional (so that absolutely continuous maps are a.e. differentiable
by Rademacher's theorem), the conclusion does hold.

Suggested proof: fix `t ∈ (a,b)` and `ε > 0`; pick `δ > 0` with `‖P s - P t‖ < ε` for `|s - t| < δ`
and `(t-δ, t+δ) ⊆ (a,b)`.  On `[t, s]` (resp. `[s, t]`) apply the mean value inequality for
absolutely continuous maps -- `Commons.Analysis.Calculus.mean_value_inequality_absolutelyContinuous`
-- to `s' ↦ f s' - (s' - t) • P t`, whose a.e. derivative is `P s' - P t` (uses that `f` is a.e.
differentiable, from `AbsolutelyContinuousOnInterval.boundedVariationOn` together with
`BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`), bounding it by `ε`.  This gives
`‖f s - f t - (s - t) • P t‖ ≤ ε * |s - t|` near `t`, i.e. `HasDerivAt f (P t) t`. -/
theorem hasDerivAt_of_ae_deriv_eq_continuousOn_finiteDimensional {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f P : ℝ → F} {a b : ℝ} (hab : a < b) (hac : AbsolutelyContinuousOnInterval f a b)
    (hP : ContinuousOn P (Set.Icc a b))
    (h : Filter.Eventually (fun t => t ∈ Set.Ioo a b → deriv f t = P t)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℝ))) :
    ∀ t ∈ Set.Ioo a b, HasDerivAt f (P t) t := by
  intro t ht
  rw [Set.mem_Ioo] at ht
  obtain ⟨hta, htb⟩ := ht
  have ht_Icc : t ∈ Set.Icc a b := ⟨hta.le, htb.le⟩
  have hcontWithin : ContinuousWithinAt P (Set.Icc a b) t := hP.continuousWithinAt ht_Icc
  have hdiff : ∀ᵐ x, x ∈ Set.uIcc a b → DifferentiableAt ℝ f x :=
    hac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := (Metric.continuousWithinAt_iff.mp hcontWithin) ε hε
  set δ : ℝ := min (min (t - a) (b - t)) δ₂ with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (lt_min (by linarith) (by linarith)) hδ₂pos
  have hδ_le_ta : δ ≤ t - a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ_le_bt : δ ≤ b - t := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ_le_δ₂ : δ ≤ δ₂ := min_le_right _ _
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδpos] with hh hhball
  have habs : |hh| < δ := by
    have := Metric.mem_ball.mp hhball
    rwa [Real.dist_eq, sub_zero] at this
  obtain ⟨habs_lo, habs_hi⟩ := abs_lt.mp habs
  have hsab : t + hh ∈ Set.Ioo a b := by
    rw [Set.mem_Ioo]
    constructor <;> linarith
  set g : ℝ → F := (f - fun _ => f t) - fun u => (u - t) • P t with hgdef
  rcases lt_trichotomy hh 0 with hneg | hzero | hpos
  · -- hh < 0 : interval [t+hh, t]
    have hsub : Set.uIcc (t + hh) t ⊆ Set.uIcc a b := by
      rw [Set.uIcc_of_le (by linarith : t + hh ≤ t), Set.uIcc_of_le hab.le]
      exact Set.Icc_subset_Icc (le_of_lt hsab.1) (le_of_lt htb)
    have hgac : AbsolutelyContinuousOnInterval g (t + hh) t := by
      have h1 : AbsolutelyContinuousOnInterval f (t + hh) t := hac.mono hsub
      have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => f t) (t + hh) t := by
        apply ContDiffOn.absolutelyContinuousOnInterval; fun_prop
      have h3 : AbsolutelyContinuousOnInterval (fun u : ℝ => (u - t) • P t) (t + hh) t := by
        apply ContDiffOn.absolutelyContinuousOnInterval; fun_prop
      have hh' := (h1.sub h2).sub h3
      simpa [hgdef] using hh'
    have hderiv : ∀ᵐ u, u ∈ Set.Ioo (t + hh) t → HasDerivAt g (deriv f u - P t) u := by
      filter_upwards [h, hdiff] with u hu hdiffu
      intro huI
      have hua : u ∈ Set.Ioo a b := by
        rw [Set.mem_Ioo] at huI ⊢; exact ⟨by linarith [huI.1, hsab.1], by linarith [huI.2, htb]⟩
      have huIcc : u ∈ Set.uIcc a b := by
        rw [Set.uIcc_of_le hab.le]; exact ⟨hua.1.le, hua.2.le⟩
      have hf' : HasDerivAt f (deriv f u) u := (hdiffu huIcc).hasDerivAt
      have hc : HasDerivAt (fun _ : ℝ => f t) 0 u := hasDerivAt_const u (f t)
      have haff : HasDerivAt (fun v : ℝ => (v - t) • P t) (P t) u := by
        have h1 : HasDerivAt (fun v : ℝ => v - t) (1:ℝ) u := (hasDerivAt_id u).sub_const t
        simpa using h1.smul_const (P t)
      have hh' : HasDerivAt ((f - fun _ => f t) - fun v => (v - t) • P t)
          (deriv f u - 0 - P t) u := (hf'.sub hc).sub haff
      simpa [hgdef] using hh'
    have hbound : ∀ᵐ u, u ∈ Set.Ioo (t + hh) t → ‖deriv f u - P t‖ ≤ ε := by
      filter_upwards [h] with u hu
      intro huI
      have hua : u ∈ Set.Ioo a b := by
        rw [Set.mem_Ioo] at huI ⊢; exact ⟨by linarith [huI.1, hsab.1], by linarith [huI.2, htb]⟩
      have huIcc : u ∈ Set.Icc a b := ⟨hua.1.le, hua.2.le⟩
      have hdist : dist u t < δ₂ := by
        rw [Real.dist_eq]
        have : |u - t| < δ := by
          rw [abs_lt]; constructor <;> linarith [huI.1, huI.2, habs_lo, habs_hi]
        exact lt_of_lt_of_le this hδ_le_δ₂
      have hPu : dist (P u) (P t) < ε := hδ₂ huIcc hdist
      rw [hu hua, dist_eq_norm] at *
      exact hPu.le
    have hmvt := mean_value_inequality_absolutelyContinuous (d := t + hh) (b := t) (η := ε)
      (g := g) (g' := fun u => deriv f u - P t) (by linarith) hε.le hgac hderiv hbound
    have hgt : g t = 0 := by simp [hgdef]
    have hgs : g (t + hh) = f (t + hh) - f t - hh • P t := by simp [hgdef]
    rw [hgt, hgs, dist_zero_right, show t - (t + hh) = -hh by ring] at hmvt
    rw [Real.norm_eq_abs, abs_of_neg hneg]
    exact hmvt
  · subst hzero
    simp
  · -- hh > 0 : interval [t, t+hh]
    have hsub : Set.uIcc t (t + hh) ⊆ Set.uIcc a b := by
      rw [Set.uIcc_of_le (by linarith : t ≤ t + hh), Set.uIcc_of_le hab.le]
      exact Set.Icc_subset_Icc (le_of_lt hta) (le_of_lt hsab.2)
    have hgac : AbsolutelyContinuousOnInterval g t (t + hh) := by
      have h1 : AbsolutelyContinuousOnInterval f t (t + hh) := hac.mono hsub
      have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => f t) t (t + hh) := by
        apply ContDiffOn.absolutelyContinuousOnInterval; fun_prop
      have h3 : AbsolutelyContinuousOnInterval (fun u : ℝ => (u - t) • P t) t (t + hh) := by
        apply ContDiffOn.absolutelyContinuousOnInterval; fun_prop
      have hh' := (h1.sub h2).sub h3
      simpa [hgdef] using hh'
    have hderiv : ∀ᵐ u, u ∈ Set.Ioo t (t + hh) → HasDerivAt g (deriv f u - P t) u := by
      filter_upwards [h, hdiff] with u hu hdiffu
      intro huI
      have hua : u ∈ Set.Ioo a b := by
        rw [Set.mem_Ioo] at huI ⊢; exact ⟨by linarith [huI.1, hta], by linarith [huI.2, hsab.2]⟩
      have huIcc : u ∈ Set.uIcc a b := by
        rw [Set.uIcc_of_le hab.le]; exact ⟨hua.1.le, hua.2.le⟩
      have hf' : HasDerivAt f (deriv f u) u := (hdiffu huIcc).hasDerivAt
      have hc : HasDerivAt (fun _ : ℝ => f t) 0 u := hasDerivAt_const u (f t)
      have haff : HasDerivAt (fun v : ℝ => (v - t) • P t) (P t) u := by
        have h1 : HasDerivAt (fun v : ℝ => v - t) (1:ℝ) u := (hasDerivAt_id u).sub_const t
        simpa using h1.smul_const (P t)
      have hh' : HasDerivAt ((f - fun _ => f t) - fun v => (v - t) • P t)
          (deriv f u - 0 - P t) u := (hf'.sub hc).sub haff
      simpa [hgdef] using hh'
    have hbound : ∀ᵐ u, u ∈ Set.Ioo t (t + hh) → ‖deriv f u - P t‖ ≤ ε := by
      filter_upwards [h] with u hu
      intro huI
      have hua : u ∈ Set.Ioo a b := by
        rw [Set.mem_Ioo] at huI ⊢; exact ⟨by linarith [huI.1, hta], by linarith [huI.2, hsab.2]⟩
      have huIcc : u ∈ Set.Icc a b := ⟨hua.1.le, hua.2.le⟩
      have hdist : dist u t < δ₂ := by
        rw [Real.dist_eq]
        have : |u - t| < δ := by
          rw [abs_lt]; constructor <;> linarith [huI.1, huI.2, habs_lo, habs_hi]
        exact lt_of_lt_of_le this hδ_le_δ₂
      have hPu : dist (P u) (P t) < ε := hδ₂ huIcc hdist
      rw [hu hua, dist_eq_norm] at *
      exact hPu.le
    have hmvt := mean_value_inequality_absolutelyContinuous (d := t) (b := t + hh) (η := ε)
      (g := g) (g' := fun u => deriv f u - P t) (by linarith) hε.le hgac hderiv hbound
    have hgt : g t = 0 := by simp [hgdef]
    have hgs : g (t + hh) = f (t + hh) - f t - hh • P t := by simp [hgdef]
    rw [hgt, hgs, dist_zero_left, show t + hh - t = hh by ring] at hmvt
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact hmvt

end Commons.Analysis.Calculus