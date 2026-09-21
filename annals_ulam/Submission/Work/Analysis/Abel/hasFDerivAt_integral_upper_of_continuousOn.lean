import Mathlib

namespace Work.Analysis.Abel

open MeasureTheory Set Filter
open scoped Topology Interval

/-- **Local Fréchet differentiability of the upper-limit interval integral.**

If `F : ℝ → ℝ → ℝ` is continuous on the closed box `[x₁,x₂] × [c,d]` and `(x₀,b₀)` is in its
interior (`x₁ < x₀ < x₂`, `c < b₀ < d`), then `p ↦ ∫_{b₀}^{p.2} F p.1 t dt` is Fréchet
differentiable at `(x₀,b₀)` with derivative `(h₁,h₂) ↦ h₂ • F x₀ b₀`. -/
theorem hasFDerivAt_integral_upper_of_continuousOn
    {F : ℝ → ℝ → ℝ} {x₀ b₀ x₁ x₂ c d : ℝ}
    (hx₁ : x₁ < x₀) (hx₂ : x₀ < x₂) (hc : c < b₀) (hd : b₀ < d)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc x₁ x₂ ×ˢ Set.Icc c d)) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ t in b₀..p.2, F p.1 t)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F x₀ b₀)) (x₀, b₀) := by
  -- We verify the defining little-o estimate.  Write `S` for the box on which `F` is continuous
  -- and note that `S` is compact, hence `F` is uniformly continuous on it.
  set S : Set (ℝ × ℝ) := Set.Icc x₁ x₂ ×ˢ Set.Icc c d with hS
  have hx₀mem : x₀ ∈ Set.Icc x₁ x₂ := ⟨hx₁.le, hx₂.le⟩
  have hb₀mem : b₀ ∈ Set.Icc c d := ⟨hc.le, hd.le⟩
  have hptS : (x₀, b₀) ∈ S := by rw [hS]; exact ⟨hx₀mem, hb₀mem⟩
  have huc : UniformContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) S := by
    rw [hS]
    exact (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hF
  rw [uniformContinuousOn_iff_restrict, Metric.uniformContinuous_iff] at huc
  rw [hasFDerivAt_iff_isLittleO]
  simp only [intervalIntegral.integral_same, sub_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  -- `δ` is the uniform-continuity threshold for `ε` on the box.
  obtain ⟨δ, hδpos, hδ⟩ := huc ε hε
  -- The radius of the neighbourhood of `(x₀,b₀)` on which the estimate is valid: it must be
  -- small enough that `p` stays in the box and that the whole segment between `b₀` and `p.2`
  -- lies in `[c,d]`.
  set ρ : ℝ := min δ (min (b₀ - c) (min (d - b₀) (min (x₀ - x₁) (x₂ - x₀)))) with hρ
  have hρpos : 0 < ρ := by
    rw [hρ]
    exact lt_min hδpos
      (lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith))))
  have hρδ : ρ ≤ δ := by rw [hρ]; exact min_le_left _ _
  have hρbc : ρ ≤ b₀ - c := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρdb : ρ ≤ d - b₀ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρx1 : ρ ≤ x₀ - x₁ :=
    le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρx2 : ρ ≤ x₂ - x₀ :=
    le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- Uniform continuity, transferred to points of the box.
  have hucapply : ∀ (x t : ℝ), x ∈ Set.Icc x₁ x₂ → t ∈ Set.Icc c d →
      max |x - x₀| |t - b₀| < δ → ‖F x t - F x₀ b₀‖ < ε := by
    intro x t hx ht hmax
    have hmem : (x, t) ∈ S := by rw [hS]; exact ⟨hx, ht⟩
    have hdist : dist (⟨(x, t), hmem⟩ : ↥S) (⟨(x₀, b₀), hptS⟩ : ↥S) < δ := by
      rw [Subtype.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact hmax
    have h := hδ (a := (⟨(x, t), hmem⟩ : ↥S)) (b := (⟨(x₀, b₀), hptS⟩ : ↥S)) hdist
    rw [dist_eq_norm] at h
    simpa using h
  filter_upwards [Metric.ball_mem_nhds (x₀, b₀) hρpos] with p hp
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hp1ρ : |p.1 - x₀| < ρ := by simpa using hp1
  have hp2ρ : |p.2 - b₀| < ρ := by simpa using hp2
  -- Put the derivative in the shape `h ↦ h.2 * F x₀ b₀`.
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd', smul_eq_mul,
    Prod.snd_sub]
  have hp1mem : p.1 ∈ Set.Icc x₁ x₂ := by
    have h1 := (abs_lt.mp hp1ρ).1
    have h2 := (abs_lt.mp hp1ρ).2
    exact ⟨by linarith, by linarith⟩
  have hp2mem : p.2 ∈ Set.Icc c d := by
    have h1 := (abs_lt.mp hp2ρ).1
    have h2 := (abs_lt.mp hp2ρ).2
    exact ⟨by linarith, by linarith⟩
  -- `t ↦ F p.1 t` is continuous on `[c,d]`, hence on the interval between `b₀` and `p.2`.
  have hcontIcc : ContinuousOn (fun t : ℝ => F p.1 t) (Set.Icc c d) := by
    have hmap : Set.MapsTo (fun t : ℝ => (p.1, t)) (Set.Icc c d) S := fun t ht => by
      rw [hS]; exact ⟨hp1mem, ht⟩
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hsub : Set.uIcc b₀ p.2 ⊆ Set.Icc c d := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans hb₀mem.1 h1, le_trans h2 hp2mem.2⟩
    · exact ⟨le_trans hp2mem.1 h1, le_trans h2 hb₀mem.2⟩
  have hint : IntervalIntegrable (fun t : ℝ => F p.1 t) volume b₀ p.2 :=
    (hcontIcc.mono hsub).intervalIntegrable
  have hconstint : IntervalIntegrable (fun _ : ℝ => F x₀ b₀) volume b₀ p.2 :=
    intervalIntegrable_const
  -- Absorb the linear term into the integral of the constant `F x₀ b₀`.
  have hdecomp : (∫ t in b₀..p.2, F p.1 t) - (p.2 - b₀) * F x₀ b₀
      = ∫ t in b₀..p.2, (F p.1 t - F x₀ b₀) := by
    have hc1 : (∫ _ in b₀..p.2, F x₀ b₀) = (p.2 - b₀) * F x₀ b₀ := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hc1, ← intervalIntegral.integral_sub hint hconstint]
  rw [hdecomp]
  -- Bound the integral by `ε * |p.2 - b₀|` and then by `ε * ‖p - (x₀,b₀)‖`.
  calc ‖∫ t in b₀..p.2, (F p.1 t - F x₀ b₀)‖
      ≤ ε * |p.2 - b₀| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        have htu : t ∈ Set.uIcc b₀ p.2 := Set.uIoc_subset_uIcc ht
        rcases Set.mem_uIcc.mp htu with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- `b₀ ≤ t ≤ p.2`
          have htmem : t ∈ Set.Icc c d := ⟨le_trans hb₀mem.1 h1, le_trans h2 hp2mem.2⟩
          have habs : |t - b₀| ≤ |p.2 - b₀| := by
            rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
          exact le_of_lt (hucapply p.1 t hp1mem htmem
            (max_lt (lt_of_lt_of_le hp1ρ hρδ)
              (lt_of_lt_of_le (lt_of_le_of_lt habs hp2ρ) hρδ)))
        · -- `p.2 ≤ t ≤ b₀`
          have htmem : t ∈ Set.Icc c d := ⟨le_trans hp2mem.1 h1, le_trans h2 hb₀mem.2⟩
          have habs : |t - b₀| ≤ |p.2 - b₀| := by
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
          exact le_of_lt (hucapply p.1 t hp1mem htmem
            (max_lt (lt_of_lt_of_le hp1ρ hρδ)
              (lt_of_lt_of_le (lt_of_le_of_lt habs hp2ρ) hρδ)))
    _ ≤ ε * ‖p - (x₀, b₀)‖ := by
        have h2 : |p.2 - b₀| ≤ ‖p - (x₀, b₀)‖ := by
          rw [← dist_eq_norm, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
          exact le_max_right _ _
        exact mul_le_mul_of_nonneg_left h2 hε.le

end Work.Analysis.Abel
