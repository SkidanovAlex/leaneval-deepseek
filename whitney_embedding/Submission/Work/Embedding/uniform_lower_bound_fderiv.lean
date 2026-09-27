import Mathlib

set_option linter.style.haveILetI false

namespace Work.Embedding

/-- On a nonempty compact set on which `Dψ` is everywhere injective, `‖Dψ u d‖ / ‖d‖` is
uniformly bounded below by a positive constant.  (For a finite dimensional `E`; if `E` is trivial
any positive `κ` works.) -/
theorem uniform_lower_bound_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ψ : E → F} {s : Set E} (hs : IsCompact s) (hne : s.Nonempty)
    (hψ : ∀ u ∈ s, ContDiffAt ℝ 1 ψ u)
    (hinj : ∀ u ∈ s, Function.Injective (fderiv ℝ ψ u)) :
    ∃ κ > 0, ∀ u ∈ s, ∀ d : E, κ * ‖d‖ ≤ ‖fderiv ℝ ψ u d‖ := by
  by_cases hE : Subsingleton E
  · -- `E` is trivial: every `d` is `0`, so any positive `κ` works.
    refine ⟨1, one_pos, ?_⟩
    intro u _hu d
    rw [hE.elim d 0]
    simp
  · haveI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    -- `Dψ` is continuous on the compact set `s`.
    have hcont : ContinuousOn (fun u => fderiv ℝ ψ u) s :=
      fun u hu => ((hψ u hu).continuousAt_fderiv (by norm_num)).continuousWithinAt
    -- The map `(u, d) ↦ ‖Dψ u d‖` is continuous on `s × sphere`.
    have h1 : ContinuousOn (fun p : E × E => fderiv ℝ ψ p.1)
        (s ×ˢ Metric.sphere (0 : E) 1) := by
      apply hcont.comp'
      · exact continuous_fst.continuousOn
      · intro p hp; exact (Set.mem_prod.mp hp).1
    have h2 : ContinuousOn (fun p : E × E => p.2) (s ×ˢ Metric.sphere (0 : E) 1) :=
      continuous_snd.continuousOn
    have hjoint : ContinuousOn (fun p : E × E => ‖fderiv ℝ ψ p.1 p.2‖)
        (s ×ˢ Metric.sphere (0 : E) 1) :=
      (h1.clm_apply h2).norm
    -- `s × sphere` is compact and nonempty, so `hjoint` attains its minimum there.
    have hK : IsCompact (s ×ˢ Metric.sphere (0 : E) 1) := hs.prod (isCompact_sphere 0 1)
    have hKne : (s ×ˢ Metric.sphere (0 : E) 1).Nonempty :=
      hne.prod (NormedSpace.sphere_nonempty.mpr zero_le_one)
    obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hKne hjoint
    have hp1 : p.1 ∈ s := (Set.mem_prod.mp hp).1
    have hp2 : ‖p.2‖ = 1 := by
      have h := (Set.mem_prod.mp hp).2
      rw [Metric.mem_sphere, dist_zero_right] at h
      exact h
    have hp2ne : p.2 ≠ 0 := by
      intro h; rw [h, norm_zero] at hp2; exact one_ne_zero hp2.symm
    -- The minimum `κ = ‖Dψ p.1 p.2‖` is positive because `Dψ p.1` is injective.
    have hpos : 0 < ‖fderiv ℝ ψ p.1 p.2‖ := by
      rw [norm_pos_iff]
      intro hzero
      exact hp2ne ((hinj p.1 hp1) (by rw [hzero, map_zero]))
    refine ⟨‖fderiv ℝ ψ p.1 p.2‖, hpos, ?_⟩
    intro u hu d
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · have hd' : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
      -- `e := ‖d‖⁻¹ • d` is a unit vector.
      have he_mem : (‖d‖⁻¹) • d ∈ Metric.sphere (0 : E) 1 := by
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ hd'
      have hmem : (u, (‖d‖⁻¹) • d) ∈ s ×ˢ Metric.sphere (0 : E) 1 := ⟨hu, he_mem⟩
      have heq : ‖d‖ • ((‖d‖⁻¹) • d) = d := by
        rw [smul_smul, mul_inv_cancel₀ hd', one_smul]
      -- Homogeneity of a continuous linear map in the norm.
      have key : ∀ (L : E →L[ℝ] F) (c : ℝ) (x : E), 0 ≤ c → ‖L (c • x)‖ = c * ‖L x‖ := by
        intro L c x hc
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      have hfd : ‖fderiv ℝ ψ u (‖d‖ • ((‖d‖⁻¹) • d))‖
          = ‖d‖ * ‖fderiv ℝ ψ u ((‖d‖⁻¹) • d)‖ :=
        key (fderiv ℝ ψ u) ‖d‖ ((‖d‖⁻¹) • d) (norm_nonneg d)
      have hLHS : ‖fderiv ℝ ψ u d‖ = ‖d‖ * ‖fderiv ℝ ψ u ((‖d‖⁻¹) • d)‖ := by
        rw [← hfd, heq]
      have hmain : ‖fderiv ℝ ψ u d‖ = ‖fderiv ℝ ψ u ((‖d‖⁻¹) • d)‖ * ‖d‖ := by
        rw [hLHS]; exact mul_comm _ _
      rw [hmain]
      exact mul_le_mul_of_nonneg_right (hmin hmem) (norm_nonneg d)

end Work.Embedding
