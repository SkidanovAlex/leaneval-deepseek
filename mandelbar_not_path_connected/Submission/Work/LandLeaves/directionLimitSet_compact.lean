import Mathlib
import Submission.Work.LandLeaves.snailDescentDefs
import Submission.Work.LandLeaves.isCompact_nonempty_isPreconnected_limitSet_of_subset_compact

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Set
open scoped Topology

/-- For a nonzero complex number `z`, the normalised number `z / ‖z‖` lies on the unit circle. -/
private lemma div_norm_mem_sphere (z : ℂ) (hz : z ≠ 0) :
    z / ((‖z‖ : ℝ) : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
  rw [mem_sphere_iff_norm, sub_zero, norm_div]
  have h : ‖(((‖z‖ : ℝ)) : ℂ)‖ = ‖z‖ := by
    rw [show ‖(((‖z‖ : ℝ)) : ℂ)‖ = |(‖z‖ : ℝ)| from RCLike.norm_ofReal (K := ℂ) (‖z‖)]
    exact abs_of_nonneg (norm_nonneg z)
  rw [h]
  exact div_self (norm_ne_zero_iff.mpr hz)

/-- The set `Work.LandLeaves.directionLimitSet q` of limit directions of a path `q : ℝ → ℂ`
which is continuous on `[0,∞)` and never vanishes is compact, nonempty, preconnected, and
contained in the unit circle.

Hint. Reparametrising `t = T + 1/s`, `s ∈ (0,1]`, reduces this to
`Work.LandLeaves.isCompact_nonempty_isPreconnected_limitSet_of_subset_compact` in
`Submission/Work/LandLeaves/isCompact_nonempty_isPreconnected_limitSet_of_subset_compact.lean`
applied to the compact set `Metric.sphere (0:ℂ) 1`, which contains all directions. -/
theorem directionLimitSet_compact {q : ℝ → ℂ}
    (hqc : ContinuousOn q (Set.Ici 0)) (hqne : ∀ t ∈ Set.Ici (0 : ℝ), q t ≠ 0) :
    IsCompact (Work.LandLeaves.directionLimitSet q) ∧
      (Work.LandLeaves.directionLimitSet q).Nonempty ∧
      IsPreconnected (Work.LandLeaves.directionLimitSet q) ∧
      Work.LandLeaves.directionLimitSet q ⊆ Metric.sphere (0 : ℂ) 1 := by
  have hsub : Set.Ici (1:ℝ) ⊆ Set.Ici (0:ℝ) := by
    intro t ht; simp only [Set.mem_Ici] at ht ⊢; linarith
  -- continuity of the direction map `t ↦ q t / ‖q t‖` on the tail `[1,∞)`
  have hwcont : ContinuousOn (fun t : ℝ => q t / ((‖q t‖:ℝ):ℂ)) (Set.Ici 1) := by
    refine ContinuousOn.div (hqc.mono hsub) ?_ ?_
    · exact Complex.continuous_ofReal.comp_continuousOn ((hqc.mono hsub).norm)
    · intro t ht
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hqne t (hsub ht)))
  -- the reparametrised map `s ↦ q (1/s) / ‖q (1/s)‖` is continuous on `(0,1]`
  have hvcont : ContinuousOn (fun s : ℝ => q (1/s) / ((‖q (1/s)‖:ℝ):ℂ)) (Set.Ioc 0 1) := by
    have hinv : ContinuousOn (fun s : ℝ => 1/s) (Set.Ioc 0 1) := by
      have : (fun s : ℝ => 1/s) = Inv.inv := by funext s; rw [one_div]
      rw [this]
      exact continuousOn_inv₀.mono (fun s hs => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hs.1)
    have hmap : Set.MapsTo (fun s : ℝ => 1/s) (Set.Ioc 0 1) (Set.Ici 1) := by
      intro s hs
      simp only [Set.mem_Ici]
      have : (1:ℝ)⁻¹ ≤ s⁻¹ := (inv_le_inv₀ (by norm_num) hs.1).mpr hs.2
      simpa [one_div] using this
    exact hwcont.comp hinv hmap
  -- inversion maps `(0, δ]` onto `[δ⁻¹, ∞)`
  have h1 : ∀ δ : ℝ, 0 < δ →
      (fun s : ℝ => 1/s) '' Set.Ioc 0 δ = Set.Ici δ⁻¹ := by
    intro δ hδ
    ext t
    simp only [Set.mem_image, Set.mem_Ioc, Set.mem_Ici]
    constructor
    · rintro ⟨s, ⟨hs0, hsδ⟩, rfl⟩
      have : δ⁻¹ ≤ s⁻¹ := (inv_le_inv₀ hδ hs0).mpr hsδ
      simpa [one_div] using this
    · intro ht
      have hδinv_pos : 0 < δ⁻¹ := inv_pos.mpr hδ
      have ht0 : 0 < t := lt_of_lt_of_le hδinv_pos ht
      have h2 : 1/t ≤ δ := by
        rw [one_div]
        rw [inv_le_iff_one_le_mul₀ ht0]
        have : 1 ≤ t * δ := (inv_le_iff_one_le_mul₀ hδ).mp ht
        linarith [this]
      refine ⟨1/t, ⟨by rw [one_div]; exact inv_pos.mpr ht0, h2⟩, ?_⟩
      simp [one_div]
  -- the reparametrised truncations are the tail truncations
  have hvimg : ∀ δ : ℝ, 0 < δ →
      (fun s : ℝ => q (1/s) / ((‖q (1/s)‖:ℝ):ℂ)) '' Set.Ioc 0 δ
        = (fun t : ℝ => q t / ((‖q t‖:ℝ):ℂ)) '' Set.Ici δ⁻¹ := by
    intro δ hδ
    rw [← Set.image_image (fun t : ℝ => q t / ((‖q t‖:ℝ):ℂ)) (fun s : ℝ => 1/s) (Set.Ioc 0 δ)]
    rw [h1 δ hδ]
  -- the reparametrised map takes values in the unit circle
  have hvsphere : ∀ s ∈ Set.Ioc (0:ℝ) 1,
      (fun s : ℝ => q (1/s) / ((‖q (1/s)‖:ℝ):ℂ)) s ∈ Metric.sphere (0:ℂ) 1 := by
    intro s hs
    have hge : (1:ℝ) ≤ 1/s := by
      have : (1:ℝ)⁻¹ ≤ s⁻¹ := (inv_le_inv₀ (by norm_num) hs.1).mpr hs.2
      simpa [one_div] using this
    have hne : q (1/s) ≠ 0 := hqne (1/s) (by simp only [Set.mem_Ici]; linarith)
    exact div_norm_mem_sphere (q (1/s)) hne
  -- apply the limit-set lemma to the compact unit circle
  obtain ⟨hc1, hc2, hc3⟩ :=
    isCompact_nonempty_isPreconnected_limitSet_of_subset_compact
      (K := Metric.sphere (0:ℂ) 1) (isCompact_sphere 0 1) (by norm_num : (0:ℝ) < 1)
      hvcont hvsphere
  -- identify the direction limit set with the reparametrised limit set
  have hset : Work.LandLeaves.directionLimitSet q
      = ⋂ δ ∈ Set.Ioc (0:ℝ) 1,
          closure ((fun s : ℝ => q (1/s) / ((‖q (1/s)‖:ℝ):ℂ)) '' Set.Ioc (0:ℝ) δ) := by
    simp only [Work.LandLeaves.directionLimitSet]
    apply le_antisymm
    · intro x hx
      simp only [Set.mem_iInter] at hx ⊢
      intro δ hδ
      rw [hvimg δ hδ.1]
      exact hx δ⁻¹ (by simp only [Set.mem_Ici]; exact le_of_lt (inv_pos.mpr hδ.1))
    · intro x hx
      simp only [Set.mem_iInter] at hx ⊢
      intro T hT
      simp only [Set.mem_Ici] at hT
      have hT1 : (0:ℝ) < T + 1 := by linarith
      have hδmem : (T+1)⁻¹ ∈ Set.Ioc (0:ℝ) 1 :=
        ⟨inv_pos.mpr hT1, (inv_le_one₀ hT1).mpr (by linarith)⟩
      have hthis := hx (T+1)⁻¹ hδmem
      rw [hvimg (T+1)⁻¹ (inv_pos.mpr hT1), inv_inv] at hthis
      exact closure_mono (Set.image_mono (Set.Ici_subset_Ici.mpr (by linarith))) hthis
  rw [hset]
  refine ⟨hc1, hc2, hc3, ?_⟩
  intro x hx
  simp only [Set.mem_iInter] at hx
  have hthis := hx 1 ⟨by norm_num, le_refl 1⟩
  refine closure_minimal ?_ (isCompact_sphere (0:ℂ) 1).isClosed hthis
  rintro y ⟨s, hs, rfl⟩
  exact hvsphere s hs

end Work.LandLeaves
