import Mathlib

namespace Work.HornFC

/-- A compact subset of the domain of a holomorphic function that is nowhere locally constant
meets every fibre `g ⁻¹' {w}` in only finitely many points.

Indeed, by the principle of isolated zeros, at each point `z` of the domain the function
`g - w` is either identically zero near `z` (which is excluded by `hnl`) or nonzero on a
punctured neighbourhood of `z`; hence every point of `K` has an open neighbourhood meeting
`g ⁻¹' {w}` only in that point.  These neighbourhoods form an open cover of the compact set
`K`, so finitely many of them cover `K`, and the fibre points all lie among the corresponding
centres. -/
theorem finite_inter_preimage_singleton {D : Set ℂ} (hD : IsOpen D) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g D) (hnl : ∀ z ∈ D, ¬ Filter.Eventually (fun u => g u = g z) (nhds z))
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ D) {w : ℂ} :
    (K ∩ g ⁻¹' {w}).Finite := by
  classical
  -- Every point of `K` has an open neighbourhood meeting the fibre `g ⁻¹' {w}` only in itself.
  have hU : ∀ x : K, ∃ U : Set ℂ, IsOpen U ∧ (x : ℂ) ∈ U ∧ U ∩ g ⁻¹' {w} ⊆ {(x : ℂ)} := by
    intro x
    have hxD : (x : ℂ) ∈ D := hKD x.2
    have hgan : AnalyticAt ℂ g (x : ℂ) := hg.analyticAt (hD.mem_nhds hxD)
    -- The isolated-zeros principle applied to `g` and to the constant function `w`.
    rcases AnalyticAt.eventually_eq_or_eventually_ne hgan (analyticAt_const (v := w)) with h1 | h2
    · -- If `g` were eventually equal to `w`, it would be eventually equal to `g x = w`,
      -- contradicting the hypothesis that it is nowhere locally constant.
      have hxw : g (x : ℂ) = w := h1.self_of_nhds
      exact absurd (h1.mono (fun u hu => by rw [hxw]; exact hu)) (hnl (x : ℂ) hxD)
    · -- Otherwise `g` differs from `w` on a punctured neighbourhood; shrink it to an open set.
      rw [eventually_nhdsWithin_iff] at h2
      obtain ⟨s, hs, hsprop⟩ := h2.exists_mem
      refine ⟨interior s, isOpen_interior, mem_interior_iff_mem_nhds.mpr hs, ?_⟩
      rintro u ⟨huU, huw⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      exact hsprop u (interior_subset huU) (by simpa using hne) huw
  choose U hUo hxU hUiso using hU
  -- Extract a finite subcover of `K` from the open cover `U`.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo
    (fun k hk => Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hxU ⟨k, hk⟩⟩)
  -- The fibre points lie among the (finitely many) centres of that subcover.
  refine (t.finite_toSet.image (Subtype.val : K → ℂ)).subset ?_
  rintro z ⟨hzK, hzw⟩
  rcases Set.mem_iUnion.mp (ht hzK) with ⟨x, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hxt, hxUx⟩
  have hzx : z = (x : ℂ) := by
    have : z ∈ U x ∩ g ⁻¹' {w} := ⟨hxUx, hzw⟩
    simpa using hUiso x this
  exact ⟨x, Finset.mem_coe.mpr hxt, by simpa using hzx.symm⟩

end Work.HornFC
