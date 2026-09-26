import Mathlib

namespace Work.Drive.Mono

/-- Given a compact set `K` and a point `y ∈ K` lying in the affine hyperplane `{f = t}`
and in the half-space `{ℓ ≤ lam}`, there is a point of `frontier K` with the same two
properties.  (The proof only uses that `K` is compact; convexity and nonempty interior
are not needed.) -/
theorem exists_frontier_mem_inter_hyperplane_inter_halfspace {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hKc : Convex ℝ K) (hKcomp : IsCompact K) (hKint : (interior K).Nonempty)
    {f : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ} {ℓ : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ} {t lam : ℝ}
    {y : EuclideanSpace ℝ (Fin 3)}
    (hyK : y ∈ K) (hyf : f y = t) (hyH : ℓ y ≤ lam) :
    ∃ z ∈ frontier K, f z = t ∧ ℓ z ≤ lam := by
  -- The kernel of a linear functional on `ℝ³` is nonzero.
  have hker : LinearMap.ker (f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) ≠ ⊥ := by
    intro h
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp h
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [finrank_euclideanSpace, Module.finrank_self] at hle
    norm_num at hle
  obtain ⟨v, hvker, hvne⟩ :=
    (Submodule.ne_bot_iff (LinearMap.ker (f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ))).mp hker
  have hfv : f v = 0 := hvker
  -- A nonzero direction on which `f` vanishes and `ℓ` is non-increasing.
  obtain ⟨u, hu_ne, hfu, hℓu⟩ : ∃ u : EuclideanSpace ℝ (Fin 3), u ≠ 0 ∧ f u = 0 ∧ ℓ u ≤ 0 := by
    rcases le_or_gt (ℓ v) 0 with h | h
    · exact ⟨v, hvne, hfv, h⟩
    · refine ⟨-v, neg_ne_zero.mpr hvne, ?_, ?_⟩
      · rw [map_neg, hfv, neg_zero]
      · rw [map_neg]; linarith
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  -- The ray `s ↦ y + s • u` starting at `y`.
  set g : ℝ → EuclideanSpace ℝ (Fin 3) := fun s => y + s • u with hg
  have hg_cont : Continuous g := by rw [hg]; fun_prop
  -- The parameters for which the ray stays in `K`.
  set A : Set ℝ := {s : ℝ | 0 ≤ s} ∩ g ⁻¹' K with hA
  have hA_closed : IsClosed A := by
    rw [hA]; exact isClosed_Ici.inter (hKcomp.isClosed.preimage hg_cont)
  have hA_ne : A.Nonempty := ⟨0, by rw [hA]; exact ⟨by simp, by simp [hg, hyK]⟩⟩
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hKcomp.isBounded
  -- `A` is bounded above because `K` is bounded.
  have hBdd : BddAbove A := by
    refine ⟨(R + ‖y‖) / ‖u‖, ?_⟩
    intro s hs
    rw [hA] at hs
    obtain ⟨hs0, hsg⟩ := hs
    have hnorm : ‖y + s • u‖ ≤ R := by
      simpa only [hg] using hR (g s) hsg
    have h2 : |s| * ‖u‖ ≤ R + ‖y‖ := by
      have h3 : ‖s • u‖ ≤ R + ‖y‖ := by
        calc ‖s • u‖ = ‖(y + s • u) - y‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖y + s • u‖ + ‖y‖ := norm_sub_le _ _
          _ ≤ R + ‖y‖ := by linarith
      rwa [norm_smul, Real.norm_eq_abs] at h3
    have h4 : s * ‖u‖ ≤ R + ‖y‖ := by rwa [abs_of_nonneg (by simpa using hs0)] at h2
    rw [le_div_iff₀ hu_pos]
    exact h4
  -- The last point of the ray inside `K` is on the frontier.
  have hsup_mem : sSup A ∈ A := hA_closed.csSup_mem hA_ne hBdd
  have hsup_ge : 0 ≤ sSup A := by
    have h := hsup_mem; rw [hA] at h; simpa using h.1
  have hgsup_mem : g (sSup A) ∈ K := by
    have h := hsup_mem; rw [hA] at h; simpa using h.2
  have hub : ∀ b ∈ A, b ≤ sSup A := fun b hb => le_csSup hBdd hb
  refine ⟨g (sSup A), ?_, ?_, ?_⟩
  · rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hgsup_mem, ?_⟩
    -- points just beyond `sSup A` are outside `K` and accumulate at `g (sSup A)`
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδlt⟩ := exists_pos_mul_lt hε ‖u‖
    refine ⟨g (sSup A + δ), ?_, ?_⟩
    · rw [Set.mem_compl_iff]
      intro hmem
      have hmemA : sSup A + δ ∈ A := by
        rw [hA]
        exact ⟨by simp only [Set.mem_ofPred_eq]; linarith, hmem⟩
      have := hub _ hmemA
      linarith
    · have hdist : dist (g (sSup A)) (g (sSup A + δ)) = δ * ‖u‖ := by
        rw [dist_eq_norm, hg]
        have hsub : y + sSup A • u - (y + (sSup A + δ) • u) = (-δ) • u := by
          rw [add_sub_add_left_eq_sub, ← sub_smul]
          congr 1
          ring
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos]
      rw [hdist, mul_comm δ ‖u‖]
      exact hδlt
  · -- `f` is unchanged along the ray
    rw [hg]
    simp [map_add, map_smul, hyf, hfu]
  · -- `ℓ` does not increase along the ray
    rw [hg]
    have h1 : ℓ (y + sSup A • u) = ℓ y + sSup A * ℓ u := by
      simp [map_add, map_smul]
    rw [h1]
    nlinarith [hyH, hsup_ge, hℓu]

end Work.Drive.Mono
