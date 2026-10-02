import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Gen

open Metric Set Filter Topology

/-- **A tube lemma for homogeneous "norm-like" functions.**

Let `g : A × F → ℝ` be continuous, nonnegative, `g x 0 = 0`, `g x v = 0 → v = 0`, and positively
homogeneous in the second variable (`g (x, c • v) = |c| * g (x, v)`); let `F` be a proper normed
`ℝ`-vector space.  If an open set `L ⊆ A × F` contains the full "annulus"
`{v | lo ≤ g (b, v) ≤ hi}` over a point `b`, then the annuli over a whole neighbourhood `U` of `b`
are still contained in `L`.

This is the standard tube lemma, except that the compact set one tubes over has to be extracted
uniformly: near `b`, `g (x, ·)` is comparable to `‖·‖` (the homogeneity turns the extreme value
theorem on the unit sphere into a two-sided bound), so the relevant annuli all lie in one compact
annulus of `F`. -/
theorem tubeOfHomogeneous {A : Type*} [TopologicalSpace A] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [ProperSpace F] (g : A × F → ℝ) (hg : Continuous g)
    (hhom : ∀ x c v, g (x, c • v) = |c| * g (x, v))
    (hpos : ∀ x v, 0 ≤ g (x, v)) (hne : ∀ x v, g (x, v) = 0 → v = 0)
    {lo hi : ℝ} (hlo : 0 < lo) (b : A) {L : Set (A × F)} (hL : IsOpen L)
    (hsub : ∀ v, lo ≤ g (b, v) → g (b, v) ≤ hi → (b, v) ∈ L) :
    ∃ U, U ∈ nhds b ∧ ∀ x ∈ U, ∀ v, lo ≤ g (x, v) → g (x, v) ≤ hi → (x, v) ∈ L := by
  -- If the annulus is empty for all `x` (i.e. `hi < lo`) there is nothing to prove.
  by_cases hhi : hi < lo
  · refine ⟨univ, univ_mem, ?_⟩
    intro x _ v h1 h2
    exact absurd (le_trans h1 h2) (not_le.mpr hhi)
  · rcases subsingleton_or_nontrivial F with hF | hF
    · -- `F` is trivial: then `g (x, v) = 0 < lo` for all `v`, so the conclusion is vacuous.
      refine ⟨univ, univ_mem, ?_⟩
      intro x _ v h1 h2
      have hv : v = 0 := hF.allEq v 0
      subst hv
      have hg0 : g (x, (0 : F)) = 0 := by simpa using hhom x 0 (0 : F)
      rw [hg0] at h1
      exact absurd h1 (not_le.mpr hlo)
    · have hex : ∃ v : F, v ≠ 0 := by
        obtain ⟨a, b, hab⟩ := hF.exists_pair_ne
        rcases eq_or_ne a 0 with ha | ha
        · exact ⟨b, fun hb => hab (by rw [ha, hb])⟩
        · exact ⟨a, ha⟩
      -- The unit sphere, and the extrema of `g (b, ·)` on it.
      set S : Set F := sphere (0 : F) 1 with hSdef
      have hScomp : IsCompact S := isCompact_sphere 0 1
      have hSne : S.Nonempty := by
        obtain ⟨v, hv⟩ := hex
        refine ⟨‖v‖⁻¹ • v, ?_⟩
        rw [hSdef, mem_sphere_iff_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg (norm_nonneg v)]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
      have hcont : Continuous (fun s : F => g (b, s)) :=
        hg.comp (continuous_const.prodMk continuous_id)
      obtain ⟨smin, hsmin, hmin⟩ := hScomp.exists_isMinOn hSne hcont.continuousOn
      obtain ⟨smax, hsmax, hmax⟩ := hScomp.exists_isMaxOn hSne hcont.continuousOn
      have hmin' : ∀ s ∈ S, g (b, smin) ≤ g (b, s) := isMinOn_iff.mp hmin
      have hmax' : ∀ s ∈ S, g (b, s) ≤ g (b, smax) := isMaxOn_iff.mp hmax
      have hαpos : 0 < g (b, smin) := by
        have hne0 : smin ≠ 0 := by
          intro h0
          rw [hSdef, h0] at hsmin
          simp at hsmin
        exact lt_of_le_of_ne (hpos b smin) (fun h => hne0 (hne b smin h.symm))
      have hβge : g (b, smin) ≤ g (b, smax) := hmax' smin hsmin
      have hβpos : 0 < g (b, smax) := lt_of_lt_of_le hαpos hβge
      -- The neighbourhood `u` on which `g (x, ·)` is uniformly comparable to `‖·‖`.
      have hNopen : IsOpen {p : A × F | g (b, smin) / 2 < g p ∧ g p < 2 * g (b, smax)} :=
        (isOpen_lt continuous_const hg).inter (isOpen_lt hg continuous_const)
      have hsubN : {b} ×ˢ S ⊆ {p : A × F | g (b, smin) / 2 < g p ∧ g p < 2 * g (b, smax)} := by
        rintro ⟨x, s⟩ hmem
        obtain ⟨hx, hs⟩ := Set.mem_prod.mp hmem
        rw [mem_singleton_iff] at hx
        subst hx
        exact ⟨lt_of_lt_of_le (by linarith [hαpos]) (hmin' s hs),
          lt_of_le_of_lt (hmax' s hs) (by linarith [hβpos])⟩
      obtain ⟨u, vset, hu_open, hv_open, hbu, hSv, huv⟩ :=
        generalized_tube_lemma isCompact_singleton hScomp hNopen hsubN
      have hc1pos : 0 < g (b, smin) / 2 := by linarith [hαpos]
      have hc2pos : 0 < 2 * g (b, smax) := by linarith [hβpos]
      have hcomp : ∀ x ∈ u, ∀ v : F,
          g (b, smin) / 2 * ‖v‖ ≤ g (x, v) ∧ g (x, v) ≤ 2 * g (b, smax) * ‖v‖ := by
        intro x hx v
        rcases eq_or_ne v 0 with hv | hv
        · subst hv
          have hg0 : g (x, (0 : F)) = 0 := by simpa using hhom x 0 (0 : F)
          rw [hg0, norm_zero, mul_zero, mul_zero]
          exact ⟨le_refl 0, le_refl 0⟩
        · have hvn : ‖v‖⁻¹ • v ∈ S := by
            rw [hSdef, mem_sphere_iff_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
              abs_of_nonneg (norm_nonneg v)]
            exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
          have hvn' : ‖v‖⁻¹ • v ∈ vset := hSv hvn
          have hmem : (x, ‖v‖⁻¹ • v) ∈ u ×ˢ vset := Set.mem_prod.mpr ⟨hx, hvn'⟩
          have hbound := huv hmem
          have hghom : g (x, v) = ‖v‖ * g (x, ‖v‖⁻¹ • v) := by
            have hv_eq : (‖v‖ : ℝ) • (‖v‖⁻¹ • v) = v := by
              rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
            have hh := hhom x ‖v‖ (‖v‖⁻¹ • v)
            rw [hv_eq, abs_of_nonneg (norm_nonneg v)] at hh
            exact hh
          rw [hghom]
          exact ⟨by nlinarith [norm_nonneg v, hbound.1.le],
                 by nlinarith [norm_nonneg v, hbound.2.le]⟩
      -- The compact annulus containing all the `x`-annuli for `x ∈ u`.
      set K : Set F := {v : F | lo / (2 * g (b, smax)) ≤ ‖v‖ ∧ ‖v‖ ≤ hi / (g (b, smin) / 2)} with hKdef
      have hKcomp : IsCompact K := by
        rw [hKdef]
        refine (isCompact_closedBall (0 : F) (hi / (g (b, smin) / 2))).of_isClosed_subset ?_ ?_
        · exact (isClosed_le continuous_const continuous_norm).inter
            (isClosed_le continuous_norm continuous_const)
        · intro v hv
          rw [mem_closedBall, dist_zero_right]
          exact hv.2
      have hZK : ∀ x ∈ u, ∀ v, lo ≤ g (x, v) → g (x, v) ≤ hi → v ∈ K := by
        intro x hx v h1 h2
        have hc := hcomp x hx v
        simp only [hKdef, Set.mem_ofPred_eq]
        refine ⟨?_, ?_⟩
        · rw [div_le_iff₀ hc2pos]; linarith [hc.2]
        · rw [le_div_iff₀ hc1pos]; linarith [hc.1]
      -- The set of bad points.
      set Z : Set (A × F) := {p | lo ≤ g p ∧ g p ≤ hi ∧ p ∉ L} with hZdef
      have hZclosed : IsClosed Z := by
        rw [hZdef]
        exact (isClosed_le continuous_const hg).inter
          ((isClosed_le hg continuous_const).inter hL.isClosed_compl)
      have hb_notin : ¬ (∃ v : F, (b, v) ∈ Z) := by
        rintro ⟨v, hv⟩
        simp only [hZdef, Set.mem_ofPred_eq] at hv
        exact hv.2.2 (hsub v hv.1 hv.2.1)
      have hbK : {b} ×ˢ K ⊆ Zᶜ := by
        rintro ⟨x, v⟩ hmem
        obtain ⟨hx, hv⟩ := Set.mem_prod.mp hmem
        rw [mem_singleton_iff] at hx
        subst hx
        intro hmemZ
        exact hb_notin ⟨v, hmemZ⟩
      obtain ⟨u₀, v₀, hu₀_open, hv₀_open, hbu₀, hKv₀, huv₀⟩ :=
        generalized_tube_lemma isCompact_singleton hKcomp hZclosed.isOpen_compl hbK
      have hu₀K : u₀ ×ˢ K ⊆ Zᶜ := (Set.prod_mono_right hKv₀).trans huv₀
      refine ⟨u₀ ∩ u, ?_, ?_⟩
      · exact inter_mem (hu₀_open.mem_nhds (hbu₀ (by simp))) (hu_open.mem_nhds (hbu (by simp)))
      · intro x hx v h1 h2
        by_contra hxL
        have hZmem : (x, v) ∈ Z := by
          simp only [hZdef, Set.mem_ofPred_eq]
          exact ⟨h1, h2, hxL⟩
        have hvK : v ∈ K := hZK x hx.2 v h1 h2
        have hmem : (x, v) ∈ u₀ ×ˢ K := Set.mem_prod.mpr ⟨hx.1, hvK⟩
        exact (hu₀K hmem) hZmem

end Work.Gen
