import Mathlib.Analysis.Normed.Order.Lattice

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology

namespace Commons.Topology.Compact

/-- Compactness (tube lemma) form: if `f : ℝ → ℝ → X` is continuous on
`Icc (-1) 1 ×ˢ K` with `K` compact, and `f 0 t ∈ W` for all `t ∈ K` with `W`
open, then `f s t ∈ W` for all `s` in a symmetric interval `Icc (-ε) ε` around
`0` and all `t ∈ K`. -/
theorem exists_pos_forall_mem_of_isCompact {X : Type*} [TopologicalSpace X] {W : Set X}
    (hW : IsOpen W) {K : Set ℝ} (hK : IsCompact K) {f : ℝ → ℝ → X}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc (-1 : ℝ) 1 ×ˢ K))
    (h0 : ∀ t ∈ K, f 0 t ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Icc (-ε) ε, ∀ t ∈ K, f s t ∈ W := by
  let g : ℝ × ℝ → X := fun p => f p.1 p.2
  let S : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ K
  have hfS : ContinuousOn g S := hf
  -- Step 1: `g ⁻¹' W` is a neighbourhood of `{0} × K` within `S`.
  have hn : g ⁻¹' W ∈ 𝓝ˢ[S] ({0} ×ˢ K) := by
    rw [mem_nhdsSetWithin]
    obtain ⟨u, hu_open, hu_eq⟩ := continuousOn_iff'.1 hfS W hW
    refine ⟨u, hu_open, ?_, ?_⟩
    · intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      have hp1' : p.1 = 0 := hp1
      have hgp : g p ∈ W := by
        have hpp : p = (0, p.2) := by ext <;> simp [hp1']
        rw [hpp]
        exact h0 p.2 hp2
      have hpS : p ∈ S := by
        refine ⟨?_, hp2⟩
        rw [hp1']
        exact ⟨by norm_num, by norm_num⟩
      have : p ∈ g ⁻¹' W ∩ S := ⟨hgp, hpS⟩
      rw [hu_eq] at this
      exact this.1
    · intro p hp
      have hp' : p ∈ g ⁻¹' W ∩ S := by rw [hu_eq]; exact hp
      exact hp'.1
  -- Step 2: the tube lemma.
  obtain ⟨u, hu_mem, v, hv_mem, huv⟩ :=
    generalized_tube_lemma' (s := ({0} : Set ℝ)) (s' := Set.Icc (-1 : ℝ) 1)
      (t := K) (t' := K) (n := g ⁻¹' W) isCompact_singleton hK hn
  -- Step 3: extract `ε` from `u ∈ 𝓝[Icc (-1) 1] {0}`.
  have hu_mem' : u ∈ 𝓝 (0 : ℝ) := by
    rw [nhdsSetWithin_singleton] at hu_mem
    have hIcc : Set.Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
      Icc_mem_nhds (by norm_num) (by norm_num)
    rwa [nhdsWithin_eq_nhds.2 hIcc] at hu_mem
  obtain ⟨l, r, h0mem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hu_mem'
  have hl : l < 0 := h0mem.1
  have hr : 0 < r := h0mem.2
  have hv : K ⊆ v := by
    rw [nhdsSetWithin_self] at hv_mem
    exact hv_mem
  refine ⟨min (-l) r / 2, ?_, ?_⟩
  · have hm : 0 < min (-l) r := lt_min (by linarith) hr
    exact div_pos hm (by norm_num)
  · intro s hs t ht
    have hsIoo : s ∈ Set.Ioo l r := by
      refine ⟨?_, ?_⟩
      · have h1 : min (-l) r ≤ -l := min_le_left _ _
        linarith [hs.1]
      · have h2 : min (-l) r ≤ r := min_le_right _ _
        linarith [hs.2]
    have hu_s : s ∈ u := hsub hsIoo
    have ht_v : t ∈ v := hv ht
    have hmem : (s, t) ∈ u ×ˢ v := ⟨hu_s, ht_v⟩
    exact huv hmem

end Commons.Topology.Compact