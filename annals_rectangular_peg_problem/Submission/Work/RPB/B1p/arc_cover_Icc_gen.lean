import Mathlib

namespace Work.RPB.B1p

theorem arc_cover_Icc_gen {G : ℝ → ℝ × ℝ} (hcont : Continuous G) {a b s₀ : ℝ}
    (ha : a < s₀) (hb : s₀ < b) (hinj : Set.InjOn G (Set.Icc a b)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ t ∈ Set.Icc a b, dist (G t) (G s₀) < η → dist t s₀ < δ := by
  have hs₀ : s₀ ∈ Set.Icc a b := ⟨le_of_lt ha, le_of_lt hb⟩
  -- the "bad" set: parameters in `[a,b]` that stay at distance at least `δ` from `s₀`
  set S : Set ℝ := {t : ℝ | δ ≤ dist t s₀} ∩ Set.Icc a b with hS
  have hclosed : IsClosed S := by
    rw [hS]
    exact (isClosed_Ici.preimage (continuous_id.dist continuous_const)).inter isClosed_Icc
  have hcomp : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hclosed (by rw [hS]; exact Set.inter_subset_right)
  -- `G s₀` is not in the image of the bad set, by injectivity
  have hnot : G s₀ ∉ G '' S := by
    rintro ⟨t, ht, hGt⟩
    obtain ⟨h1, h2⟩ := ht
    have hts : t = s₀ := hinj h2 hs₀ hGt
    have h1' : δ ≤ dist t s₀ := h1
    rw [hts, dist_self] at h1'
    linarith
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · -- if the bad set is empty, any positive radius works
    refine ⟨1, one_pos, fun t htK _ => ?_⟩
    by_contra hc
    have htS : t ∈ S := by rw [hS]; exact ⟨not_lt.mp hc, htK⟩
    rw [hSe] at htS
    exact htS
  · -- otherwise the compact image `G '' S` is closed and misses `G s₀`
    refine ⟨Metric.infDist (G s₀) (G '' S), ?_, ?_⟩
    · exact ((hcomp.image hcont).isClosed).notMem_iff_infDist_pos (hSne.image G) |>.mp hnot
    · intro t htK hd
      by_contra hc
      have htS : t ∈ S := by rw [hS]; exact ⟨not_lt.mp hc, htK⟩
      have hmem : G t ∈ G '' S := ⟨t, htS, rfl⟩
      have hle := Metric.infDist_le_dist_of_mem (x := G s₀) hmem
      rw [dist_comm] at hle
      linarith

end Work.RPB.B1p
