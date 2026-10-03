import Mathlib

namespace Work.Normal

/-- Every open subset of `ℂ` (more generally of a locally compact σ-compact space) admits an
exhaustion by compact subsets: a sequence `K n` of compact sets contained in `U` such that every
compact subset of `U` is contained in some `K n`. -/
lemma exists_compact_exhaustion (U : Set ℂ) (hU : IsOpen U) :
    ∃ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ U) ∧
      (∀ K' : Set ℂ, K' ⊆ U → IsCompact K' → ∃ n, K' ⊆ K n) := by
  classical
  by_cases hne : (Uᶜ : Set ℂ).Nonempty
  · -- Main case: `Uᶜ` is nonempty, so the distance to `Uᶜ` is a useful cut-off.
    -- We intersect a compact exhaustion of `ℂ` with the closed sets `{z | εₙ ≤ dist(z, Uᶜ)}`.
    let K : CompactExhaustion ℂ := CompactExhaustion.choice ℂ
    refine ⟨fun n => K n ∩ {z | ((n : ℝ) + 1)⁻¹ ≤ Metric.infDist z Uᶜ}, ?_, ?_, ?_⟩
    · -- compactness: intersection of a compact set with a closed level set.
      intro n
      exact (K.isCompact n).inter_right
        (isClosed_le continuous_const (Metric.continuous_infDist_pt Uᶜ))
    · -- containment in `U`: points of `Uᶜ` have vanishing distance to `Uᶜ`.
      intro n z hz
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
      obtain ⟨-, hz2⟩ := hz
      by_contra hzU
      have h0 : Metric.infDist z Uᶜ = 0 := Metric.infDist_zero_of_mem (by simpa using hzU)
      have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith
    · -- exhaustion: a compact `K'` stays at positive distance from `Uᶜ` and is bounded.
      intro K' hK'U hK'c
      have hbase : ∃ d : ℝ, 0 < d ∧ ∀ z ∈ K', d ≤ Metric.infDist z Uᶜ := by
        rcases K'.eq_empty_or_nonempty with rfl | hK'ne
        · exact ⟨1, one_pos, by simp⟩
        · obtain ⟨z₀, hz₀, hmin⟩ :=
            hK'c.exists_isMinOn hK'ne (Metric.continuous_infDist_pt Uᶜ).continuousOn
          refine ⟨Metric.infDist z₀ Uᶜ, ?_, fun z hz => hmin hz⟩
          have hz₀U : z₀ ∈ U := hK'U hz₀
          have hz0not : z₀ ∉ Uᶜ := by simpa using hz₀U
          exact (hU.isClosed_compl.notMem_iff_infDist_pos hne).1 hz0not
      obtain ⟨d, hdpos, hd⟩ := hbase
      obtain ⟨N, hN⟩ := K.exists_superset_of_isCompact hK'c
      obtain ⟨n, hn⟩ := exists_nat_ge (max (N : ℝ) d⁻¹)
      refine ⟨n, fun z hz => ⟨?_, ?_⟩⟩
      · exact K.subset (by exact_mod_cast (le_trans (le_max_left _ _) hn)) (hN hz)
      · have h1 : d⁻¹ ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
        have h2 : d⁻¹ ≤ (n : ℝ) + 1 := by linarith
        have h3 : 1 ≤ ((n : ℝ) + 1) * d := (inv_le_iff_one_le_mul₀ hdpos).1 h2
        have h3' : 1 ≤ d * ((n : ℝ) + 1) := by rw [mul_comm]; exact h3
        have hthis : ((n : ℝ) + 1)⁻¹ ≤ d :=
          (inv_le_iff_one_le_mul₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2 h3'
        exact le_trans hthis (hd z hz)
  · -- Degenerate case: `Uᶜ` has no point, so `U = univ` and a compact exhaustion of `ℂ` works.
    have hUuniv : U = Set.univ := by
      have h : Uᶜ = (∅ : Set ℂ) := Set.not_nonempty_iff_eq_empty.mp hne
      rw [← compl_compl U, h, Set.compl_empty]
    let K : CompactExhaustion ℂ := CompactExhaustion.choice ℂ
    refine ⟨fun n => K n, fun n => K.isCompact n, fun n => ?_, ?_⟩
    · rw [hUuniv]; exact Set.subset_univ _
    · intro K' _hK'U hK'c
      exact K.exists_superset_of_isCompact hK'c

end Work.Normal
