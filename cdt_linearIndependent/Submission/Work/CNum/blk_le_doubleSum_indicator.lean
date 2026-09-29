import Mathlib
import Submission.Work.CNum.blkDef

namespace Work.CNum

theorem blk_le_doubleSum_indicator {N : ℕ} (hN : 0 < N) {f : ℝ → ℝ → ℝ} {c : Fin N → Fin N → ℝ}
    (h : ∀ k k' : Fin N, ∀ s ∈ blk N k, ∀ t ∈ blk N k', f s t ≤ c k k') :
    ∀ p ∈ Set.Ioc (0:ℝ) 1 ×ˢ Set.Ioc (0:ℝ) 1,
      f p.1 p.2 ≤ ∑ k : Fin N, ∑ k' : Fin N,
        (blk N k ×ˢ blk N k').indicator (fun _ => c k k') p := by
  intro p hp
  rw [Set.mem_prod] at hp
  obtain ⟨hp1, hp2⟩ := hp
  -- locate the unique blocks containing `p.1` and `p.2`
  obtain ⟨k0, hk0, huniq⟩ := exists_unique_blk hN hp1
  obtain ⟨k0', hk0', huniq'⟩ := exists_unique_blk hN hp2
  have hmem : p ∈ blk N k0 ×ˢ blk N k0' := Set.mem_prod.mpr ⟨hk0, hk0'⟩
  -- the inner sum over `k'` reduces to the single surviving block
  have hres : ∀ k : Fin N, (∑ k' : Fin N,
        (blk N k ×ˢ blk N k').indicator (fun _ => c k k') p)
      = if k = k0 then c k0 k0' else 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk
      rw [if_pos rfl]
      rw [Finset.sum_eq_single k0']
      · exact Set.indicator_of_mem hmem _
      · intro b _ hb
        rw [Set.indicator_of_notMem]
        intro hmem'
        rw [Set.mem_prod] at hmem'
        exact hb (huniq' b hmem'.2)
      · intro hmem'
        exact absurd (Finset.mem_univ k0') hmem'
    · rw [if_neg hk]
      refine Finset.sum_eq_zero (fun k' _ => ?_)
      rw [Set.indicator_of_notMem]
      intro hmem'
      rw [Set.mem_prod] at hmem'
      exact hk (huniq k hmem'.1)
  rw [Finset.sum_congr rfl (fun k _ => hres k)]
  rw [Finset.sum_ite_eq' Finset.univ k0 (fun _ => c k0 k0')]
  simp only [Finset.mem_univ, if_true]
  exact h k0 k0' p.1 hk0 p.2 hk0'

end Work.CNum
