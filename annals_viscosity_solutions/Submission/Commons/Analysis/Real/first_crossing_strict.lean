import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.GDelta.MetrizableSpace

namespace Commons.Analysis.Real

open Set

/-- **First crossing point.** If `f` is continuous on `[a, b]`, `f a > c` and `f b < c`, then there
is a *first* point `T ∈ (a, b]` at which `f` reaches the level `c`, i.e. `f T = c` and `f t ≥ c` for
all `t ∈ [a, T]`. -/
theorem first_crossing_strict {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : c < f a) (hb : f b < c) :
    ∃ T : ℝ, a < T ∧ T ≤ b ∧ f T = c ∧ ∀ t ∈ Set.Icc a T, c ≤ f t := by
  -- `S` is the set of points of `[a, b]` where `f` equals `c`.
  set S : Set ℝ := Set.Icc a b ∩ f ⁻¹' {c} with hSdef
  have hS_mem : ∀ x, x ∈ S ↔ a ≤ x ∧ x ≤ b ∧ f x = c := by
    intro x
    rw [hSdef]
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage, Set.mem_singleton_iff]
    tauto
  -- `S` is nonempty by the intermediate value theorem.
  have hS_nonempty : S.Nonempty := by
    obtain ⟨x, hxI, hxf⟩ :=
      (intermediate_value_Icc' hab hf) (show c ∈ Set.Icc (f b) (f a) from ⟨le_of_lt hb, le_of_lt ha⟩)
    exact ⟨x, (hS_mem x).2 ⟨hxI.1, hxI.2, hxf⟩⟩
  -- `S` is closed: intersection of the closed interval `[a, b]` with the preimage of the closed
  -- point `{c}` under a function continuous on `[a, b]`.
  have hS_closed : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  -- `S` is bounded below by `a`.
  have hS_bdd : BddBelow S := ⟨a, fun x hx => ((hS_mem x).1 hx).1⟩
  -- `T := sInf S` is the least crossing point.
  have hT_mem : sInf S ∈ S := hS_closed.csInf_mem hS_nonempty hS_bdd
  have hfT : f (sInf S) = c := ((hS_mem _).1 hT_mem).2.2
  have ha_le_T : a ≤ sInf S := le_csInf hS_nonempty (fun x hx => ((hS_mem x).1 hx).1)
  have hT_le_b : sInf S ≤ b := by
    obtain ⟨x, hx⟩ := hS_nonempty
    exact le_trans (csInf_le hS_bdd hx) ((hS_mem x).1 hx).2.1
  refine ⟨sInf S, ?_, hT_le_b, hfT, ?_⟩
  · -- `a < sInf S` since `sInf S ∈ S` would otherwise force `f a = c`.
    rcases lt_or_eq_of_le ha_le_T with h | h
    · exact h
    · exact absurd (h ▸ hfT) (ne_of_gt ha)
  · -- No point of `[a, sInf S]` can lie strictly below the level `c`.
    intro t ht
    by_contra hcon
    push Not at hcon
    have hat : a ≤ t := ht.1
    have htT : t ≤ sInf S := ht.2
    have htb : t ≤ b := le_trans htT hT_le_b
    have ht_ne : t ≠ sInf S := by
      intro heq
      rw [← heq] at hfT
      exact absurd hfT (ne_of_lt hcon)
    have ht_lt : t < sInf S := lt_of_le_of_ne htT ht_ne
    -- Apply IVT on `[a, t]`: there is `s ∈ [a, t]` with `f s = c`.
    have hcont : ContinuousOn f (Set.Icc a t) := hf.mono (Set.Icc_subset_Icc_right htb)
    obtain ⟨s, hsI, hsf⟩ :=
      (intermediate_value_Icc' hat hcont)
        (show c ∈ Set.Icc (f t) (f a) from ⟨le_of_lt hcon, le_of_lt ha⟩)
    have hsS : s ∈ S := (hS_mem s).2 ⟨hsI.1, le_trans hsI.2 htb, hsf⟩
    -- But then `sInf S ≤ s ≤ t < sInf S`, a contradiction.
    exact absurd (le_trans (csInf_le hS_bdd hsS) hsI.2) (not_le.mpr ht_lt)

end Commons.Analysis.Real