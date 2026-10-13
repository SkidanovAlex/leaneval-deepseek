import Mathlib
import Submission.Work.WilC4.ULPMDefs

namespace Work.WilC4

/-- If `t ⊆ s` is finite with `t.ncard = k`, then there is an injective map `Fin k → α` whose
values all lie in `s`. -/
private lemma exists_injective_of_ncard_eq {α : Type*} {s t : Set α} {k : ℕ}
    (ht : t.Finite) (hst : t ⊆ s) (hcard : t.ncard = k) :
    ∃ f : Fin k → α, Function.Injective f ∧ ∀ i, f i ∈ s := by
  classical
  have hc : ht.toFinset.card = k := by
    rw [← hcard, Set.ncard_eq_toFinset_card t ht]
  let e : ht.toFinset ≃ Fin k := (Finset.equivFin ht.toFinset).trans (finCongr hc)
  refine ⟨fun i => (e.symm i : α), fun i j hij => ?_, fun i => ?_⟩
  · exact e.symm.injective (Subtype.ext hij)
  · exact hst (ht.mem_toFinset.mp (e.symm i).2)

theorem encardLePigeonhole {α : Type*} (s : Set α) (n : ℕ) :
    s.encard ≤ n ↔ ∀ f : Fin (n + 1) → α, (∀ i, f i ∈ s) → ∃ i j : Fin (n + 1), i < j ∧ f i = f j := by
  constructor
  · -- Pigeonhole: `n + 1` elements of a set of size at most `n` cannot be pairwise distinct.
    intro hs f hf
    rw [Set.encard_le_coe_iff_finite_ncard_le] at hs
    obtain ⟨hfin, hncard⟩ := hs
    have hlt : s.ncard < (Set.univ : Set (Fin (n + 1))).ncard := by
      rw [Set.ncard_univ, Nat.card_fin]
      exact Nat.lt_succ_of_le hncard
    obtain ⟨i, -, j, -, hne, heq⟩ :=
      Set.exists_ne_map_eq_of_ncard_lt_of_maps_to hlt (fun a _ => hf a) hfin
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, heq⟩
    · exact ⟨j, i, h, heq.symm⟩
  · -- Conversely, a set admitting `n + 1` distinct elements has cardinality at least `n + 1`.
    intro h
    by_contra hcon
    rw [not_le] at hcon
    have hle : ((n + 1 : ℕ) : ℕ∞) ≤ s.encard := by
      have := ENat.natCast_add_one_le_iff.mpr hcon
      simpa using this
    have key : ∃ f : Fin (n + 1) → α, Function.Injective f ∧ ∀ i, f i ∈ s := by
      rcases s.finite_or_infinite with hfin | hinf
      · have hn : n + 1 ≤ s.ncard := by
          have : ((n + 1 : ℕ) : ℕ∞) ≤ ((s.ncard : ℕ) : ℕ∞) := by
            rw [hfin.cast_ncard_eq]
            exact hle
          exact Nat.cast_le.mp this
        obtain ⟨t, hts, htc⟩ := Set.exists_subset_card_eq hn
        exact exists_injective_of_ncard_eq (hfin.subset hts) hts htc
      · obtain ⟨t, hts, htfin, htc⟩ := hinf.exists_subset_ncard_eq (n + 1)
        exact exists_injective_of_ncard_eq htfin hts htc
    obtain ⟨f, hinj, hf⟩ := key
    obtain ⟨i, j, hij, heq⟩ := h f hf
    exact absurd (hinj heq) (ne_of_lt hij)

end Work.WilC4
