import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.ContractionAux

open Set

/-- A decreasing sequence of compact preconnected subsets of `ℂ` has preconnected intersection. -/
theorem isPreconnected_iInter_of_antitone_isCompact {A : ℕ → Set ℂ}
    (hcpt : ∀ n, IsCompact (A n)) (hpre : ∀ n, IsPreconnected (A n))
    (hanti : ∀ n, A (n + 1) ⊆ A n) : IsPreconnected (⋂ n, A n) := by
  have hmono : Antitone A := antitone_nat_of_succ_le hanti
  have hKclosed : IsClosed (⋂ n, A n) := isClosed_iInter fun n => (hcpt n).isClosed
  have hKcpt : IsCompact (⋂ n, A n) :=
    (hcpt 0).of_isClosed_subset hKclosed (iInter_subset _ 0)
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hKsub hKt hKt'
  by_contra hcontra
  rw [not_nonempty_iff_eq_empty] at hcontra
  -- `K ∩ t` and `K ∩ t'` are two disjoint compact sets; separate them by disjoint open sets.
  have hPQ : Disjoint ((⋂ n, A n) ∩ t) ((⋂ n, A n) ∩ t') := by
    rw [disjoint_iff_inter_eq_empty]
    rw [show ((⋂ n, A n) ∩ t) ∩ ((⋂ n, A n) ∩ t') = (⋂ n, A n) ∩ (t ∩ t') from by
      ext x; constructor
      · intro hx; exact ⟨hx.1.1, hx.1.2, hx.2.2⟩
      · intro hx; exact ⟨⟨hx.1, hx.2.1⟩, hx.1, hx.2.2⟩]
    exact hcontra
  obtain ⟨U, V, hUo, hVo, hPU, hQV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact_isClosed
      (hKcpt.inter_right ht) (hKcpt.inter_right ht') (hKclosed.inter ht') hPQ
  -- The intersection is covered by `U ∪ V`.
  have hKUV : (⋂ n, A n) ⊆ U ∪ V := by
    intro x hx
    rcases hKsub hx with hxt | hxt
    · exact Or.inl (hPU ⟨hx, hxt⟩)
    · exact Or.inr (hQV ⟨hx, hxt⟩)
  -- Compactness forces some `A N` to be covered by `U ∪ V` as well.
  have hN : ∃ N, A N ⊆ U ∪ V := by
    have hdisj : Disjoint (A 0) (⋂ n, (A n ∩ (U ∪ V)ᶜ)) := by
      rw [disjoint_iff_inter_eq_empty]
      apply Subset.antisymm
      · intro x hx
        have key := Set.mem_iInter.mp hx.2
        exact (key 0).2 (hKUV (Set.mem_iInter.mpr fun n => (key n).1))
      · exact empty_subset _
    have hdir : Directed (· ⊇ ·) (fun n => A n ∩ (U ∪ V)ᶜ) := by
      intro i j
      exact ⟨max i j, inter_subset_inter (hmono (Nat.le_max_left i j)) subset_rfl,
        inter_subset_inter (hmono (Nat.le_max_right i j)) subset_rfl⟩
    obtain ⟨N, hNdisj⟩ :=
      (hcpt 0).elim_directed_family_closed (fun n => A n ∩ (U ∪ V)ᶜ)
        (fun n => (hcpt n).isClosed.inter (hUo.union hVo).isClosed_compl) hdisj hdir
    refine ⟨N, fun x hx => by
      by_contra hxc
      have hmem : x ∈ A 0 ∩ (A N ∩ (U ∪ V)ᶜ) := ⟨hmono (Nat.zero_le N) hx, hx, hxc⟩
      exact hNdisj.le_bot hmem⟩
  obtain ⟨N, hN⟩ := hN
  obtain ⟨a, haK, hat⟩ := hKt
  obtain ⟨b, hbK, hbt'⟩ := hKt'
  -- `A N` is preconnected and contained in the disjoint open sets `U` and `V`.
  rcases (hpre N).subset_or_subset hUo hVo hUV hN with hNU | hNV
  · obtain ⟨y, hyN, hyV⟩ :=
      (show (A N ∩ V).Nonempty from ⟨b, (Set.mem_iInter.mp hbK) N, hQV ⟨hbK, hbt'⟩⟩)
    have hy : y ∈ U ∩ V := ⟨hNU hyN, hyV⟩
    rw [hUV.inter_eq] at hy
    exact hy
  · obtain ⟨y, hyN, hyU⟩ :=
      (show (A N ∩ U).Nonempty from ⟨a, (Set.mem_iInter.mp haK) N, hPU ⟨haK, hat⟩⟩)
    have hy : y ∈ U ∩ V := ⟨hyU, hNV hyN⟩
    rw [hUV.inter_eq] at hy
    exact hy

end Work.Bottcher.ContractionAux
