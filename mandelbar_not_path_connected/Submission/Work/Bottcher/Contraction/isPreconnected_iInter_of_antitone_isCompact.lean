import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

open Set

/-- Auxiliary statement in a general Hausdorff space: the intersection of a decreasing
sequence of preconnected compact sets is preconnected.

This is Cantor's intersection theorem for continua: if `K = ⋂ₙ Aₙ` could be written as a
disjoint union of two closed (in `K`) nonempty pieces, those pieces, being disjoint compact
sets, are separated by disjoint open sets `U`, `V`; a finite-intersection argument then
produces `n` with `Aₙ ⊆ U ∪ V`, which contradicts the preconnectedness of `Aₙ`. -/
theorem isPreconnected_iInter_of_antitone_isCompact_general {X : Type*} [TopologicalSpace X]
    [T2Space X] {A : ℕ → Set X} (hcpt : ∀ n, IsCompact (A n))
    (hpre : ∀ n, IsPreconnected (A n)) (hanti : ∀ n, A (n + 1) ⊆ A n) :
    IsPreconnected (⋂ n, A n) := by
  set K : Set X := ⋂ n, A n with hKdef
  intro u v hu hv hKuv huK hvK
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  -- `K ∩ u` and `K ∩ v` are disjoint closed (hence compact) pieces of `K`.
  have hu_eq : K ∩ u = K ∩ vᶜ := by
    ext x
    constructor
    · rintro ⟨hxK, hxu⟩
      refine ⟨hxK, ?_⟩
      intro hxv
      have hx : x ∈ K ∩ (u ∩ v) := ⟨hxK, hxu, hxv⟩
      rw [hcon] at hx
      exact hx
    · rintro ⟨hxK, hxv⟩
      refine ⟨hxK, ?_⟩
      rcases hKuv hxK with h | h
      · exact h
      · exact absurd h hxv
  have hv_eq : K ∩ v = K ∩ uᶜ := by
    ext x
    constructor
    · rintro ⟨hxK, hxv⟩
      refine ⟨hxK, ?_⟩
      intro hxu
      have hx : x ∈ K ∩ (u ∩ v) := ⟨hxK, hxu, hxv⟩
      rw [hcon] at hx
      exact hx
    · rintro ⟨hxK, hxu⟩
      refine ⟨hxK, ?_⟩
      rcases hKuv hxK with h | h
      · exact absurd h hxu
      · exact h
  have hKcompact : IsCompact K := by
    rw [hKdef]
    exact (hcpt 0).of_isClosed_subset (isClosed_iInter fun n => (hcpt n).isClosed)
      (Set.iInter_subset A 0)
  have hKuc : IsCompact (K ∩ u) := by
    rw [hu_eq]
    exact hKcompact.inter_right hv.isClosed_compl
  have hKvc : IsCompact (K ∩ v) := by
    rw [hv_eq]
    exact hKcompact.inter_right hu.isClosed_compl
  have hdisj : Disjoint (K ∩ u) (K ∩ v) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    have h : (K ∩ u) ∩ (K ∩ v) = K ∩ (u ∩ v) := by
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    rw [h, hcon]
  obtain ⟨U, V, hUo, hVo, hKU, hKV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact hKuc hKvc hdisj
  have hK_UV : K ⊆ U ∪ V := by
    intro x hx
    rcases hKuv hx with h | h
    · exact Or.inl (hKU ⟨hx, h⟩)
    · exact Or.inr (hKV ⟨hx, h⟩)
  -- Some `A n` must already be contained in `U ∪ V` (Cantor, finite intersection property).
  have hA_sub : ∃ n, A n ⊆ U ∪ V := by
    by_contra h
    have h' : ∀ i, ¬ (A i ⊆ U ∪ V) := not_exists.mp h
    set B : ℕ → Set X := fun n => A n \ (U ∪ V) with hBdef
    have hBanti : ∀ i, B (i + 1) ⊆ B i := by
      intro i
      rw [hBdef]
      exact Set.sdiff_subset_sdiff_left (hanti i)
    have hBne : ∀ i, (B i).Nonempty := by
      intro i
      rw [hBdef, Set.nonempty_iff_ne_empty]
      intro hzero
      exact h' i (Set.sdiff_eq_empty.mp hzero)
    have hB0cpt : IsCompact (B 0) := by
      have hB0 : B 0 = A 0 ∩ (U ∪ V)ᶜ := by
        ext x
        simp [hBdef]
      rw [hB0]
      exact (hcpt 0).inter_right (hUo.union hVo).isClosed_compl
    have hBclosed : ∀ i, IsClosed (B i) := by
      intro i
      have hBi : B i = A i ∩ (U ∪ V)ᶜ := by
        ext x
        simp [hBdef]
      rw [hBi]
      exact (hcpt i).isClosed.inter (hUo.union hVo).isClosed_compl
    obtain ⟨x, hx⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed B hBanti hBne
        hB0cpt hBclosed
    have hxK : x ∈ K := by
      rw [hKdef]
      exact Set.mem_iInter.mpr fun n => (Set.mem_iInter.mp hx n).1
    have hxUV : x ∉ U ∪ V := (Set.mem_iInter.mp hx 0).2
    exact hxUV (hK_UV hxK)
  obtain ⟨n, hn⟩ := hA_sub
  have hKsub_n : K ⊆ A n := by
    rw [hKdef]
    exact Set.iInter_subset A n
  have hAnU : (A n ∩ U).Nonempty := by
    obtain ⟨x, hxK, hxu⟩ := huK
    exact ⟨x, hKsub_n hxK, hKU ⟨hxK, hxu⟩⟩
  have hAnV : (A n ∩ V).Nonempty := by
    obtain ⟨x, hxK, hxv⟩ := hvK
    exact ⟨x, hKsub_n hxK, hKV ⟨hxK, hxv⟩⟩
  obtain ⟨x, hxAn, hxUV⟩ := hpre n U V hUo hVo hn hAnU hAnV
  exact (Set.disjoint_left.mp hUV) hxUV.1 hxUV.2

theorem isPreconnected_iInter_of_antitone_isCompact {A : ℕ → Set ℂ}
    (hcpt : ∀ n, IsCompact (A n)) (hpre : ∀ n, IsPreconnected (A n))
    (hanti : ∀ n, A (n + 1) ⊆ A n) : IsPreconnected (⋂ n, A n) :=
  isPreconnected_iInter_of_antitone_isCompact_general hcpt hpre hanti

end Work.Bottcher.Contraction
