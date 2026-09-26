import Mathlib

namespace Work.BoxShrink.PinchOff

/-- Auxiliary lemma: if `C` is open and `closure C = C ∪ {a}`, then `C ∪ {a}` is closed and
preconnected (the latter because a clopen non-trivial subset of a preconnected space cannot
exist). -/
lemma isClosed_and_isPreconnected_union_singleton {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {a : X} {C : Set X} (hCop : IsOpen C)
    (hcl : closure C = C ∪ {a}) :
    IsClosed (C ∪ {a}) ∧ IsPreconnected (C ∪ {a}) := by
  have hEc : IsClosed (C ∪ {a}) := hcl ▸ isClosed_closure
  refine ⟨hEc, ?_⟩
  rw [IsPreconnected]
  intro p q hp hq hpq hEp hEq
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have key : ∀ r s : Set X, IsOpen r → IsOpen s → (C ∪ {a}) ⊆ r ∪ s →
      (C ∪ {a}) ∩ (r ∩ s) = ∅ → ((C ∪ {a}) ∩ r).Nonempty → a ∉ r → False := by
    intro r s hr hs hrs hrsd hrne har
    have hEq1 : (C ∪ {a}) ∩ r = C ∩ r := by
      ext x
      constructor
      · rintro ⟨hxE, hxr⟩
        rcases hxE with hxC | hxa
        · exact ⟨hxC, hxr⟩
        · exact absurd (hxa ▸ hxr) har
      · rintro ⟨hxC, hxr⟩
        exact ⟨Or.inl hxC, hxr⟩
    have hEq2 : (C ∪ {a}) ∩ r = (C ∪ {a}) ∩ sᶜ := by
      ext x
      constructor
      · rintro ⟨hxE, hxr⟩
        refine ⟨hxE, ?_⟩
        intro hxs
        have : x ∈ (C ∪ {a}) ∩ (r ∩ s) := ⟨hxE, hxr, hxs⟩
        rw [hrsd] at this
        exact this
      · rintro ⟨hxE, hxs⟩
        refine ⟨hxE, ?_⟩
        rcases hrs hxE with h | h
        · exact h
        · exact absurd h hxs
    have hQopen : IsOpen ((C ∪ {a}) ∩ r) := by rw [hEq1]; exact hCop.inter hr
    have hQclosed : IsClosed ((C ∪ {a}) ∩ r) := by
      rw [hEq2]; exact hEc.inter hs.isClosed_compl
    have hQne : ((C ∪ {a}) ∩ r) ≠ Set.univ := by
      intro h
      have : a ∈ (C ∪ {a}) ∩ r := h ▸ Set.mem_univ a
      rw [hEq1] at this
      exact har this.2
    exact hQne (IsClopen.eq_univ ⟨hQclosed, hQopen⟩ hrne)
  by_cases haq : a ∈ q
  · have hap : a ∉ p := by
      intro hap
      have : a ∈ (C ∪ {a}) ∩ (p ∩ q) := ⟨Or.inr (Set.mem_singleton a), hap, haq⟩
      rw [hcon] at this
      exact this
    exact key p q hp hq hpq hcon hEp hap
  · refine key q p hq hp ?_ ?_ hEq haq
    · rw [Set.union_comm q p]; exact hpq
    · rw [Set.inter_comm p q] at hcon; exact hcon

/-- Auxiliary lemma: in a compact connected (T1) space, a point `a` whose complement is
disconnected cannot be a vertex of a minimal subcontinuum containing two points. -/
lemma aux_preconnected_compl_singleton_of_minimal {X : Type*} [TopologicalSpace X] [T1Space X]
    [CompactSpace X] [PreconnectedSpace X] {a b : X} (hab : a ≠ b)
    (hmin : ∀ E : Set X, IsCompact E → IsPreconnected E → a ∈ E → b ∈ E → E = Set.univ) :
    IsPreconnected ({a}ᶜ : Set X) := by
  by_contra hnot
  rw [isPreconnected_iff_subset_of_disjoint] at hnot
  push_neg at hnot
  obtain ⟨u, v, hu, hv, huv, hdisj, hnu, hnv⟩ := hnot
  set A : Set X := {a}ᶜ ∩ u with hA
  set B : Set X := {a}ᶜ ∩ v with hB
  have hAsub : A ⊆ {a}ᶜ := by rw [hA]; exact Set.inter_subset_left
  have hBsub : B ⊆ {a}ᶜ := by rw [hB]; exact Set.inter_subset_left
  have hAopen : IsOpen A := by rw [hA]; exact isOpen_compl_singleton.inter hu
  have hBopen : IsOpen B := by rw [hB]; exact isOpen_compl_singleton.inter hv
  have hAB : A ∪ B = {a}ᶜ := by
    rw [hA, hB, ← Set.inter_union_distrib_left]
    exact Set.inter_eq_left.mpr huv
  have hAdisjB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    rw [hA] at hxA
    rw [hB] at hxB
    have hx : x ∈ ({a}ᶜ : Set X) ∩ (u ∩ v) := ⟨hxA.1, hxA.2, hxB.2⟩
    rw [hdisj] at hx
    exact hx
  have hBne : B.Nonempty := by
    rw [Set.not_subset] at hnu
    obtain ⟨x, hxS, hxu⟩ := hnu
    refine ⟨x, ?_⟩
    rw [hB]
    refine ⟨hxS, ?_⟩
    rcases huv hxS with h | h
    · exact absurd h hxu
    · exact h
  have hAne : A.Nonempty := by
    rw [Set.not_subset] at hnv
    obtain ⟨x, hxS, hxv⟩ := hnv
    refine ⟨x, ?_⟩
    rw [hA]
    refine ⟨hxS, ?_⟩
    rcases huv hxS with h | h
    · exact h
    · exact absurd h hxv
  have hclA : closure A ∩ {a}ᶜ = A := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxBc : x ∈ Bᶜ :=
        closure_minimal hAdisjB.subset_compl_right hBopen.isClosed_compl hx.1
      have hxAB : x ∈ A ∪ B := by rw [hAB]; exact hx.2
      rcases hxAB with h | h
      · exact h
      · exact absurd h hxBc
    · intro x hx
      exact ⟨subset_closure hx, hAsub hx⟩
  have hclB : closure B ∩ {a}ᶜ = B := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxAc : x ∈ Aᶜ :=
        closure_minimal hAdisjB.symm.subset_compl_right hAopen.isClosed_compl hx.1
      have hxAB : x ∈ A ∪ B := by rw [hAB]; exact hx.2
      rcases hxAB with h | h
      · exact absurd h hxAc
      · exact h
    · intro x hx
      exact ⟨subset_closure hx, hBsub hx⟩
  have haA : a ∈ closure A := by
    by_contra hacl
    have hclosedA : IsClosed A := by
      rw [← closure_subset_iff_isClosed]
      intro x hx
      by_cases hxa : x = a
      · exact absurd (hxa ▸ hx) hacl
      · have : x ∈ closure A ∩ ({a}ᶜ : Set X) :=
          ⟨hx, by rw [Set.mem_compl_singleton_iff]; exact hxa⟩
        rwa [hclA] at this
    have huniv : A = Set.univ := IsClopen.eq_univ ⟨hclosedA, hAopen⟩ hAne
    have : a ∈ A := huniv ▸ Set.mem_univ a
    exact (hAsub this) rfl
  have haB : a ∈ closure B := by
    by_contra hacl
    have hclosedB : IsClosed B := by
      rw [← closure_subset_iff_isClosed]
      intro x hx
      by_cases hxa : x = a
      · exact absurd (hxa ▸ hx) hacl
      · have : x ∈ closure B ∩ ({a}ᶜ : Set X) :=
          ⟨hx, by rw [Set.mem_compl_singleton_iff]; exact hxa⟩
        rwa [hclB] at this
    have huniv : B = Set.univ := IsClopen.eq_univ ⟨hclosedB, hBopen⟩ hBne
    have : a ∈ B := huniv ▸ Set.mem_univ a
    exact (hBsub this) rfl
  have hclAeq : closure A = A ∪ {a} := by
    apply Set.Subset.antisymm
    · intro x hx
      by_cases hxa : x = a
      · exact Or.inr (by rw [Set.mem_singleton_iff]; exact hxa)
      · left
        have : x ∈ closure A ∩ ({a}ᶜ : Set X) :=
          ⟨hx, by rw [Set.mem_compl_singleton_iff]; exact hxa⟩
        rwa [hclA] at this
    · rintro x (hx | hx)
      · exact subset_closure hx
      · rw [Set.mem_singleton_iff] at hx
        exact hx ▸ haA
  have hclBeq : closure B = B ∪ {a} := by
    apply Set.Subset.antisymm
    · intro x hx
      by_cases hxa : x = a
      · exact Or.inr (by rw [Set.mem_singleton_iff]; exact hxa)
      · left
        have : x ∈ closure B ∩ ({a}ᶜ : Set X) :=
          ⟨hx, by rw [Set.mem_compl_singleton_iff]; exact hxa⟩
        rwa [hclB] at this
    · rintro x (hx | hx)
      · exact subset_closure hx
      · rw [Set.mem_singleton_iff] at hx
        exact hx ▸ haB
  have hbS : b ∈ ({a}ᶜ : Set X) := by
    rw [Set.mem_compl_singleton_iff]; exact fun h => hab h.symm
  have hbAB : b ∈ A ∪ B := by rw [hAB]; exact hbS
  rcases hbAB with hbA | hbB
  · obtain ⟨hEc, hEpc⟩ := isClosed_and_isPreconnected_union_singleton hAopen hclAeq
    have hEcompact : IsCompact (A ∪ {a}) :=
      IsCompact.of_isClosed_subset isCompact_univ hEc (Set.subset_univ _)
    have hEeq : A ∪ {a} = Set.univ :=
      hmin (A ∪ {a}) hEcompact hEpc (Or.inr (Set.mem_singleton a))
        (Or.inl hbA)
    obtain ⟨x, hxB⟩ := hBne
    have hxE : x ∈ A ∪ {a} := hEeq ▸ Set.mem_univ x
    rcases hxE with h | h
    · exact (Set.disjoint_left.mp hAdisjB h) hxB
    · exact (hBsub hxB) h
  · obtain ⟨hEc, hEpc⟩ := isClosed_and_isPreconnected_union_singleton hBopen hclBeq
    have hEcompact : IsCompact (B ∪ {a}) :=
      IsCompact.of_isClosed_subset isCompact_univ hEc (Set.subset_univ _)
    have hEeq : B ∪ {a} = Set.univ :=
      hmin (B ∪ {a}) hEcompact hEpc (Or.inr (Set.mem_singleton a))
        (Or.inl hbB)
    obtain ⟨x, hxA⟩ := hAne
    have hxE : x ∈ B ∪ {a} := hEeq ▸ Set.mem_univ x
    rcases hxE with h | h
    · exact (Set.disjoint_left.mp hAdisjB hxA) h
    · exact (hAsub hxA) h

theorem isPreconnected_diff_singleton_of_minimal {M : Set ℂ} {a b : ℂ}
    (hMk : IsCompact M) (hMp : IsPreconnected M) (ha : a ∈ M) (hb : b ∈ M) (hab : a ≠ b)
    (hmin : ∀ E : Set ℂ, E ⊆ M → IsCompact E → IsPreconnected E → a ∈ E → b ∈ E → E = M) :
    IsPreconnected (M \ {a}) := by
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hMk
  haveI : PreconnectedSpace M := isPreconnected_iff_preconnectedSpace.mp hMp
  have hab' : (⟨a, ha⟩ : M) ≠ ⟨b, hb⟩ := by
    intro h
    exact hab (Subtype.ext_iff.mp h)
  have hmin' : ∀ E : Set M, IsCompact E → IsPreconnected E →
      (⟨a, ha⟩ : M) ∈ E → (⟨b, hb⟩ : M) ∈ E → E = Set.univ := by
    intro E hEk hEp haE hbE
    have hsub : ((↑) : M → ℂ) '' E ⊆ M := by
      rintro x ⟨y, -, rfl⟩
      exact y.2
    have hk : IsCompact (((↑) : M → ℂ) '' E) :=
      (Topology.IsEmbedding.subtypeVal.isCompact_iff).mp hEk
    have hp : IsPreconnected (((↑) : M → ℂ) '' E) :=
      (Topology.IsInducing.subtypeVal.isPreconnected_image).mpr hEp
    have hres : ((↑) : M → ℂ) '' E = M :=
      hmin _ hsub hk hp ⟨⟨a, ha⟩, haE, rfl⟩ ⟨⟨b, hb⟩, hbE, rfl⟩
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have hxM : (x : ℂ) ∈ ((↑) : M → ℂ) '' E := by rw [hres]; exact x.2
      rcases hxM with ⟨y, hy, hyx⟩
      exact (Subtype.val_injective hyx) ▸ hy
  have hgoal : IsPreconnected ({⟨a, ha⟩}ᶜ : Set M) :=
    aux_preconnected_compl_singleton_of_minimal hab' hmin'
  have himg : ((↑) : M → ℂ) '' ({⟨a, ha⟩}ᶜ : Set M) = M \ {a} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [Set.mem_compl_iff] at hy
      intro hya
      exact hy (Subtype.ext hya)
    · rintro ⟨hxM, hxa⟩
      refine ⟨⟨x, hxM⟩, ?_, rfl⟩
      rw [Set.mem_compl_iff]
      intro h
      exact hxa (Subtype.ext_iff.mp h)
  rw [← himg]
  exact (Topology.IsInducing.subtypeVal.isPreconnected_image).mpr hgoal

end Work.BoxShrink.PinchOff
