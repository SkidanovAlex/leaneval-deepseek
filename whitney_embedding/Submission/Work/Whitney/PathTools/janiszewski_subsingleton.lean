import Mathlib
import Submission.Work.Whitney.PathTools.JaniszewskiTwo
import Submission.Work.Whitney.PathTools.TotallyDisconnectedPlane
import Submission.Work.Whitney.PathTools.minimal_separator_preconnected
import Submission.Work.Whitney.PathTools.minimal_separator_no_cut_point

namespace Work.Whitney.PathTools

open Set

/-- **Zorn step.**  If `K` is a compact set separating `X` from `Y`, then there is a compact subset
`L ⊆ K` which is *minimal* with this property: every compact `M ⊆ L` still separating `X` from `Y`
equals `L`.

(The chain condition: a chain of separators has as a lower bound its intersection; a path avoiding
the intersection avoids finitely many members of the chain, and a finite subfamily of a chain has a
least member.) -/
lemma exists_minimal_compact_separator {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    {x y : EuclideanSpace ℝ (Fin 2)} (hsep : ¬ JoinedIn (Kᶜ) x y) :
    ∃ L : Set (EuclideanSpace ℝ (Fin 2)), L ⊆ K ∧ IsCompact L ∧ ¬ JoinedIn (Lᶜ) x y ∧
      ∀ M : Set (EuclideanSpace ℝ (Fin 2)), M ⊆ L → IsCompact M → ¬ JoinedIn (Mᶜ) x y → L ⊆ M := by
  classical
  set S : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
    {L | L ⊆ K ∧ IsCompact L ∧ ¬ JoinedIn (Lᶜ) x y} with hSdef
  have hKmem : K ∈ S := ⟨subset_rfl, hK, hsep⟩
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hcchain
    rcases c.eq_empty_or_nonempty with rfl | hcne
    · exact ⟨K, hKmem, fun s hs => absurd hs (by simp)⟩
    · refine ⟨⋂₀ c, ⟨?_, ?_, ?_⟩, fun s hs => sInter_subset_of_mem hs⟩
      · obtain ⟨L₀, hL₀⟩ := hcne
        exact (sInter_subset_of_mem hL₀).trans (hcS hL₀).1
      · refine hK.of_isClosed_subset ?_ ?_
        · exact isClosed_sInter fun s hs => ((hcS hs).2.1).isClosed
        · obtain ⟨L₀, hL₀⟩ := hcne
          exact (sInter_subset_of_mem hL₀).trans (hcS hL₀).1
      · rintro ⟨γ, hγ⟩
        have hcover : range γ ⊆ ⋃ i : {L // L ∈ c}, ((i : Set _))ᶜ := by
          intro z hz
          obtain ⟨t, rfl⟩ := hz
          have h1 : γ t ∉ ⋂₀ c := hγ t
          rw [Set.mem_sInter] at h1
          push_neg at h1
          obtain ⟨L, hLc, hLt⟩ := h1
          exact Set.mem_iUnion.mpr ⟨⟨L, hLc⟩, hLt⟩
        obtain ⟨u, hu⟩ := (isCompact_range γ.continuous).elim_finite_subcover
          (fun i : {L // L ∈ c} => ((i : Set _))ᶜ)
          (fun i => ((hcS i.2).2.1).isClosed.isOpen_compl) hcover
        have hufin : ∀ L' ∈ u.image Subtype.val, L' ∈ c := by
          intro L' hL'
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hL'
          exact i.2
        rcases u.eq_empty_or_nonempty with rfl | uone
        · exfalso
          have h0 := hu ⟨(0 : unitInterval), rfl⟩
          simp at h0
        obtain ⟨L', hL'u, hL'min⟩ :=
          Grid.Finset.exists_subset_of_isChain hcchain hufin (uone.image Subtype.val)
        have hsub : range γ ⊆ ((L' : Set _))ᶜ := by
          intro z hz
          have h1 := hu hz
          rw [Set.mem_iUnion] at h1
          obtain ⟨i, h1⟩ := h1
          rw [Set.mem_iUnion] at h1
          obtain ⟨hiu, hzi⟩ := h1
          have h2 : (i : Set _) ∈ u.image Subtype.val := Finset.mem_image.mpr ⟨i, hiu, rfl⟩
          exact fun hzL => hzi ((hL'min (i : Set _) h2) hzL)
        exact (hcS (hufin L' hL'u)).2.2 ⟨γ, fun t => hsub ⟨t, rfl⟩⟩
  obtain ⟨L, hLmin⟩ := zorn_superset S hchain
  exact ⟨L, hLmin.1.1, hLmin.1.2.1, hLmin.1.2.2,
    fun M hML hMc hMs => hLmin.2 ⟨hML.trans hLmin.1.1, hMc, hMs⟩ hML⟩

/-- **Janiszewski's theorem for a subsingleton intersection.**  If `A` and `B` are compact
subsets of the plane whose intersection has at most one point, and two points `X, Y` outside
`A ∪ B` can be joined both by a path avoiding `A` and by a path avoiding `B`, then they can be
joined by a path avoiding `A ∪ B`.

The disjoint case `A ∩ B = ∅` is the two-piece lemma `Grid.joinedIn_compl_union` for separated
compacta.  In the singleton case `A ∩ B = {p}` we take a compact separator `L ⊆ A ∪ B` minimal
under inclusion (`exists_minimal_compact_separator`), which is connected
(`minimal_separator_preconnected`) and, by `minimal_separator_no_cut_point`, has no cut point; but
`L = (L ∩ A) ∪ (L ∩ B)` with `L ∩ A ∩ L ∩ B = {p}` exhibits `p` as a cut point of `L`. -/
theorem janiszewski_subsingleton {A B : Set (EuclideanSpace ℝ (Fin 2))} (hA : IsCompact A)
    (hB : IsCompact B) (hsub : (A ∩ B).Subsingleton) {X Y : EuclideanSpace ℝ (Fin 2)}
    (hX : X ∉ A ∪ B) (hY : Y ∉ A ∪ B) (h₁ : JoinedIn (Aᶜ) X Y) (h₂ : JoinedIn (Bᶜ) X Y) :
    JoinedIn ((A ∪ B)ᶜ) X Y := by
  classical
  rcases (A ∩ B).eq_empty_or_nonempty with hemp | hne
  · -- Disjoint case: the two-piece lemma for separated compacta.
    have hdisj : Disjoint A B := Set.disjoint_iff_inter_eq_empty.mpr hemp
    have hsep : ∀ x ∈ A, ∀ y ∈ B, 0 < dist x y := by
      intro x hx y hy
      exact dist_pos.mpr fun h => hdisj.le_bot ⟨hx, h ▸ hy⟩
    exact Grid.joinedIn_compl_union hA hB hsep hX hY h₁ h₂
  · -- Singleton case `A ∩ B = {p}` (Janiszewski's theorem).
    obtain ⟨p, hp⟩ := hne
    have hAB : A ∩ B = {p} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun q hq => ?_⟩
      exact hsub hq hp
    by_contra hnot
    -- a minimal compact separator inside `A ∪ B`
    obtain ⟨L, hLK, hLcpt, hLsep, hLmin⟩ :=
      exists_minimal_compact_separator (hA.union hB) hnot
    have hxL : X ∉ L := fun h => hX (hLK h)
    have hyL : Y ∉ L := fun h => hY (hLK h)
    have hLpre : IsPreconnected L :=
      minimal_separator_preconnected hLcpt hxL hyL hLsep hLmin
    have hLAB : (L ∩ A) ∪ (L ∩ B) = L := by
      refine Set.Subset.antisymm (union_subset inter_subset_left inter_subset_left) ?_
      intro z hz
      rcases hLK hz with hzA | hzB
      · exact Or.inl ⟨hz, hzA⟩
      · exact Or.inr ⟨hz, hzB⟩
    by_cases hpL : p ∈ L
    · -- `p ∈ L`: then `p` is a cut point of `L`
      have hnotpre : ¬ IsPreconnected (L \ {p}) := by
        intro hpre
        rw [isPreconnected_iff_subset_of_disjoint_closed] at hpre
        have hcov : (L \ {p}) ⊆ (L ∩ A) ∪ (L ∩ B) := by
          intro z hz
          rcases hLK hz.1 with hzA | hzB
          · exact Or.inl ⟨hz.1, hzA⟩
          · exact Or.inr ⟨hz.1, hzB⟩
        have hdisj'' : (L \ {p}) ∩ ((L ∩ A) ∩ (L ∩ B)) = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.mpr ?_
          rintro z ⟨⟨hzL, hzp⟩, ⟨⟨-, hzA⟩, ⟨-, hzB⟩⟩⟩
          have hzAB : z ∈ A ∩ B := ⟨hzA, hzB⟩
          rw [hAB, Set.mem_singleton_iff] at hzAB
          exact hzp hzAB
        have hcase := hpre (L ∩ A) (L ∩ B) (hLcpt.isClosed.inter hA.isClosed)
          (hLcpt.isClosed.inter hB.isClosed) hcov hdisj''
        have hLA' : ¬ (L \ {p}) ⊆ L ∩ A := by
          intro hsub'
          have hLA : L ⊆ A := by
            intro z hz
            by_cases hzp : z = p
            · rw [hzp]; exact hp.1
            · exact (hsub' ⟨hz, hzp⟩).2
          exact hLsep (h₁.mono fun z hz hzL => hz (hLA hzL))
        have hLB' : ¬ (L \ {p}) ⊆ L ∩ B := by
          intro hsub'
          have hLB : L ⊆ B := by
            intro z hz
            by_cases hzp : z = p
            · rw [hzp]; exact hp.2
            · exact (hsub' ⟨hz, hzp⟩).2
          exact hLsep (h₂.mono fun z hz hzL => hz (hLB hzL))
        exact hcase.elim hLA' hLB'
      exact hnotpre (minimal_separator_no_cut_point hLcpt hLpre hxL hyL hLsep hLmin hpL)
    · -- `p ∉ L`: the two pieces of `L` are disjoint compacta
      have hdisj : Disjoint (L ∩ A) (L ∩ B) := by
        rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
        rintro z ⟨⟨hzL, hzA⟩, hzB⟩
        have : z ∈ A ∩ B := ⟨hzA, hzB.2⟩
        rw [hAB] at this
        exact hpL (this ▸ hzL)
      have hjoinA : JoinedIn ((L ∩ A)ᶜ) X Y := h₁.mono fun z hz hzLA => hz hzLA.2
      have hjoinB : JoinedIn ((L ∩ B)ᶜ) X Y := h₂.mono fun z hz hzLB => hz hzLB.2
      have hX' : X ∉ (L ∩ A) ∪ (L ∩ B) := by rw [hLAB]; exact hxL
      have hY' : Y ∉ (L ∩ A) ∪ (L ∩ B) := by rw [hLAB]; exact hyL
      have hsep' : ∀ x ∈ L ∩ A, ∀ y ∈ L ∩ B, 0 < dist x y := by
        intro x hx y hy
        exact dist_pos.mpr fun h => Set.disjoint_left.mp hdisj hx (h ▸ hy)
      have hmain := Grid.joinedIn_compl_union (hLcpt.inter hA) (hLcpt.inter hB) hsep' hX' hY' hjoinA hjoinB
      exact hLsep (by rw [← hLAB]; exact hmain)

end Work.Whitney.PathTools
