import Mathlib
import Submission.Work.Whitney.PathTools.JaniszewskiTwo

namespace Work.Whitney.PathTools

open Set

/-- **A minimal compact separator is connected.**  If `L` is a compact set separating `X` from `Y`
(the two terms are not joined in `Lᶜ`) and `L` is minimal among such compact sets, then `L` is
preconnected.

Proof: a disconnection `L = A ⊔ B` into two nonempty closed (hence compact) pieces would force, by
minimality, that `X` and `Y` are joined in both `Aᶜ` and `Bᶜ`; the two pieces are disjoint compacta,
so the two-piece lemma (`Grid.joinedIn_compl_union`) joins `X` and `Y` in `(A ∪ B)ᶜ = Lᶜ`,
contradiction. -/
theorem minimal_separator_preconnected {L : Set (EuclideanSpace ℝ (Fin 2))} (hLc : IsCompact L)
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∉ L) (hy : y ∉ L) (hsep : ¬ JoinedIn (Lᶜ) x y)
    (hmin : ∀ M : Set (EuclideanSpace ℝ (Fin 2)), M ⊆ L → IsCompact M → ¬ JoinedIn (Mᶜ) x y → L ⊆ M) :
    IsPreconnected L := by
  by_contra hcon
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hcon
  push_neg at hcon
  obtain ⟨u, v, hu, hv, huv, hdisj, hnu, hnv⟩ := hcon
  -- the two pieces
  have hsub₁ : L ∩ u ⊆ L := inter_subset_left
  have hsub₂ : L ∩ v ⊆ L := inter_subset_left
  have hcpt₁ : IsCompact (L ∩ u) := hLc.of_isClosed_subset (hLc.isClosed.inter hu) hsub₁
  have hcpt₂ : IsCompact (L ∩ v) := hLc.of_isClosed_subset (hLc.isClosed.inter hv) hsub₂
  have hcover : L = (L ∩ u) ∪ (L ∩ v) := by
    refine Set.Subset.antisymm ?_ (union_subset hsub₁ hsub₂)
    intro z hz
    rcases huv hz with hzu | hzv
    · exact Or.inl ⟨hz, hzu⟩
    · exact Or.inr ⟨hz, hzv⟩
  have hdisj' : (L ∩ u) ∩ (L ∩ v) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro z ⟨⟨hzL, hzu⟩, -, hzv⟩
    have : z ∈ L ∩ (u ∩ v) := ⟨hzL, hzu, hzv⟩
    rw [hdisj] at this
    exact this
  have hne₁ : (L ∩ u).Nonempty := by
    obtain ⟨z, hzL, hzv⟩ : ∃ z, z ∈ L ∧ z ∉ v := by
      by_contra h
      exact hnv (fun z hz => by by_contra hzv; exact h ⟨z, hz, hzv⟩)
    exact ⟨z, hzL, (huv hzL).resolve_right hzv⟩
  have hne₂ : (L ∩ v).Nonempty := by
    obtain ⟨z, hzL, hzu⟩ : ∃ z, z ∈ L ∧ z ∉ u := by
      by_contra h
      exact hnu (fun z hz => by by_contra hzu; exact h ⟨z, hz, hzu⟩)
    exact ⟨z, hzL, (huv hzL).resolve_left hzu⟩
  have hsep' : ∀ a ∈ L ∩ u, ∀ b ∈ L ∩ v, 0 < dist a b := by
    intro a ha b hb
    refine dist_pos.mpr fun hab => ?_
    have : a ∈ (L ∩ u) ∩ (L ∩ v) := ⟨ha, hab ▸ hb⟩
    rw [hdisj'] at this
    exact notMem_empty a this
  have hjoin₁ : JoinedIn ((L ∩ u)ᶜ) x y := by
    by_contra hcon₁
    obtain ⟨z, hz⟩ := hne₂
    have hsub : L ⊆ L ∩ u := hmin (L ∩ u) hsub₁ hcpt₁ hcon₁
    have hzA : z ∈ L ∩ u := hsub hz.1
    have : z ∈ (L ∩ u) ∩ (L ∩ v) := ⟨hzA, hz⟩
    rw [hdisj'] at this
    exact notMem_empty z this
  have hjoin₂ : JoinedIn ((L ∩ v)ᶜ) x y := by
    by_contra hcon₂
    obtain ⟨z, hz⟩ := hne₁
    have hsub : L ⊆ L ∩ v := hmin (L ∩ v) hsub₂ hcpt₂ hcon₂
    have hzB : z ∈ L ∩ v := hsub hz.1
    have : z ∈ (L ∩ u) ∩ (L ∩ v) := ⟨hz, hzB⟩
    rw [hdisj'] at this
    exact notMem_empty z this
  have hx' : x ∉ (L ∩ u) ∪ (L ∩ v) := by rw [← hcover]; exact hx
  have hy' : y ∉ (L ∩ u) ∪ (L ∩ v) := by rw [← hcover]; exact hy
  have hmain := Grid.joinedIn_compl_union hcpt₁ hcpt₂ hsep' hx' hy' hjoin₁ hjoin₂
  exact hsep (by rw [hcover]; exact hmain)

end Work.Whitney.PathTools
