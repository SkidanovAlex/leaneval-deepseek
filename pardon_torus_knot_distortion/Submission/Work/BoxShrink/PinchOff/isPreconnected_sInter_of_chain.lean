import Mathlib

/-!
# Intersections of chains of compact preconnected subsets of `ℂ`

A chain (under `⊆`) of nonempty compact preconnected subsets of `ℂ` has preconnected
intersection.  The proof is the classical one: given an open cover `u ∪ v` of the
intersection `K = ⋂₀ c` with `K` avoiding `u ∩ v`, the two pieces `K ∩ u` and `K ∩ v`
are disjoint compact (hence closed) sets, which by normality of `ℂ` admit disjoint open
neighbourhoods `U ⊇ K ∩ u`, `V ⊇ K ∩ v`.  Since `U ∪ V` is an open cover of `K`, the
chain of compact sets `{s ∩ (U ∪ V)ᶜ}` has empty intersection, so (Cantor / finite
intersection property for chains) some member `s₀ ∈ c` already lies in `U ∪ V`; as `s₀`
is preconnected and `U`, `V` are disjoint it lies in `U` or in `V`, and then so does
`K = ⋂₀ c`.
-/

namespace Work.BoxShrink.PinchOff

open Set

/-- **Chain Cantor lemma.**  If `c` is a chain of compact subsets of `ℂ` and `W` is
closed with `(⋂₀ c) ∩ W = ∅`, then already some member of `c` misses `W`. -/
theorem exists_mem_inter_eq_empty_of_chain {c : Set (Set ℂ)} (hchain : IsChain (· ⊆ ·) c)
    (hne : c.Nonempty) (hcpt : ∀ s ∈ c, IsCompact s) {W : Set ℂ} (hW : IsClosed W)
    (hdisj : ⋂₀ c ∩ W = ∅) : ∃ s ∈ c, s ∩ W = ∅ := by
  by_contra h
  push Not at h
  have hmem : ∀ U ∈ (fun s : Set ℂ => s ∩ W) '' c, U.Nonempty := by
    rintro U ⟨s, hs, rfl⟩
    exact h s hs
  have hcpt' : ∀ U ∈ (fun s : Set ℂ => s ∩ W) '' c, IsCompact U := by
    rintro U ⟨s, hs, rfl⟩
    exact (hcpt s hs).inter_right hW
  have hcl' : ∀ U ∈ (fun s : Set ℂ => s ∩ W) '' c, IsClosed U := by
    rintro U ⟨s, hs, rfl⟩
    exact (hcpt s hs).isClosed.inter hW
  have hdir : DirectedOn (· ⊇ ·) ((fun s : Set ℂ => s ∩ W) '' c) := by
    rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩
    rcases eq_or_ne s t with rfl | hst
    · exact ⟨s ∩ W, ⟨s, hs, rfl⟩, subset_rfl, subset_rfl⟩
    · rcases hchain hs ht hst with hst' | hts'
      · exact ⟨s ∩ W, ⟨s, hs, rfl⟩, subset_rfl, fun x hx => ⟨hst' hx.1, hx.2⟩⟩
      · exact ⟨t ∩ W, ⟨t, ht, rfl⟩, fun x hx => ⟨hts' hx.1, hx.2⟩, subset_rfl⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    (S := (fun s : Set ℂ => s ∩ W) '' c)
    (hS := Set.Nonempty.to_subtype (hne.image _)) hdir hmem hcpt' hcl'
  have hsInter : ⋂₀ ((fun s : Set ℂ => s ∩ W) '' c) = ⋂₀ c ∩ W := by
    ext x
    simp only [Set.mem_sInter, Set.mem_inter_iff, Set.mem_image]
    constructor
    · intro hx
      exact ⟨fun s hs => (hx (s ∩ W) ⟨s, hs, rfl⟩).1, (hx _ ⟨hne.some, hne.some_mem, rfl⟩).2⟩
    · rintro ⟨h1, h2⟩ U ⟨s, hs, rfl⟩
      exact ⟨h1 s hs, h2⟩
  rw [hsInter, hdisj] at hx
  exact hx

/-- **An intersection of a chain of compact preconnected subsets of `ℂ` is
preconnected.** -/
theorem isPreconnected_sInter_of_chain {c : Set (Set ℂ)} (hchain : IsChain (· ⊆ ·) c)
    (hne : c.Nonempty) (hcpt : ∀ s ∈ c, IsCompact s) (hpre : ∀ s ∈ c, IsPreconnected s) :
    IsPreconnected (⋂₀ c) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hKuv huv
  have hKcl : IsClosed (⋂₀ c) := isClosed_sInter (fun s hs => (hcpt s hs).isClosed)
  have hAcl : IsClosed (⋂₀ c ∩ vᶜ) := hKcl.inter hv.isClosed_compl
  have hBcl : IsClosed (⋂₀ c ∩ uᶜ) := hKcl.inter hu.isClosed_compl
  have hABdisj : Disjoint (⋂₀ c ∩ vᶜ) (⋂₀ c ∩ uᶜ) := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    rw [Set.mem_inter_iff] at hxA hxB
    rcases hKuv hxA.1 with hxu | hxv
    · exact hxB.2 hxu
    · exact hxA.2 hxv
  obtain ⟨U, V, hUo, hVo, hAU, hBV, hUVdisj⟩ := normal_separation hAcl hBcl hABdisj
  have huv' : ∀ x, x ∉ ⋂₀ c ∩ (u ∩ v) := by intro x hx; rw [huv] at hx; exact hx
  have hKUV : ⋂₀ c ⊆ U ∪ V := by
    intro x hx
    rcases hKuv hx with hxu | hxv
    · left
      exact hAU ⟨hx, fun hxv' => huv' x ⟨hx, hxu, hxv'⟩⟩
    · right
      exact hBV ⟨hx, fun hxu' => huv' x ⟨hx, hxu', hxv⟩⟩
  have hW : IsClosed (U ∪ V)ᶜ := (hUo.union hVo).isClosed_compl
  have hdisjW : ⋂₀ c ∩ (U ∪ V)ᶜ = ∅ :=
    (Set.disjoint_compl_right_iff_subset.mpr hKUV).inter_eq
  obtain ⟨s₁, hs₁c, hs₁⟩ := exists_mem_inter_eq_empty_of_chain hchain hne hcpt hW hdisjW
  have hs₁U : s₁ ⊆ U ∪ V := by
    intro x hx
    by_contra hx'
    exact (Set.not_nonempty_iff_eq_empty.mpr hs₁) ⟨x, hx, hx'⟩
  have hsub : s₁ ⊆ U ∨ s₁ ⊆ V :=
    (isPreconnected_iff_subset_of_disjoint.mp (hpre s₁ hs₁c)) U V hUo hVo hs₁U
      (by rw [hUVdisj.inter_eq, Set.inter_empty])
  rcases hsub with hsub | hsub
  · left
    have hKU : ⋂₀ c ⊆ U := fun x hx => hsub (hx s₁ hs₁c)
    intro x hx
    rcases hKuv hx with hxu | hxv
    · exact hxu
    · exfalso
      exact (Set.disjoint_left.mp hUVdisj) (hKU hx) (hBV ⟨hx, fun hxu' => huv' x ⟨hx, hxu', hxv⟩⟩)
  · right
    have hKV : ⋂₀ c ⊆ V := fun x hx => hsub (hx s₁ hs₁c)
    intro x hx
    rcases hKuv hx with hxu | hxv
    · exfalso
      exact (Set.disjoint_left.mp hUVdisj)
        (hAU ⟨hx, fun hxv' => huv' x ⟨hx, hxu, hxv'⟩⟩) (hKV hx)
    · exact hxv

end Work.BoxShrink.PinchOff
