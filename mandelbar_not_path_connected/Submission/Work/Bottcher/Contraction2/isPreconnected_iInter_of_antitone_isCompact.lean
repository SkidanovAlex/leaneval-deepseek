import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Decreasing intersections of compact preconnected sets are preconnected

If `A : ℕ → Set ℂ` is a decreasing sequence of compact preconnected subsets of `ℂ`,
then `⋂ n, A n` is preconnected.

The argument is the classical one for nested continua.  Suppose `S = ⋂ n, A n` were
separated by open sets `u, v` with `S ⊆ u ∪ v` and `S ∩ u ∩ v = ∅`, with `S` meeting both
`u` and `v`.  The two compact sets `S \ v` and `S \ u` are disjoint, so by normality they
are separated by disjoint open sets `U ⊇ S \ v` and `V ⊇ S \ u`; since `S = (S \ v) ∪ (S \ u)`
we get `S ⊆ U ∪ V`, and both `U` and `V` meet `S`.  Compactness of `A 0` (Cantor's
intersection theorem) now forces some `A N ⊆ U ∪ V`, contradicting preconnectedness of
`A N`, since `U` and `V` are disjoint open sets both meeting `A N`.
-/

namespace Work.Bottcher.Contraction2

theorem isPreconnected_iInter_of_antitone_isCompact {A : ℕ → Set ℂ}
    (hcpt : ∀ n, IsCompact (A n)) (hpre : ∀ n, IsPreconnected (A n))
    (hanti : ∀ n, A (n + 1) ⊆ A n) : IsPreconnected (⋂ n, A n) := by
  set S : Set ℂ := ⋂ n, A n with hS
  have hSclosed : IsClosed S := by
    rw [hS]; exact isClosed_iInter fun n => (hcpt n).isClosed
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hSuv hSuv'
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnotu, hnotv⟩ := hcon
  -- `S \ v` and `S \ u` are disjoint closed sets, separated by disjoint open sets.
  have hF1closed : IsClosed (S \ v) := hSclosed.sdiff hv
  have hF2closed : IsClosed (S \ u) := hSclosed.sdiff hu
  have hFdisj : Disjoint (S \ v) (S \ u) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases hSuv hx1.1 with hxu | hxv
    · exact hx2.2 hxu
    · exact hx1.2 hxv
  obtain ⟨U, V, hUo, hVo, hF1U, hF2V, hUV⟩ :=
    NormalSpace.normal (S \ v) (S \ u) hF1closed hF2closed hFdisj
  -- `S = (S \ v) ∪ (S \ u)`, hence `S ⊆ U ∪ V`.
  have hSUV : S ⊆ U ∪ V := by
    intro x hx
    rcases hSuv hx with hxu | hxv
    · by_cases hxv' : x ∈ v
      · exfalso
        have hm : x ∈ S ∩ (u ∩ v) := ⟨hx, hxu, hxv'⟩
        rw [hSuv'] at hm
        exact hm
      · exact Or.inl (hF1U ⟨hx, hxv'⟩)
    · by_cases hxu' : x ∈ u
      · exfalso
        have hm : x ∈ S ∩ (u ∩ v) := ⟨hx, hxu', hxv⟩
        rw [hSuv'] at hm
        exact hm
      · exact Or.inr (hF2V ⟨hx, hxu'⟩)
  -- `U` and `V` both meet `S`.
  obtain ⟨a, haS, hav⟩ := Set.not_subset.mp hnotv
  obtain ⟨b, hbS, hbu⟩ := Set.not_subset.mp hnotu
  have haU : a ∈ U := hF1U ⟨haS, hav⟩
  have hbV : b ∈ V := hF2V ⟨hbS, hbu⟩
  have hKclosed : IsClosed ((U ∪ V)ᶜ : Set ℂ) := isClosed_compl_iff.mpr (hUo.union hVo)
  have hIntEmpty : (⋂ n, A n ∩ (U ∪ V)ᶜ) = ∅ := by
    rw [← Set.iInter_inter ((U ∪ V)ᶜ) A]
    rw [hS.symm]
    ext x
    constructor
    · intro hx; exact hx.2 (hSUV hx.1)
    · intro hx; exact (hx : False).elim
  -- Cantor: some `A N` is covered by `U ∪ V`.
  obtain ⟨N, hN⟩ : ∃ N, A N ⊆ U ∪ V := by
    by_contra h
    rw [not_exists] at h
    have hne : ∀ n, (A n ∩ (U ∪ V)ᶜ : Set ℂ).Nonempty := by
      intro n
      obtain ⟨x, hxA, hx⟩ := Set.not_subset.mp (h n)
      exact ⟨x, hxA, by simpa using hx⟩
    have hnested : ∀ i, (A (i+1) ∩ (U ∪ V)ᶜ : Set ℂ) ⊆ A i ∩ (U ∪ V)ᶜ := by
      intro i x hx
      exact ⟨hanti i hx.1, hx.2⟩
    have hcomp : IsCompact (A 0 ∩ (U ∪ V)ᶜ : Set ℂ) := (hcpt 0).inter_right hKclosed
    have hcl : ∀ i, IsClosed (A i ∩ (U ∪ V)ᶜ : Set ℂ) :=
      fun i => (hcpt i).isClosed.inter hKclosed
    have hnei := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => A n ∩ (U ∪ V)ᶜ) hnested hne hcomp hcl
    rw [hIntEmpty] at hnei
    exact Set.not_nonempty_empty hnei
  have hSsubN : S ⊆ A N := hS ▸ Set.iInter_subset A N
  have hANint : (A N ∩ (U ∩ V) : Set ℂ) = ∅ := by rw [hUV.inter_eq]; simp
  -- `A N` is preconnected but meets both disjoint open sets `U` and `V`.
  rcases (isPreconnected_iff_subset_of_disjoint.mp (hpre N)) U V hUo hVo hN hANint with hAU | hAV
  · have hm : b ∈ U ∩ V := ⟨hAU (hSsubN hbS), hbV⟩
    rw [hUV.inter_eq] at hm
    exact hm
  · have hm : a ∈ U ∩ V := ⟨haU, hAV (hSsubN haS)⟩
    rw [hUV.inter_eq] at hm
    exact hm

end Work.Bottcher.Contraction2
