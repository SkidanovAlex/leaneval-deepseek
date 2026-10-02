import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.ContractionAux

open Set

/-- If `S ⊆ ℂ` is preconnected and contains `0`, then its preimage under `z ↦ z ^ 2` is
preconnected.

The map `z ↦ z ^ 2` is a two-to-one cover branched at `0`.  The preimage `T` of `S` is
symmetric under `z ↦ -z` and contains `0`.  Given a clopen piece `D ⊆ T` with `0 ∉ D`,
the set `D' = D ∪ (-D)` is clopen in `T`, symmetric, and its complement `A' = T \ D'`
contains `0`.  Since squaring is an open map, `(· ^ 2) '' D' = S ∩ (· ^ 2) '' D'.'` etc.
are open in `S`, giving a partition of the preconnected `S`, a contradiction. -/
theorem isPreconnected_preimage_sq {S : Set ℂ} (hS : IsPreconnected S) (h0 : (0 : ℂ) ∈ S) :
    IsPreconnected {z : ℂ | z ^ 2 ∈ S} := by
  set f : ℂ → ℂ := fun z => z ^ 2 with hf
  have hf_open : IsOpenMap f := by rw [hf]; exact (Complex.isOpenQuotientMap_pow 2).isOpenMap
  have hf_surj : Function.Surjective f := by
    rw [hf]; exact (Complex.isOpenQuotientMap_pow 2).surjective
  set T : Set ℂ := {z : ℂ | z ^ 2 ∈ S} with hT
  have hTf : ∀ z, z ∈ T ↔ f z ∈ S := by
    intro z; rw [hT]; simp only [mem_ofPred_eq, hf]
  have hfT : f '' T = S := by
    ext w; constructor
    · rintro ⟨z, hz, rfl⟩; exact (hTf z).mp hz
    · intro hw; obtain ⟨z, hz⟩ := hf_surj w
      exact ⟨z, (hTf z).mpr (by rw [hz]; exact hw), hz⟩
  have h0T : (0 : ℂ) ∈ T := (hTf 0).mpr (by rw [hf]; simpa using h0)
  have hTsym : ∀ z, z ∈ T ↔ -z ∈ T := by
    intro z; rw [hTf z, hTf (-z)]; rw [hf]; simp only [neg_sq]
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdisj
  by_contra hgo
  rw [not_or, not_subset, not_subset] at hgo
  obtain ⟨⟨x, hxT, hxu⟩, ⟨y, hyT, hyv⟩⟩ := hgo
  have hxv : x ∈ v := (hcov hxT).resolve_left hxu
  have hyu : y ∈ u := (hcov hyT).resolve_right hyv
  have key : ∀ (a b : Set ℂ), IsOpen a → IsOpen b → T ⊆ a ∪ b → T ∩ (a ∩ b) = ∅ →
      (0 : ℂ) ∉ a → (T ∩ a).Nonempty → False := by
    intro a b ha hb hab hdis h0a hTa
    set a' : Set ℂ := a ∪ (fun z : ℂ => -z) ⁻¹' a with ha'def
    set b' : Set ℂ := b ∩ (fun z : ℂ => -z) ⁻¹' b with hb'def
    have ha' : IsOpen a' := by rw [ha'def]; exact ha.union (continuous_neg.isOpen_preimage a ha)
    have hb' : IsOpen b' := by rw [hb'def]; exact hb.inter (continuous_neg.isOpen_preimage b hb)
    have hiff : ∀ z ∈ T, z ∈ a' ↔ z ∉ b' := by
      intro z hz
      have hnegT : -z ∈ T := (hTsym z).mp hz
      have hzab : z ∈ a ∪ b := hab hz
      have hnab : -z ∈ a ∪ b := hab hnegT
      have hznab : z ∉ a ∩ b := by
        intro h; have hh : z ∈ T ∩ (a ∩ b) := ⟨hz, h⟩; rw [hdis] at hh; exact hh
      have hnnab : -z ∉ a ∩ b := by
        intro h; have hh : -z ∈ T ∩ (a ∩ b) := ⟨hnegT, h⟩; rw [hdis] at hh; exact hh
      rw [ha'def, hb'def, mem_union, mem_preimage]
      constructor
      · intro h ⟨hbz, hbn⟩
        rcases h with h | h
        · exact hznab ⟨h, hbz⟩
        · exact hnnab ⟨h, hbn⟩
      · intro h
        by_cases hza : z ∈ a
        · exact Or.inl hza
        · right
          rcases hzab with h' | h'
          · exact absurd h' hza
          · by_contra hna
            rcases hnab with h1 | h1
            · exact hna h1
            · exact h ⟨h', h1⟩
    have ha'sym : ∀ z, z ∈ a' ↔ -z ∈ a' := by
      intro z; rw [ha'def]; simp only [mem_union, mem_preimage, neg_neg]; exact or_comm
    have hTsub : T ⊆ (T ∩ a') ∪ (T ∩ b') := by
      intro z hz
      by_cases hza : z ∈ a'
      · exact Or.inl ⟨hz, hza⟩
      · refine Or.inr ⟨hz, ?_⟩
        by_contra hzb
        exact hza ((hiff z hz).mpr hzb)
    have hDisj' : (T ∩ a') ∩ (T ∩ b') = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨z, ⟨hzT, hza⟩, ⟨_, hzb⟩⟩
      exact (hiff z hzT).mp hza hzb
    have hD'ne : (T ∩ a').Nonempty :=
      hTa.mono (fun z hz => ⟨hz.1, by rw [ha'def]; exact Or.inl hz.2⟩)
    have h0D' : (0 : ℂ) ∉ T ∩ a' := by
      rintro ⟨-, h0a'⟩
      rw [ha'def] at h0a'
      rcases h0a' with h | h
      · exact h0a h
      · exact h0a (by simpa using h)
    have h0A' : (0 : ℂ) ∈ T ∩ b' := by
      rcases hTsub h0T with h | h
      · exact absurd h h0D'
      · exact h
    have himg : ∀ c : Set ℂ, f '' (T ∩ c) = S ∩ f '' c := by
      intro c; ext w; constructor
      · rintro ⟨z, hz, hfz⟩
        exact ⟨by rw [← hfz]; exact (hTf z).mp hz.1, ⟨z, hz.2, hfz⟩⟩
      · rintro ⟨hwS, z, hzc, hfz⟩
        exact ⟨z, ⟨(hTf z).mpr (by rw [hfz]; exact hwS), hzc⟩, hfz⟩
    have hDa : f '' (T ∩ a') = S ∩ f '' a' := himg a'
    have hDb : f '' (T ∩ b') = S ∩ f '' b' := himg b'
    have hne1 : (S ∩ f '' a').Nonempty := by rw [← hDa]; exact hD'ne.image f
    have hne2 : (S ∩ f '' b').Nonempty := by
      rw [← hDb]; exact ⟨f 0, ⟨0, h0A', rfl⟩⟩
    have hDisjImg : f '' (T ∩ a') ∩ f '' (T ∩ b') = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨z, ⟨p, ⟨hpT, hpa⟩, hfp⟩, ⟨q, ⟨hqT, hqb⟩, hfq⟩⟩
      have hpq : p ^ 2 = q ^ 2 := by show f p = f q; rw [hfp, hfq]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hpq with h | h
      · rw [h] at hpa
        exact (hiff q hqT).mp hpa hqb
      · have hqa : q ∈ a' := (ha'sym q).mpr (by rw [h] at hpa; exact hpa)
        exact (hiff q hqT).mp hqa hqb
    have hcover : S ⊆ f '' a' ∪ f '' b' := by
      intro w hw
      rw [← hfT] at hw
      rcases hw with ⟨z, hz, rfl⟩
      rcases hTsub hz with ⟨-, hza⟩ | ⟨-, hzb⟩
      · exact Or.inl ⟨z, hza, rfl⟩
      · exact Or.inr ⟨z, hzb, rfl⟩
    have hndisj : S ∩ (f '' a' ∩ f '' b') = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨w, hwS, hwa, hwb⟩
      have hwa' : w ∈ f '' (T ∩ a') := by rw [hDa]; exact ⟨hwS, hwa⟩
      have hwb' : w ∈ f '' (T ∩ b') := by rw [hDb]; exact ⟨hwS, hwb⟩
      have hmem : w ∈ f '' (T ∩ a') ∩ f '' (T ∩ b') := ⟨hwa', hwb'⟩
      rw [hDisjImg] at hmem
      exact hmem
    have hcon := hS (f '' a') (f '' b') (hf_open a' ha') (hf_open b' hb') hcover hne1 hne2
    rw [hndisj] at hcon
    obtain ⟨w, hw⟩ := hcon
    exact hw
  by_cases h0u : (0 : ℂ) ∈ u
  · have h0v : (0 : ℂ) ∉ v := by
      intro hv0; have hh : (0 : ℂ) ∈ T ∩ (u ∩ v) := ⟨h0T, h0u, hv0⟩
      rw [hdisj] at hh; exact hh
    exact key v u hv hu (by rw [union_comm]; exact hcov) (by rw [inter_comm v u]; exact hdisj)
      h0v ⟨x, hxT, hxv⟩
  · exact key u v hu hv hcov hdisj h0u ⟨y, hyT, hyu⟩

end Work.Bottcher.ContractionAux
