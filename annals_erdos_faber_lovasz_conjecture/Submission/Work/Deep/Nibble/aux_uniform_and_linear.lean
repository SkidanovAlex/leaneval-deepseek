import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.AuxDefs

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

variable {n M D : ℕ} {𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin M)} {ι : Fin n ↪ Fin M}
  {Mfam : Fin D → Set (Set (Fin n))}

/-- If `f` is disjoint from `ι '' V(M i)` then every vertex of `f` is outside
`ι '' V(M i)`. -/
theorem notMem_image_famVert_of_mem {f : Set (Fin M)} {i : Fin D}
    (hdisj : f ∩ ι '' famVert (Mfam i) = ∅) {v : Fin M} (hv : v ∈ f) :
    v ∉ ι '' famVert (Mfam i) := by
  intro hv'
  have hmem : v ∈ f ∩ ι '' famVert (Mfam i) := ⟨hv, hv'⟩
  rw [hdisj] at hmem
  exact hmem

/-- An edge `auxEdge f i` of `𝓗_aux` with `f ∈ 𝓖` and `f ∩ ι '' V(M i) = ∅`
has exactly `|f| + 1` vertices: the `e*`-vertex attached to `f`, plus the
copies `w^i` of the vertices `w ∈ f`. -/
theorem auxEdge_ncard (n M D : ℕ) {𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin M)}
    {ι : Fin n ↪ Fin M} {Mfam : Fin D → Set (Set (Fin n))} {f : Set (Fin M)} {i : Fin D}
    (hf : f ∈ 𝓖) (hdisj : f ∩ ι '' famVert (Mfam i) = ∅) :
    (auxEdge n M D 𝓖 ι Mfam f i).ncard = f.ncard + 1 := by
  have hcard : (auxEdge n M D 𝓖 ι Mfam f i).ncard =
      (insert (Sum.inl f) ((fun v : Fin M => Sum.inr (i, v)) '' f)).ncard := by
    refine Set.ncard_congr (s := auxEdge n M D 𝓖 ι Mfam f i)
      (t := insert (Sum.inl f) ((fun v : Fin M => Sum.inr (i, v)) '' f))
      (fun y _ => y.val) ?_ ?_ ?_
    · intro y hy
      rcases (val_mem_auxEdge y f i).1 hy with h | ⟨v, hval, hvf⟩
      · exact Set.mem_insert_iff.2 (Or.inl h)
      · refine Set.mem_insert_iff.2 (Or.inr ?_)
        rw [hval]
        exact Set.mem_image_of_mem (fun v : Fin M => Sum.inr (i, v)) hvf
    · intro a _ b _ h
      exact auxVertex_ext h
    · intro b hb
      rcases Set.mem_insert_iff.1 hb with hb | hb
      · exact ⟨auxVInl n M D 𝓖 ι Mfam f hf, (auxVInl_mem_auxEdge hf i).2 rfl, by
          rw [auxVInl_val hf, hb]⟩
      · obtain ⟨v, hvf, hval⟩ := (Set.mem_image (fun v : Fin M => Sum.inr (i, v)) f b).1 hb
        refine ⟨auxVInr n M D 𝓖 ι Mfam i v (notMem_image_famVert_of_mem hdisj hvf),
          (auxVInr_mem_auxEdge (notMem_image_famVert_of_mem hdisj hvf)).2 ⟨rfl, hvf⟩, ?_⟩
        rw [auxVInr_val (notMem_image_famVert_of_mem hdisj hvf)]
        exact hval
  have hnotin : Sum.inl f ∉ (fun v : Fin M => Sum.inr (i, v)) '' f := by
    rintro ⟨v, hv, hval⟩
    exact Sum.inl_ne_inr hval.symm
  have hinj : Set.InjOn (fun v : Fin M => (Sum.inr (i, v) : Set (Fin M) ⊕ Fin D × Fin M)) f := by
    intro a _ b _ h
    exact congrArg Prod.snd (Sum.inr.inj h)
  rw [hcard, Set.ncard_insert_of_notMem hnotin, Set.InjOn.ncard_image hinj]

/-- The auxiliary hypergraph `𝓗_aux` is `(r+1)`-uniform and linear. -/
theorem aux_uniform_and_linear {n M D r : ℕ} {𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin M)}
    {ι : Fin n ↪ Fin M} {Mfam : Fin D → Set (Set (Fin n))}
    (huni : ∀ f ∈ 𝓖, f.ncard = r) (hlin : 𝓖.IsLinear) :
    (∀ A ∈ Work.Deep.Nibble.auxHypergraph n M D 𝓖 ι Mfam, A.ncard = r + 1) ∧
      (Work.Deep.Nibble.auxHypergraph n M D 𝓖 ι Mfam).IsLinear := by
  constructor
  · intro A hA
    obtain ⟨f, hf, i, hdisj, hAeq⟩ := mem_auxHypergraph.1 hA
    subst hAeq
    rw [auxEdge_ncard n M D hf hdisj, huni f hf]
  · intro A₁ hA₁ A₂ hA₂ hne
    obtain ⟨f, hf, i, hdisj, hAeq⟩ := mem_auxHypergraph.1 hA₁
    subst hAeq
    obtain ⟨f', hf', i', hdisj', hAeq'⟩ := mem_auxHypergraph.1 hA₂
    subst hAeq'
    by_cases hff : f = f'
    · -- the two edges have the same `e*`-part: they differ only in the index `i`
      subst hff
      have hii : i ≠ i' := fun h => hne (by rw [h])
      have hval : ∀ y ∈ auxEdge n M D 𝓖 ι Mfam f i ∩ auxEdge n M D 𝓖 ι Mfam f i',
          y.val = Sum.inl f := by
        intro y hy
        rcases (val_mem_auxEdge y f i).1 hy.1 with h1 | ⟨v, h1, hvf⟩
        · exact h1
        · rcases (val_mem_auxEdge y f i').1 hy.2 with h2 | ⟨v', h2, hvf'⟩
          · exact absurd (h1.symm.trans h2) Sum.inr_ne_inl
          · exact absurd (congrArg Prod.fst (Sum.inr.inj (h1.symm.trans h2))) hii
      intro y hy z hz
      exact auxVertex_ext ((hval y hy).trans (hval z hz).symm)
    · -- the two edges have different `e*`-parts: their intersection lies in `f ∩ f'`
      have hval : ∀ y ∈ auxEdge n M D 𝓖 ι Mfam f i ∩ auxEdge n M D 𝓖 ι Mfam f' i',
          ∃ v, v ∈ f ∩ f' ∧ y.val = Sum.inr (i, v) := by
        intro y hy
        rcases (val_mem_auxEdge y f i).1 hy.1 with h1 | ⟨v, h1, hvf⟩
        · rcases (val_mem_auxEdge y f' i').1 hy.2 with h2 | ⟨v', h2, hvf'⟩
          · exact absurd (Sum.inl.inj (h1.symm.trans h2)) hff
          · exact absurd (h1.symm.trans h2) Sum.inl_ne_inr
        · rcases (val_mem_auxEdge y f' i').1 hy.2 with h2 | ⟨v', h2, hvf'⟩
          · exact absurd (h1.symm.trans h2) Sum.inr_ne_inl
          · have hpp : (i, v) = (i', v') := Sum.inr.inj (h1.symm.trans h2)
            have hvv : v = v' := congrArg Prod.snd hpp
            subst hvv
            exact ⟨v, ⟨hvf, hvf'⟩, h1⟩
      intro y hy z hz
      obtain ⟨v, hvf, h1⟩ := hval y hy
      obtain ⟨w, hwf, h2⟩ := hval z hz
      have hsub : (f ∩ f').Subsingleton := hlin hf hf' hff
      exact auxVertex_ext (by rw [h1, h2, hsub hvf hwf])

end Work.Deep.Nibble
