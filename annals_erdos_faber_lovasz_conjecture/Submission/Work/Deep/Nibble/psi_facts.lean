import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.AuxDefs

/-!
# The four facts about the paper's `ψ` used in `lem:pseudorandom_matching`

`lem:pseudorandom_matching` (`PseudorandomMatchingStatement`) applies the
matching theorem `cor:sparse_egj` to the auxiliary hypergraph `𝓗_aux`, whose
`(r+1)`-uniform edges are `{e*} ∪ {w^i : w ∈ e*}`.  Its verifications of the
hypotheses of `cor:sparse_egj` (efl.tex:1670–1700) use four elementary facts
about the map `ψ : E_meet → E(𝓗')` produced by `lem:embed`:

* (C1) `ψ(e*)` is an edge of `𝓗'` (counted with multiplicity), i.e. lies in
  `𝓗'.edgeSet` — the proper edges *and* the singleton copies;
* (C2) when every vertex of `𝓗'` is non-isolated, `ψ(e*) = e* ∩ V(𝓗')`, read
  through the embedding `ι` as `psiSet ι e* = {v | ι v ∈ e*}`;
* (C3) `ψ` commutes with `famVert`: an `M i` meets `e* ⊆ V(𝓖)` in `𝓖` iff it
  meets `ψ(e*)` in `𝓗'`;
* (C4) `eqn:unif_intersect`: at most `βD` of the `M i` meet any edge of `𝓖`
  (this is the hypothesis C4 transferred from `𝓗'` to `𝓖` via (C1)+(C2)+(C3)).

The bridge between the witness data and `ψ` is the `EmbedWitness` field `κ`,
the bijection identifying the edges of `𝓖` meeting `ι '' V(𝓗')` with the edges
of `𝓗'` counted with multiplicity.  The helpers below unpack `κ`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

variable {n r : ℕ} {D' C : ℝ} {𝓗' : MultiHypergraph n}

/-- The witness subtype `E_meet` of `lem:embed`: the edges of `𝓖` meeting the
image of the non-isolated vertices of `𝓗'`. -/
abbrev EmbedWitness.Emeet (W : EmbedWitness n r D' C 𝓗') : Type :=
  {e : Set (Fin W.M) // e ∈ W.𝓖 ∧ (e ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty}

/-- `ψ` of a proper edge of `𝓗'`: if `κ.symm` takes `f` to the left summand,
then `ψ f` is that edge. -/
theorem psiOf_inl (W : EmbedWitness n r D' C 𝓗') (e : Set (Fin n)) (he : e ∈ 𝓗'.edges)
    (f : Set (Fin W.M)) (hf : f ∈ W.𝓖)
    (hmeet : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty)
    (h : W.κ.symm ⟨f, hf, hmeet⟩ = Sum.inl ⟨e, he⟩) :
    psiOf W ⟨f, hf, hmeet⟩ = e := by
  unfold psiOf
  rw [h]

/-- `ψ` of a singleton copy `{v}` of `𝓗'`: if `κ.symm` takes `f` to the right
summand, then `ψ f = {v}`. -/
theorem psiOf_inr (W : EmbedWitness n r D' C 𝓗') (v : Fin n) (k : ℕ)
    (hkv : k < 𝓗'.singles v)
    (f : Set (Fin W.M)) (hf : f ∈ W.𝓖)
    (hmeet : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty)
    (h : W.κ.symm ⟨f, hf, hmeet⟩ = Sum.inr ⟨(v, k), hkv⟩) :
    psiOf W ⟨f, hf, hmeet⟩ = {v} := by
  unfold psiOf
  rw [h]

/-- `κ` sends the left summand back to its preimage. -/
theorem kappa_apply_inl (W : EmbedWitness n r D' C 𝓗') (e : Set (Fin n))
    (he : e ∈ 𝓗'.edges) (f : Set (Fin W.M)) (hf : f ∈ W.𝓖)
    (hmeet : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty)
    (h : W.κ.symm ⟨f, hf, hmeet⟩ = Sum.inl ⟨e, he⟩) :
    (W.κ (Sum.inl ⟨e, he⟩) : Set (Fin W.M)) = f := by
  have h2 : W.κ (Sum.inl ⟨e, he⟩) = ⟨f, hf, hmeet⟩ := by
    rw [← h, Equiv.apply_symm_apply]
  exact congrArg Subtype.val h2

/-- `κ` sends the right summand back to its preimage. -/
theorem kappa_apply_inr (W : EmbedWitness n r D' C 𝓗') (v : Fin n) (k : ℕ)
    (hkv : k < 𝓗'.singles v) (f : Set (Fin W.M)) (hf : f ∈ W.𝓖)
    (hmeet : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty)
    (h : W.κ.symm ⟨f, hf, hmeet⟩ = Sum.inr ⟨(v, k), hkv⟩) :
    (W.κ (Sum.inr ⟨(v, k), hkv⟩) : Set (Fin W.M)) = f := by
  have h2 : W.κ (Sum.inr ⟨(v, k), hkv⟩) = ⟨f, hf, hmeet⟩ := by
    rw [← h, Equiv.apply_symm_apply]
  exact congrArg Subtype.val h2

/-- `ψ` commutes with `famVert`: because `ι` is injective, `f ⊆ V(𝓖)` meets
`ι '' S` iff `ψ f` meets `S`.  This is (C3), and it needs no hypothesis on the
witness beyond injectivity of `ι`. -/
theorem psiSet_image_iff {n M : ℕ} (ι : Fin n ↪ Fin M) (f : Set (Fin M))
    (S : Set (Fin n)) : (f ∩ ι '' S).Nonempty ↔ (psiSet ι f ∩ S).Nonempty := by
  constructor
  · rintro ⟨x, hx, hx'⟩
    obtain ⟨v, hv, rfl⟩ := hx'
    exact ⟨v, mem_psiSet.mpr hx, hv⟩
  · rintro ⟨v, hv, hvS⟩
    exact ⟨ι v, mem_psiSet.mp hv, Set.mem_image_of_mem ι hvS⟩

/-- The four facts about the paper's `ψ` (`efl.tex:1670-1700`) that the proof of
`lem:pseudorandom_matching` uses: `ψ` of an `E_meet`-edge is an edge of `𝓗'`
(counted with multiplicity), `ψ` is `e* ↦ e* ∩ V(𝓗')` when every vertex of
`𝓗'` is non-isolated, `ψ` commutes with `famVert`, and `eqn:unif_intersect`: at
most `βD` of the `M i` meet any edge of `𝓖`. -/
theorem psi_facts {n r : ℕ} {D' C : ℝ} {𝓗' : ErdosFaberLovaszConjecture.MultiHypergraph n}
    (W : Work.Deep.Nibble.EmbedWitness n r D' C 𝓗')
    (hVuniv : ∀ v : Fin n, 0 < 𝓗'.deg v)
    {D : ℕ} (Mfam : Fin D → Set (Set (Fin n)))
    {β : ℝ} (hβ : 0 < β)
    (hbeta : ∀ e ∈ 𝓗'.edgeSet,
      (({i : Fin D | (e ∩ ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard : ℝ) ≤ β * D) :
    (∀ (f : Set (Fin W.M)) (hf : f ∈ W.𝓖)
        (hmeet : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty),
        Work.Deep.Nibble.psiOf W ⟨f, hf, hmeet⟩ ∈ 𝓗'.edgeSet) ∧
    (∀ (f : Set (Fin W.M)) (hf : f ∈ W.𝓖)
        (hmeet : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty),
        Work.Deep.Nibble.psiOf W ⟨f, hf, hmeet⟩ = Work.Deep.Nibble.psiSet W.ι f) ∧
    (∀ (f : Set (Fin W.M)) (i : Fin D),
        (f ∩ W.ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty ↔
          (Work.Deep.Nibble.psiSet W.ι f ∩ ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty) ∧
    (∀ (f : Set (Fin W.M)) (hf : f ∈ W.𝓖),
        (({i : Fin D | (f ∩ W.ι '' ErdosFaberLovaszConjecture.famVert (Mfam i)).Nonempty}).ncard : ℝ) ≤ β * D) := by
  -- (C1) + (C2) for a single edge of `𝓖` meeting `ι '' V(𝓗')`, by cases on `κ.symm`.
  have key : ∀ (f : Set (Fin W.M)) (hf : f ∈ W.𝓖)
      (hmeet : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty),
      psiOf W ⟨f, hf, hmeet⟩ = psiSet W.ι f ∧ psiOf W ⟨f, hf, hmeet⟩ ∈ 𝓗'.edgeSet := by
    intro f hf hmeet
    rcases h : W.κ.symm ⟨f, hf, hmeet⟩ with ⟨e, he⟩ | ⟨⟨v, k⟩, hkv0⟩
    · -- `f` is the image of the proper edge `e ∈ 𝓗'.edges`.
      have hk : (W.κ (Sum.inl ⟨e, he⟩) : Set (Fin W.M)) = f :=
        kappa_apply_inl W e he f hf hmeet h
      have hinter : f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v} = W.ι '' e := by
        rw [← hk]; exact W.meet_inl e he
      have hpsi : psiOf W ⟨f, hf, hmeet⟩ = e := psiOf_inl W e he f hf hmeet h
      refine ⟨?_, ?_⟩
      · -- `e = ψ f = {v | ι v ∈ f}`: `ι '' e = f ∩ ι '' V(𝓗')`, and every
        -- vertex of `𝓗'` is non-isolated.
        rw [hpsi]
        ext v'
        constructor
        · intro hv'
          have h1 : W.ι v' ∈ W.ι '' e := Set.mem_image_of_mem _ hv'
          rw [← hinter] at h1
          exact mem_psiSet.mpr h1.1
        · intro hv'
          have h1 : W.ι v' ∈ f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v} :=
            ⟨mem_psiSet.mp hv', Set.mem_image_of_mem _ (hVuniv v')⟩
          rw [hinter] at h1
          obtain ⟨v'', hv'', hveq⟩ := h1
          have hvv : v'' = v' := W.ι.inj' hveq
          subst hvv
          exact hv''
      · rw [hpsi]
        exact MultiHypergraph.mem_edgeSet.2 (Or.inl he)
    · -- `f` is the image of the singleton copy `{v}`.
      have hkv : k < 𝓗'.singles v := hkv0
      have hk : (W.κ (Sum.inr ⟨(v, k), hkv⟩) : Set (Fin W.M)) = f :=
        kappa_apply_inr W v k hkv f hf hmeet (by simpa only [] using h)
      have hinter : f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v} = {W.ι v} := by
        rw [← hk]; exact W.meet_inr v k hkv
      have hpsi : psiOf W ⟨f, hf, hmeet⟩ = {v} :=
        psiOf_inr W v k hkv f hf hmeet (by simpa only [] using h)
      refine ⟨?_, ?_⟩
      · rw [hpsi]
        ext v'
        constructor
        · intro hv'
          have hvv : v' = v := by simpa using hv'
          rw [hvv]
          have h1 : W.ι v ∈ f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v} := by
            rw [hinter]; exact Set.mem_singleton (W.ι v)
          exact h1.1
        · intro hv'
          have h1 : W.ι v' ∈ f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v} :=
            ⟨mem_psiSet.mp hv', Set.mem_image_of_mem _ (hVuniv v')⟩
          rw [hinter] at h1
          have hvv : v' = v := W.ι.inj' (by simpa using h1)
          exact Set.mem_singleton_iff.mpr hvv
      · rw [hpsi]
        exact MultiHypergraph.mem_edgeSet.2 (Or.inr ⟨v, rfl, by omega⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf hmeet
    exact (key f hf hmeet).2
  · intro f hf hmeet
    exact (key f hf hmeet).1
  · intro f i
    exact psiSet_image_iff W.ι f (famVert (Mfam i))
  · -- (C4): transfer the hypothesis from `𝓗'` to `𝓖` via (C1)–(C3).
    intro f hf
    by_cases hmeet : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty
    · obtain ⟨hpsi_eq, hpsi_mem⟩ := key f hf hmeet
      have hset : {i : Fin D | (f ∩ W.ι '' famVert (Mfam i)).Nonempty}
          = {i : Fin D | (psiSet W.ι f ∩ famVert (Mfam i)).Nonempty} := by
        ext i
        exact psiSet_image_iff W.ι f (famVert (Mfam i))
      have hb := hbeta (psiOf W ⟨f, hf, hmeet⟩) hpsi_mem
      rw [hset, ← hpsi_eq]
      exact hb
    · -- `f` misses `ι '' V(𝓗')` and hence meets no `ι '' famVert (Mfam i)`.
      have hempty : {i : Fin D | (f ∩ W.ι '' famVert (Mfam i)).Nonempty} = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨i, hi⟩
        obtain ⟨x, hx, hx'⟩ := hi
        obtain ⟨v, hv, rfl⟩ := hx'
        exact hmeet ⟨W.ι v, hx, Set.mem_image_of_mem _ (hVuniv v)⟩
      rw [hempty]
      simp only [Set.ncard_empty, Nat.cast_zero]
      exact mul_nonneg hβ.le (Nat.cast_nonneg D)

end

end Work.Deep.Nibble
