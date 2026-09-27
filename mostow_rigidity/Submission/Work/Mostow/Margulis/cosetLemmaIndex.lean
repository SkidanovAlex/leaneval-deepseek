import Mathlib
import Submission.Work.Mostow.Margulis.cosetLemma

set_option linter.style.haveILetI false

namespace Work.Mostow.Margulis

/-!
# The coset lemma, infinite index case

`Work.Mostow.Margulis.cosetLemmaIndex` is the `H.index = 0` companion of
`Work.Mostow.Margulis.cosetLemma` (Thurston 4.1.15): for a symmetric generating set `S` of a group
`G` and a subgroup `H` whose index is either `> n` or infinite (`H.index = 0`, i.e. the left coset
space `G ⧸ H` is infinite) there are `n + 1` elements, each a product of at most `n` elements of
`S`, lying in pairwise distinct left cosets of `H`.

The finite-index case is exactly `cosetLemma`; the infinite-index case is proved here.  Write
`X_j = cosetSpan S H j ⊆ G ⧸ H` for the set of cosets met by products of at most `j` elements of
`S`.  Two cases:

* If `X_n` is infinite, it contains a subset of cardinality `n + 1`, and each of its elements has a
  short representative.
* If `X_n` is finite, then all `X_j` (`j ≤ n`) are finite.  If `X_j = X_{j+1}` for some `j ≤ n`
  then `X_j = univ` (the stabilised set is invariant under the whole of `G`, which acts
  transitively), contradicting finiteness of `X_j` because `G ⧸ H` is infinite.  Hence the chain
  `X_0 ⊊ X_1 ⊊ ⋯ ⊊ X_n` is strictly increasing; as `|X_0| = 1`, this gives `|X_n| ≥ n + 1`.  Again
  every element of `X_n` has a short representative.
-/

/-- A subgroup of infinite index (`H.index = 0`, i.e. `Nat.card (G ⧸ H) = 0`) has infinite left
coset space. -/
lemma infinite_quotient_of_index_eq_zero {G : Type*} [Group G] (H : Subgroup G)
    (h : H.index = 0) : Infinite (G ⧸ H) := by
  have h0 : Nat.card (G ⧸ H) = 0 := by rw [← Subgroup.index_eq_card]; exact h
  rcases Nat.card_eq_zero.mp h0 with hE | hI
  · exact (hE.false (↑(1 : G) : G ⧸ H)).elim
  · exact hI

theorem cosetLemmaIndex {G : Type*} [Group G] (S : Set G) (H : Subgroup G) (n : ℕ)
    (hgen : Subgroup.closure S = ⊤) (hS : S = S⁻¹)
    (hcard : n < H.index ∨ H.index = 0) :
    ∃ a : Fin (n + 1) → G,
      (∀ i, ∃ l : List G, l.length ≤ n ∧ (∀ x ∈ l, x ∈ S) ∧ l.prod = a i) ∧
      (∀ i j, i ≠ j → (a i)⁻¹ * (a j) ∉ H) := by
  rcases hcard with hfin | hinf
  · exact cosetLemma S H n hgen hS hfin
  · haveI hInf : Infinite (G ⧸ H) := infinite_quotient_of_index_eq_zero H hinf
    -- The set of cosets met by products of at most `n` elements of `S` contains `n + 1`
    -- pairwise distinct cosets.
    have key : ∃ f : Fin (n + 1) → G ⧸ H,
        Function.Injective f ∧ ∀ i, f i ∈ cosetSpan S H n := by
      by_cases hXinf : (cosetSpan S H n).Infinite
      · obtain ⟨t, htsub, htcard⟩ := hXinf.exists_subset_card_eq (n + 1)
        obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin (n + 1))
          (s := t) (by rw [htcard, Fintype.card_fin])
        exact ⟨f, f.injective, fun i => htsub (hf (Set.mem_range_self i))⟩
      · have hXfin : (cosetSpan S H n).Finite := Set.not_infinite.mp hXinf
        -- the chain is strictly increasing
        have hstrict : ∀ j, j < n →
            (cosetSpan S H j).ncard < (cosetSpan S H (j + 1)).ncard := by
          intro j hj
          have hsub : cosetSpan S H j ⊆ cosetSpan S H (j + 1) := cosetSpan_succ S H j
          have hfin1 : (cosetSpan S H (j + 1)).Finite :=
            hXfin.subset (cosetSpan_mono S H (Nat.succ_le_of_lt hj))
          have hne : cosetSpan S H j ≠ cosetSpan S H (j + 1) := by
            intro he
            have huniv : cosetSpan S H j = Set.univ := cosetSpan_closed_eq_univ S H hgen hS he
            have hfinj : (cosetSpan S H j).Finite := hXfin.subset (cosetSpan_mono S H hj.le)
            exact (Set.infinite_univ (α := G ⧸ H)).not_finite (huniv ▸ hfinj)
          have hle : (cosetSpan S H j).ncard ≤ (cosetSpan S H (j + 1)).ncard :=
            Set.ncard_le_ncard hsub hfin1
          exact lt_of_le_of_ne hle fun he =>
            hne (Set.eq_of_subset_of_ncard_le hsub (le_of_eq he.symm) hfin1)
        have hge : n + 1 ≤ (cosetSpan S H n).ncard := by
          have keyj : ∀ j, j ≤ n → j + 1 ≤ (cosetSpan S H j).ncard := by
            intro j
            induction j with
            | zero => intro _; rw [cosetSpan_zero S H]; simp
            | succ k ih =>
                intro hk
                have h1 := hstrict k (by omega)
                have h2 := ih (by omega)
                omega
          exact keyj n le_rfl
        obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin (n + 1))
          (s := hXfin.toFinset)
          (by
            rw [Fintype.card_fin, ← Set.ncard_eq_toFinset_card (cosetSpan S H n) hXfin]
            exact hge)
        exact ⟨f, f.injective, fun i => by
          have h1 : f i ∈ hXfin.toFinset := hf (Set.mem_range_self i)
          rwa [Set.Finite.mem_toFinset] at h1⟩
    obtain ⟨f, hfinj, hfmem⟩ := key
    have hmem : ∀ i, ∃ g : G, g ∈ shortProd S n ∧ (↑g : G ⧸ H) = f i := fun i => hfmem i
    choose a ha using hmem
    refine ⟨a, fun i => (ha i).1, ?_⟩
    intro i j hij hmemH
    refine (fun he => hij (hfinj he)) ?_
    rw [← (ha i).2, ← (ha j).2]
    exact QuotientGroup.eq.mpr hmemH

end Work.Mostow.Margulis
