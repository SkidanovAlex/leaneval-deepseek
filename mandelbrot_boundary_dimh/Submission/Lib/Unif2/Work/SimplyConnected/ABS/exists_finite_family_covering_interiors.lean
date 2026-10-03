import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_chain_of_locallyFinite_closed_cover
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.tileEngulf

namespace Work.SimplyConnected.ABS

/-- The union over `insert a S` for a finite family, split at the inserted index. -/
lemma finset_biUnion_insert_of_nerve {X : Type*} {ι : Type*} [DecidableEq ι]
    (r : ι → Set X) (a : ι) (S : Finset ι) :
    (⋃ i ∈ insert a S, r i) = r a ∪ ⋃ i ∈ S, r i := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
  constructor
  · rintro ⟨i, (rfl | hi), hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨i, hi, hx⟩
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact ⟨a, Or.inl rfl, hx⟩
    · exact ⟨i, Or.inr hi, hx⟩

/-- The union of a family indexed by a nerve-chain is preconnected, provided each member is. -/
lemma isPreconnected_biUnion_toFinset_of_nerveChain {X : Type*} [TopologicalSpace X] {ι : Type*}
    [DecidableEq ι] {r : ι → Set X} (hpre : ∀ i, IsPreconnected (r i)) :
    ∀ L : List ι, L.IsChain (NerveRel r) → IsPreconnected (⋃ i ∈ L.toFinset, r i)
  | [], _ => by simpa using (isPreconnected_empty (α := X))
  | [a], _ => by simpa using hpre a
  | a :: b :: rest, hL => by
      have hR : NerveRel r a b := ((List.isChain_cons.mp hL).1) b (by simp)
      have htail : (b :: rest).IsChain (NerveRel r) := (List.isChain_cons.mp hL).2
      have ih := isPreconnected_biUnion_toFinset_of_nerveChain hpre (b :: rest) htail
      rw [List.toFinset_cons, finset_biUnion_insert_of_nerve]
      obtain ⟨x, hx1, hx2⟩ := hR
      have hbU : x ∈ ⋃ i ∈ (b :: rest).toFinset, r i :=
        Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨by simp, hx2⟩⟩
      exact IsPreconnected.union x hx1 hbU (hpre a) ih

/-- **A finite, connected family of a locally finite closed cover engulfing a compact set.**

Let `r` be a locally finite cover of a connected space `X` by closed sets *whose interiors cover*
`X`, and suppose each member is preconnected.  Then every compact `K` is contained in the union of
the interiors of finitely many members `r i`, `i ∈ s`, and moreover the union `⋃ i ∈ s, r i` is
preconnected (the family is chosen connected in the nerve of the cover). -/
theorem exists_finite_family_covering_interiors {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {ι : Type*} (r : ι → Set X) (hlf : LocallyFinite r) (hcl : ∀ i, IsClosed (r i))
    (hcov : (⋃ i, interior (r i)) = Set.univ) (hconn : ∀ i, IsPreconnected (r i))
    {K : Set X} (hK : IsCompact K) :
    ∃ s : Finset ι, K ⊆ ⋃ i ∈ s, interior (r i) ∧ IsPreconnected (⋃ i ∈ s, r i) := by
  classical
  -- the closed cover itself covers `X`
  have hcov' : (⋃ i, r i) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ ⋃ i, interior (r i) := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, interior_subset hi⟩
  -- only finitely many members of the cover meet the compact set `K`
  have hfin : {i | (r i ∩ K).Nonempty}.Finite := hlf.finite_nonempty_inter_compact hK
  set s0 : Finset ι := hfin.toFinset with hs0def
  have hs0mem : ∀ i, i ∈ s0 ↔ (r i ∩ K).Nonempty := by
    intro i; rw [hs0def]; exact Set.Finite.mem_toFinset hfin
  have hs0ne : ∀ i ∈ s0, (r i).Nonempty := by
    intro i hi
    exact Set.Nonempty.mono Set.inter_subset_left ((hs0mem i).mp hi)
  -- the interiors of these members already cover `K`
  have hKsub0 : K ⊆ ⋃ i ∈ s0, interior (r i) := by
    intro x hx
    have hxuniv : x ∈ ⋃ i, interior (r i) := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxuniv
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨(hs0mem i).mpr ⟨x, interior_subset hi, hx⟩, hi⟩⟩
  -- enlarge `s0` to a nerve-chain containing it
  obtain ⟨L, hs0L, _hLne, hLchain⟩ :=
    Work.SimplyConnected.ABS.exists_chain_of_locallyFinite_closed_cover hlf hcl hcov' hs0ne
  have hLchain' : L.IsChain (NerveRel r) := by
    rw [List.isChain_iff_getElem]
    intro k hk
    simpa only [List.get_eq_getElem, NerveRel] using hLchain k hk
  refine ⟨L.toFinset, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hKsub0 hx)
    obtain ⟨hs0i, hxi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨List.mem_toFinset.mpr (hs0L i hs0i), hxi⟩⟩
  · exact isPreconnected_biUnion_toFinset_of_nerveChain hconn L hLchain'

end Work.SimplyConnected.ABS
