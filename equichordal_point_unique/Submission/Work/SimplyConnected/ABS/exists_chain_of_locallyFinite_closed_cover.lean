import Mathlib
import Submission.Work.SimplyConnected.ABS.chain_of_reflTransGen_finset

/-!
# Chains in the nerve of a locally finite closed cover

Given a locally finite cover of a connected space `X` by closed sets `r i`, the "nerve" of the
cover (indices `i`, `j` adjacent when `r i ∩ r j ≠ ∅`) is connected on the indices carrying a
nonempty set.  Consequently, for any finite set `s` of indices with `(r i).Nonempty`, there is a
list of indices, containing all of `s`, on which consecutive entries have nonempty intersection.

The main work is `nerve_reachable_of_connected`, which shows that the set of indices reachable
from a fixed index in the nerve, together with its complement, form a pair of disjoint closed sets
covering `X`; connectedness then forces every index outside the reachable set to carry the empty
set.  The list is then produced by the purely combinatorial lemma
`chain_of_reflTransGen_finset`.
-/

namespace Work.SimplyConnected.ABS

/-- Two indices of a cover `r` of `X` are *nerve-adjacent* when the corresponding sets meet. -/
def NerveRel {X : Type*} {ι : Type*} (r : ι → Set X) : ι → ι → Prop :=
  fun a b => (r a ∩ r b).Nonempty

/-- The set of indices reachable from `i` in the nerve of the cover `r`. -/
def NerveReach {X : Type*} {ι : Type*} (r : ι → Set X) (i : ι) : Set ι :=
  {j | Relation.ReflTransGen (NerveRel r) i j}

lemma nerveRel_symm {X : Type*} {ι : Type*} {r : ι → Set X} {a b : ι}
    (h : NerveRel r a b) : NerveRel r b a :=
  h.mono (Set.inter_comm _ _).subset

/-- If `X` is connected and `r` is a locally finite cover of `X` by closed sets, then any two
indices carrying nonempty sets are joined by a walk in the nerve of the cover. -/
theorem nerve_reachable_of_connected {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {ι : Type*} {r : ι → Set X} (hlf : LocallyFinite r) (hcl : ∀ i, IsClosed (r i))
    (hcov : (⋃ i, r i) = Set.univ) {i j : ι} (hi : (r i).Nonempty) (hj : (r j).Nonempty) :
    Relation.ReflTransGen (NerveRel r) i j := by
  classical
  have hiJ : i ∈ NerveReach r i := Relation.ReflTransGen.refl
  set U : Set X := ⋃ k : NerveReach r i, r k.1 with hUdef
  set V : Set X := ⋃ k : {k : ι // k ∉ NerveReach r i}, r k.1 with hVdef
  have hUcl : IsClosed U := by
    rw [hUdef]
    exact (hlf.comp_injective Subtype.val_injective).isClosed_iUnion (fun k => hcl k.1)
  have hVcl : IsClosed V := by
    rw [hVdef]
    exact (hlf.comp_injective Subtype.val_injective).isClosed_iUnion (fun k => hcl k.1)
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    rw [hUdef] at hxU
    rw [hVdef] at hxV
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hxV
    exact l.2 (Relation.ReflTransGen.tail k.2 ⟨x, hk, hl⟩)
  have hcover : U ∪ V = Set.univ := by
    rw [hUdef, hVdef, Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_union, Set.mem_iUnion, Set.mem_iUnion]
    have hx : x ∈ ⋃ k, r k := by rw [hcov]; trivial
    rw [Set.mem_iUnion] at hx
    obtain ⟨k, hk⟩ := hx
    by_cases hkJ : k ∈ NerveReach r i
    · exact Or.inl ⟨⟨k, hkJ⟩, hk⟩
    · exact Or.inr ⟨⟨k, hkJ⟩, hk⟩
  have hUne : U.Nonempty :=
    ⟨hi.choose, by rw [hUdef]; exact Set.mem_iUnion.mpr ⟨⟨i, hiJ⟩, hi.choose_spec⟩⟩
  have hcompl : Uᶜ = V := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx' : x ∈ U ∪ V := by rw [hcover]; trivial
      rcases (Set.mem_union x U V).mp hx' with h | h
      · exact absurd h hx
      · exact h
    · intro x hxV hxU
      exact Set.disjoint_left.mp hdisj hxU hxV
  have hUopen : IsOpen U := by
    rw [← isClosed_compl_iff, hcompl]
    exact hVcl
  have hUuniv : U = Set.univ := IsClopen.eq_univ ⟨hUcl, hUopen⟩ hUne
  have hVempty : V = ∅ := by
    apply Set.Subset.antisymm
    · intro x hxV
      have hxUc : x ∈ Uᶜ := by rw [hcompl]; exact hxV
      exact hxUc (by rw [hUuniv]; trivial)
    · exact Set.empty_subset V
  have hjJ : j ∈ NerveReach r i := by
    by_contra hcon
    obtain ⟨x, hx⟩ := hj
    have hxV : x ∈ V := by
      rw [hVdef]
      exact Set.mem_iUnion.mpr ⟨⟨j, hcon⟩, hx⟩
    rw [hVempty] at hxV
    exact hxV
  exact hjJ

/-- Along a walk in the nerve from a nonempty member of the cover, all members encountered are
nonempty. -/
lemma nonempty_of_reflTransGen_inter {X : Type*} {ι : Type*} {r : ι → Set X} {a b : ι}
    (h : Relation.ReflTransGen (NerveRel r) a b) (ha : (r a).Nonempty) : (r b).Nonempty := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hbc.mono Set.inter_subset_right

/-- **Chain of a locally finite closed cover.**  If `X` is connected, `r` a locally finite cover
of `X` by closed sets, and `s` a finite set of indices all of whose sets are nonempty, then there
is a list `L` of indices containing `s`, consisting of nonempty sets, and such that consecutive
entries of `L` have nonempty intersection. -/
theorem exists_chain_of_locallyFinite_closed_cover {X : Type*} [TopologicalSpace X]
    [ConnectedSpace X] {ι : Type*} {r : ι → Set X} (hlf : LocallyFinite r)
    (hcl : ∀ i, IsClosed (r i)) (hcov : (⋃ i, r i) = Set.univ) {s : Finset ι}
    (hs : ∀ i ∈ s, (r i).Nonempty) :
    ∃ L : List ι, (∀ i ∈ s, i ∈ L) ∧ (∀ i ∈ L, (r i).Nonempty) ∧
      (∀ (k : ℕ) (hk : k + 1 < L.length),
        (r (L.get ⟨k, by omega⟩) ∩ r (L.get ⟨k + 1, hk⟩)).Nonempty) := by
  classical
  by_cases hsne : s = ∅
  · rw [hsne]
    exact ⟨[], by simp, by simp, by simp⟩
  · obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hsne
    have hi0ne : (r i0).Nonempty := hs i0 hi0
    have hreach : ∀ i ∈ s, Relation.ReflTransGen (NerveRel r) i0 i :=
      fun i hi => nerve_reachable_of_connected hlf hcl hcov hi0ne (hs i hi)
    obtain ⟨L, hLchain, hLhead, hLsub, hLreach⟩ :=
      chain_of_reflTransGen_finset (R := NerveRel r) (a := i0) (s := s)
        (fun a b h => nerveRel_symm h) hreach
    refine ⟨L, hLsub, ?_, ?_⟩
    · intro i hiL
      exact nonempty_of_reflTransGen_inter (hLreach i hiL) hi0ne
    · rw [List.isChain_iff_getElem] at hLchain
      intro k hk
      simpa only [List.get_eq_getElem, NerveRel] using hLchain k hk

end Work.SimplyConnected.ABS
