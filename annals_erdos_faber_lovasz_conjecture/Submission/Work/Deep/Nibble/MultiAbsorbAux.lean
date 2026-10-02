import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.Defs
import Submission.Work.Deep.Nibble.Glue
import Submission.EFL.InternalMain
import Submission.EFL.Comm.InternalMatchingConnect

/-!
# Multi-hypergraph form of the §7 absorption lemmas — the bridge

The cone's absorption lemmas (`crossing_absorption`, `internal_absorption`,
`crossing_iter`, `internal_iter` in `Submission/EFL/`) are stated for a
`Hypergraph` `𝓗 : Set (Set (Fin n))` and families of edges `N : Set 𝓗` (a
subtype).  The §7 assembly of `lem:nibble2` works with `MultiHypergraph`
matchings, i.e. plain `Set (Set (Fin n))` families, and needs the absorption in
that language.

This module provides the thin bridge: the ambient hypergraph is `𝓜.edgeSet`
(all edges of the multi-hypergraph, singletons included), the map `toAbs` sends
a family of edges of `𝓜` to a family of edges of that hypergraph, and `ofAbs`
is its inverse on the image.
-/

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- A family `N` of vertex sets all of which are edges of `𝓜`, regarded as a
family of edges of the hypergraph `𝓜.edgeSet`. -/
def toAbs {𝓜 : MultiHypergraph n} (N : Set (Set (Fin n)))
    (h : N ⊆ MultiHypergraph.edgeSet 𝓜) :
    Set ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)) :=
  {e | (e : Set (Fin n)) ∈ N}

@[simp]
theorem mem_toAbs {𝓜 : MultiHypergraph n} {N : Set (Set (Fin n))}
    {h : N ⊆ MultiHypergraph.edgeSet 𝓜}
    {e : ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n))} :
    e ∈ toAbs N h ↔ (e : Set (Fin n)) ∈ N := Iff.rfl

/-- The image of a family of edges of `𝓜.edgeSet` back in `Set (Set (Fin n))`. -/
def ofAbs {𝓜 : MultiHypergraph n} (M : Set ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n))) :
    Set (Set (Fin n)) :=
  Subtype.val '' M

theorem mem_ofAbs {𝓜 : MultiHypergraph n}
    {M : Set ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n))} {e : Set (Fin n)} :
    e ∈ ofAbs M ↔ ∃ (h : e ∈ MultiHypergraph.edgeSet 𝓜),
      (⟨e, h⟩ : ↥(MultiHypergraph.edgeSet 𝓜)) ∈ M := by
  constructor
  · rintro ⟨x, hx, hxe⟩
    subst hxe
    exact ⟨x.2, by simpa using hx⟩
  · rintro ⟨h, he⟩
    exact ⟨⟨e, h⟩, he, rfl⟩

theorem ofAbs_subset (𝓜 : MultiHypergraph n)
    (M : Set ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n))) :
    ofAbs M ⊆ MultiHypergraph.edgeSet 𝓜 := by
  rintro e ⟨x, -, rfl⟩
  exact x.2

theorem ofAbs_mono {𝓜 : MultiHypergraph n}
    {M M' : Set ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n))} (h : M ⊆ M') :
    ofAbs M ⊆ ofAbs M' := by
  rintro e ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem ofAbs_toAbs {𝓜 : MultiHypergraph n} {N : Set (Set (Fin n))}
    (hN : N ⊆ MultiHypergraph.edgeSet 𝓜) :
    ofAbs (toAbs N hN) = N := by
  ext e
  rw [mem_ofAbs]
  constructor
  · rintro ⟨h, he⟩
    simpa using he
  · intro he
    exact ⟨hN he, he⟩

theorem toAbs_ofAbs (𝓜 : MultiHypergraph n)
    (M : Set ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n))) :
    toAbs (ofAbs M) (ofAbs_subset 𝓜 M) = M := by
  ext e
  rw [mem_toAbs, mem_ofAbs]
  constructor
  · rintro ⟨h, he⟩
    convert he using 2
  · intro he
    exact ⟨e.2, he⟩

theorem famVert_ofAbs (𝓜 : MultiHypergraph n)
    (M : Set ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n))) :
    famVert (ofAbs M) = matchVert M := by
  ext v
  rw [mem_famVert, mem_matchVert]
  constructor
  · rintro ⟨e, ⟨x, hx, rfl⟩, hv⟩
    exact ⟨x, hx, hv⟩
  · rintro ⟨x, hx, hv⟩
    exact ⟨x.1, ⟨x, hx, rfl⟩, hv⟩

theorem matchVert_toAbs {𝓜 : MultiHypergraph n} {N : Set (Set (Fin n))}
    (hN : N ⊆ MultiHypergraph.edgeSet 𝓜) :
    matchVert (toAbs N hN) = famVert N := by
  ext v
  rw [mem_famVert, mem_matchVert]
  constructor
  · rintro ⟨e, he, hv⟩
    exact ⟨e.1, he, hv⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨⟨e, hN he⟩, he, hv⟩

theorem pseudoRandom_toAbs_iff {𝓜 : MultiHypergraph n} {N : Set (Set (Fin n))}
    (hN : N ⊆ MultiHypergraph.edgeSet 𝓜) (𝓕 : Set (Set (Fin n))) (γ κ : ℝ) :
    PseudoRandom (toAbs N hN) 𝓕 γ κ ↔ PseudoRandomFam N 𝓕 γ κ := by
  simp only [PseudoRandom, PseudoRandomFam, matchVert_toAbs]

theorem covers_toAbs_iff {𝓜 : MultiHypergraph n} {N : Set (Set (Fin n))}
    (hN : N ⊆ MultiHypergraph.edgeSet 𝓜) (X : Set (Fin n)) :
    Covers (toAbs N hN) X ↔ CoversFamMulti N X := by
  simp only [Covers, CoversFamMulti, matchVert_toAbs]

theorem disjoint_toAbs_iff {𝓜 : MultiHypergraph n} {N N' : Set (Set (Fin n))}
    (hN : N ⊆ MultiHypergraph.edgeSet 𝓜) (hN' : N' ⊆ MultiHypergraph.edgeSet 𝓜) :
    Disjoint (toAbs N hN) (toAbs N' hN') ↔ Disjoint N N' := by
  constructor
  · intro h
    rw [Set.disjoint_left] at h ⊢
    intro e he he'
    exact h (show (⟨e, hN he⟩ : ↥(MultiHypergraph.edgeSet 𝓜)) ∈ toAbs N hN from he)
      (show (⟨e, hN he⟩ : ↥(MultiHypergraph.edgeSet 𝓜)) ∈ toAbs N' hN' from he')
  · intro h
    rw [Set.disjoint_left] at h ⊢
    intro e he he'
    exact h he he'

theorem disjoint_ofAbs_iff {𝓜 : MultiHypergraph n}
    {M M' : Set ↥(MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n))} :
    Disjoint (ofAbs M) (ofAbs M') ↔ Disjoint M M' := by
  constructor
  · intro h
    rw [Set.disjoint_left] at h ⊢
    intro e he he'
    exact h ⟨e, he, rfl⟩ ⟨e, he', rfl⟩
  · intro h
    rw [Set.disjoint_left] at h ⊢
    intro e he he'
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨y, hy, hye⟩ := he'
    exact h hx (Subtype.ext hye.symm ▸ hy)

theorem isMatching_toAbs_iff {𝓜 : MultiHypergraph n} {N : Set (Set (Fin n))}
    (hN : N ⊆ MultiHypergraph.edgeSet 𝓜) :
    MultiHypergraph.IsMatching 𝓜 N ↔
      IsMatching
        (MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)) (toAbs N hN) := by
  have key : (toAbs N hN).Pairwise (fun a b : ↥(MultiHypergraph.edgeSet 𝓜) =>
        Disjoint (a : Set (Fin n)) (b : Set (Fin n))) ↔
      N.Pairwise (fun a b : Set (Fin n) => Disjoint a b) := by
    constructor
    · intro h a ha b hb hne
      exact h (x := (⟨a, hN ha⟩ : ↥(MultiHypergraph.edgeSet 𝓜))) (by exact ha)
        (y := (⟨b, hN hb⟩ : ↥(MultiHypergraph.edgeSet 𝓜))) (by exact hb)
        (fun hh => hne (congrArg Subtype.val hh))
    · intro h a ha b hb hne
      exact h (x := (a : Set (Fin n))) ha (y := (b : Set (Fin n))) hb
        (fun hh => hne (Subtype.ext hh))
  refine ⟨?_, ?_⟩
  · rintro ⟨-, hp⟩
    exact key.mpr hp
  · intro hp
    exact ⟨hN, key.mp hp⟩

/-- The edges of `𝓜.pow2` are exactly the two-element edges of `𝓜.edgeSet`. -/
theorem pow2_eq (𝓜 : MultiHypergraph n) :
    Hypergraph.pow2 (MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)) =
      MultiHypergraph.pow2 𝓜 := by
  ext e
  rw [mem_powFam, MultiHypergraph.mem_pow2, MultiHypergraph.mem_edgeSet]
  constructor
  · rintro ⟨h | ⟨v, rfl, -⟩, h2⟩
    · exact ⟨h, h2⟩
    · rw [edgeSize_eq_ncard, Set.ncard_singleton] at h2
      omega
  · rintro ⟨h, h2⟩
    exact ⟨Or.inl h, h2⟩

/-- The 2-uniform part of the 2-uniform part is itself. -/
theorem pow2_pow2 (𝓜 : MultiHypergraph n) :
    Hypergraph.pow2 (MultiHypergraph.pow2 𝓜) = MultiHypergraph.pow2 𝓜 := by
  ext e
  rw [mem_powFam, MultiHypergraph.mem_pow2]
  constructor
  · rintro ⟨⟨h, h2⟩, -⟩
    exact ⟨h, h2⟩
  · rintro ⟨h, h2⟩
    exact ⟨⟨h, h2⟩, h2⟩

/-- `incidentTwo` of the full edge set of a multi-hypergraph is the same as
`incidentTwo` of its 2-uniform part. -/
theorem incidentTwo_edgeSet (𝓜 : MultiHypergraph n) (U : Set (Fin n)) :
    incidentTwo (MultiHypergraph.edgeSet 𝓜 : Hypergraph (Fin n)) U =
      incidentTwo (MultiHypergraph.pow2 𝓜) U := by
  rw [incidentTwo, incidentTwo, pow2_eq, pow2_pow2]

/-- Every edge of `𝓜.edgeSet` of size at least two is a proper edge. -/
theorem edges_of_mem_edgeSet_of_two_le {𝓜 : MultiHypergraph n} {e : Set (Fin n)}
    (he : e ∈ MultiHypergraph.edgeSet 𝓜) (h2 : 2 ≤ e.ncard) : e ∈ 𝓜.edges := by
  rcases he with h | ⟨v, rfl, -⟩
  · exact h
  · rw [Set.ncard_singleton] at h2
    omega

end

end ErdosFaberLovaszConjecture
