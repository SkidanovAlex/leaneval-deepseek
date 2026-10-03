/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Cocompactness of a tree action and finite transversals

For a group `G` acting on a set `V`, the orbit quotient `MulAction.orbitRel.Quotient G V`
is finite if and only if there is a finite set `s : Finset V` meeting every orbit
(the two helper lemmas `finite_orbitQuotient_iff_exists_finset` below).

Applying this to the vertices of a `GTree G V` and to its oriented edges
(`T.AdjPair`, with the induced `G`-action) gives the characterisation of
`T.IsCocompact` used throughout the project: `G` has finitely many orbits of vertices
and of edges exactly when one can pick finitely many vertices meeting every vertex orbit
and finitely many oriented edges meeting every edge orbit.

The only point in the edge part needing care is that the finite set of the statement
is a `Finset (V × V)` (an arbitrary finite set of *pairs*), so when passing from the
transversal to the finiteness of the orbit quotient of `T.AdjPair` one must restrict it
to the adjacent pairs (`Finset.filter`), and conversely when producing a transversal
from finiteness of the orbit quotient one takes the underlying pairs of a set of
representatives of the edge orbits.
-/
import Mathlib
import Submission.Work.ORDunwoody.Basic

set_option autoImplicit false

set_option linter.style.haveILetI false

namespace Work.ORDunwoody.Lemmas

open Work.ORDunwoody

/-! ## Finite transversals and finite orbit quotients -/

section Transversal

variable {G : Type*} [Group G] {V : Type*} [MulAction G V]

/-- A finite set of vertices meeting every orbit gives finitely many orbits. -/
theorem finite_orbitQuotient_of_exists_finset (s : Finset V)
    (hs : ∀ v : V, ∃ g : G, g • v ∈ s) :
    Finite (MulAction.orbitRel.Quotient G V) := by
  classical
  haveI : Finite s := s.finite_toSet.to_subtype
  refine Finite.of_surjective
    (fun x : s => (Quotient.mk (MulAction.orbitRel G V) (x : V) :
      MulAction.orbitRel.Quotient G V)) ?_
  intro q
  refine Quotient.inductionOn q (fun v => ?_)
  obtain ⟨g, hg⟩ := hs v
  refine ⟨⟨g • v, hg⟩, ?_⟩
  apply Quotient.sound
  show (MulAction.orbitRel G V) (g • v) v
  rw [MulAction.orbitRel_apply]
  exact MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩

/-- Finitely many orbits admit a finite set of representatives meeting every orbit. -/
theorem exists_finset_of_finite_orbitQuotient
    [Finite (MulAction.orbitRel.Quotient G V)] :
    ∃ s : Finset V, ∀ v : V, ∃ g : G, g • v ∈ s := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient G V) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : MulAction.orbitRel.Quotient G V => Quotient.out q),
    fun v => ?_⟩
  have hmem : Quotient.out (Quotient.mk (MulAction.orbitRel G V) v) ∈
      Finset.univ.image (fun q : MulAction.orbitRel.Quotient G V => Quotient.out q) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  obtain ⟨g, hg⟩ : ∃ g : G, g • v =
      Quotient.out (Quotient.mk (MulAction.orbitRel G V) v) := by
    have hrel : (MulAction.orbitRel G V)
        (Quotient.out (Quotient.mk (MulAction.orbitRel G V) v)) v :=
      Quotient.exact (Quotient.out_eq _)
    exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
  exact ⟨g, by rw [hg]; exact hmem⟩

/-- **Characterisation of finiteness of the orbit quotient** by the existence of a
finite transversal. -/
theorem finite_orbitQuotient_iff_exists_finset :
    Finite (MulAction.orbitRel.Quotient G V) ↔
      ∃ s : Finset V, ∀ v : V, ∃ g : G, g • v ∈ s :=
  ⟨fun _ => exists_finset_of_finite_orbitQuotient,
   fun ⟨s, hs⟩ => finite_orbitQuotient_of_exists_finset s hs⟩

end Transversal

/-! ## The tree statement -/

/-- **Cocompactness is equivalent to the existence of finite vertex and edge
transversals.**  The action of `G` on the tree `T` has finitely many orbits of vertices
and of edges iff there is a finite set of vertices meeting every vertex orbit and a
finite set of oriented edges (pairs of adjacent vertices), meeting every edge orbit. -/
theorem isCocompact_iff_transversal {G : Type*} [Group G] {V : Type*} [MulAction G V]
    (T : GTree G V) :
    T.IsCocompact ↔
      (∃ s : Finset V, ∀ v : V, ∃ g : G, g • v ∈ s) ∧
      (∃ s : Finset (V × V), ∀ p : V × V, T.Adj p.1 p.2 →
        ∃ g : G, (g • p.1, g • p.2) ∈ s) := by
  classical
  constructor
  · -- Cocompactness gives finite vertex and edge transversals.
    intro h
    obtain ⟨hV, hE⟩ := h
    haveI : Fintype (MulAction.orbitRel.Quotient G V) := Fintype.ofFinite _
    haveI : Fintype (MulAction.orbitRel.Quotient G T.AdjPair) := Fintype.ofFinite _
    refine ⟨exists_finset_of_finite_orbitQuotient, ?_⟩
    -- edge transversal: underlying pairs of a set of representatives of the edge orbits
    refine ⟨Finset.univ.image (fun q : MulAction.orbitRel.Quotient G T.AdjPair =>
        ((Quotient.out q : T.AdjPair) : V × V)), fun p hp => ?_⟩
    obtain ⟨g, hg⟩ : ∃ g : G, g • (⟨p, hp⟩ : T.AdjPair) =
        Quotient.out (Quotient.mk (MulAction.orbitRel G T.AdjPair)
          (⟨p, hp⟩ : T.AdjPair)) := by
      have hrel : (MulAction.orbitRel G T.AdjPair)
          (Quotient.out (Quotient.mk (MulAction.orbitRel G T.AdjPair)
            (⟨p, hp⟩ : T.AdjPair))) (⟨p, hp⟩ : T.AdjPair) :=
        Quotient.exact (Quotient.out_eq _)
      exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
    refine ⟨g, ?_⟩
    have hcoe : (g • p.1, g • p.2) = ((Quotient.out (Quotient.mk
        (MulAction.orbitRel G T.AdjPair) (⟨p, hp⟩ : T.AdjPair)) : T.AdjPair) : V × V) := by
      rw [← hg]; rfl
    rw [hcoe]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · -- Finite transversals give finitely many orbits.
    rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    refine ⟨finite_orbitQuotient_of_exists_finset s hs, ?_⟩
    -- only the adjacent pairs of `t` are relevant, and they are finitely many
    haveI : Finite {q : V × V // q ∈ t.filter (fun q => T.Adj q.1 q.2)} :=
      (t.filter (fun q => T.Adj q.1 q.2)).finite_toSet.to_subtype
    refine Finite.of_surjective
      (fun x : {q : V × V // q ∈ t.filter (fun q => T.Adj q.1 q.2)} =>
        (Quotient.mk (MulAction.orbitRel G T.AdjPair)
          (⟨x.1, (Finset.mem_filter.mp x.2).2⟩ : T.AdjPair) :
          MulAction.orbitRel.Quotient G T.AdjPair)) ?_
    intro q
    refine Quotient.inductionOn q (fun p => ?_)
    obtain ⟨g, hg⟩ := ht (p : V × V) p.2
    refine ⟨⟨(g • (p : V × V).1, g • (p : V × V).2),
      Finset.mem_filter.mpr ⟨hg, T.smul_adj g p.2⟩⟩, ?_⟩
    apply Quotient.sound
    show (MulAction.orbitRel G T.AdjPair)
      (⟨(g • (p : V × V).1, g • (p : V × V).2), T.smul_adj g p.2⟩ : T.AdjPair) p
    rw [MulAction.orbitRel_apply]
    exact MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩

end Work.ORDunwoody.Lemmas
