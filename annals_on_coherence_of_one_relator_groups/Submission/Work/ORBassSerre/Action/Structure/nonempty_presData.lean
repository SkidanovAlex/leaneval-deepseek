import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.BSPresentation
import Submission.Work.ORBassSerre.Action.Structure.TreeDatum

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure

open Quiver

/-!
# Existence of the presentation data of the fundamental domain

Given a `TreeDatum` `d` for a cocompact action of `G` on a graph `V` without inversions, if every
vertex stabiliser of `G` is finitely presented and every edge stabiliser is finitely generated,
then `d` admits presentation data `d.PresData`: a finite presentation of each vertex group
(a finite generating set together with a finite set of relators spanning the kernel) and a finite
generating family of each edge group.

This is a purely combinatorial extraction: `Group.IsFinitelyPresented` of a vertex group is
literally the data of a surjection `FreeGroup (Fin n) →* vgroup A` whose kernel is the normal
closure of a finite set, and `Group.FG` of an edge group is the data of a finite set generating
it, which we index by `Fin n` through `Finset.equivFinOfCardEq`.
-/

/-- A finitely generated group admits a finite generating family indexed by `Fin n`. -/
theorem exists_fin_gens_of_FG {H : Type*} [Group H] (h : Group.FG H) :
    ∃ (n : ℕ) (g : Fin n → H), Subgroup.closure (Set.range g) = ⊤ := by
  obtain ⟨n, S, hcard, hclos⟩ := Group.fg_iff'.mp h
  refine ⟨n, fun i => ((S.equivFinOfCardEq hcard).symm i : H), ?_⟩
  have hrange : Set.range (fun i : Fin n => ((S.equivFinOfCardEq hcard).symm i : H)) =
      (S : Set H) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((S.equivFinOfCardEq hcard).symm i).2
    · intro hx
      exact ⟨(S.equivFinOfCardEq hcard) ⟨x, hx⟩, by simp⟩
  rw [hrange, hclos]

/-- For a group action on a graph with finitely presented vertex stabilisers and finitely
generated edge stabilisers, the presentation datum of a spanning-tree (`TreeDatum`) exists. -/
theorem nonempty_presData {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    (d : Work.ORBassSerre.Action.Structure.TreeDatum G V)
    (hstab : ∀ v : V, Group.IsFinitelyPresented (MulAction.stabilizer G v))
    (hedge : ∀ e : Quiver.Total V, Group.FG (MulAction.stabilizer G e)) :
    Nonempty (d.PresData) := by
  classical
  -- A finite presentation of every vertex group: a surjection from a free group on finitely many
  -- generators whose kernel is the normal closure of finitely many relators.
  choose nV πV hπV using fun A => (hstab (d.vert A)).out
  choose RV hRV using fun A => (hπV A).2
  -- A finite generating family of every edge group.
  choose nE gensE hgensE using fun E => exists_fin_gens_of_FG (hedge (d.elift E))
  exact ⟨{ nV := nV, πV := πV, hπV := fun A => (hπV A).1, RV := RV,
           hRV := fun A => (hRV A),
           nE := nE, gensE := gensE, hgensE := hgensE }⟩

end Work.ORBassSerre.Action.Structure
