/-
# Structural facts about paths in the Bass--Serre tree of a free product

This file proves the structural part of the invariant of a path in the Bass--Serre tree of a free
product (see `Submission.Work.ORLocInd.CoprodTree.StarTreePath`).  Unlike the fields of `Inv`,
which require the path to be reduced, the facts collected here hold for an *arbitrary* path:
the endpoint of a path from `vtx k g` is determined by the parity of its length and by its state,
the product of its letters is the total change of state, each letter lies in the factor of its
index, and if the endpoint is a central vertex then the last letter is the step of the last arrow.

The proof is a single induction on the path; the only input is the local shape of an arrow
(`arrow_none_left`, `arrow_some_left`).
-/
import Mathlib
import Submission.Work.ORLocInd.CoprodTree.StarTreePath

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.CoprodTree

open Quiver
open Work.ORBassSerre
open Classical

variable {ι : Type u}

/-! ## Helper facts about arrows starting at a given vertex -/

/-- An arrow whose source is a leaf vertex `vtx (some i) g` starts in the `i`-th factor and ends at
the central vertex of its label. -/
private theorem arrow_some_left_of_eq {M : ι → Type u} [∀ i, Group (M i)]
    {x y : Vertex M} {i : ι} {g : Monoid.CoprodI M} (e : x ⟶ y)
    (hx : x = vtx (some i) g) :
    e.idx = i ∧ (∃ m : M i, e.lbl = g * Monoid.CoprodI.of m) ∧ y = vtx none e.lbl := by
  subst hx
  exact arrow_some_left e

/-- An arrow whose source is a central vertex `vtx none g` keeps the same label and ends at a leaf
vertex. -/
private theorem arrow_none_left_of_eq {M : ι → Type u} [∀ i, Group (M i)]
    {x y : Vertex M} {g : Monoid.CoprodI M} (e : x ⟶ y) (hx : x = vtx none g) :
    e.lbl = g ∧ y = vtx (some e.idx) e.lbl := by
  subst hx
  exact arrow_none_left e

/-! ## The structural statement -/

/-- The structural facts about an arbitrary path in the tree, bundled together so that they can be
proved by a single induction. -/
def InvS {M : ι → Type u} [∀ i, Group (M i)] (k : Option ι) (g : Monoid.CoprodI M)
    {y : Vertex M} (p : Quiver.Path (vtx k g) y) : Prop :=
  (isLeafSide k p.length = true →
      (∃ i, y = vtx (some i) (stt k g p)) ∧
      (∀ i, lidx k g p = some i → y = vtx (some i) (stt k g p))) ∧
    (isLeafSide k p.length = false → y = vtx none (stt k g p)) ∧
    ((letters k g p).map (fun x => x.2)).prod = g⁻¹ * stt k g p ∧
    (∀ x ∈ letters k g p, x.2 ∈ factor M x.1) ∧
    (isLeafSide k p.length = false → llidx k g p = lidx k g p)

/-- Every path satisfies the structural facts. -/
theorem invS_of_path {M : ι → Type u} [∀ i, Group (M i)] {k : Option ι}
    {g : Monoid.CoprodI M} :
    ∀ {y : Vertex M} (p : Quiver.Path (vtx k g) y), InvS k g p := by
  intro y p
  induction p with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h
      cases k with
      | none => exact Bool.noConfusion h
      | some i => exact ⟨⟨i, rfl⟩, fun i' hi => by
          rw [lidx_nil] at hi
          exact absurd hi.symm (Option.some_ne_none i')⟩
    · intro h
      cases k with
      | none => rfl
      | some i => exact Bool.noConfusion h
    · simp
    · intro x hx; simp at hx
    · intro _; rfl
  | cons p e ih =>
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih
    by_cases hb : isLeafSide k p.length = true
    · -- the source of `e` is a leaf vertex
      obtain ⟨i0, hi0⟩ := (ih1 hb).1
      obtain ⟨hidx, ⟨m, hmlbl⟩, hy⟩ := arrow_some_left_of_eq e hi0
      have hside : isLeafSide k (p.cons e).length = false := by
        rw [Quiver.Path.length_cons, isLeafSide_succ, hb]; rfl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h; rw [hside] at h; exact Bool.noConfusion h
      · intro _; rw [stt_cons]; exact hy
      · rw [letters_cons, dif_pos hb, List.map_append, List.prod_append, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, ih3, stt_cons]
        group
      · intro z hz
        rw [letters_cons, dif_pos hb, List.mem_append] at hz
        rcases hz with hz | hz
        · exact ih4 z hz
        · simp only [List.mem_singleton] at hz
          subst hz
          rw [hidx, hmlbl, ← mul_assoc, inv_mul_cancel, one_mul]
          exact mem_factor.mpr ⟨m, rfl⟩
      · intro _; rw [llidx_cons, dif_pos hb, lidx_cons]
    · -- the source of `e` is a central vertex
      have hbf : isLeafSide k p.length = false := by
        cases hh : isLeafSide k p.length <;> simp_all
      obtain ⟨hlbl, hy⟩ := arrow_none_left_of_eq e (ih2 hbf)
      have hside : isLeafSide k (p.cons e).length = true := by
        rw [Quiver.Path.length_cons, isLeafSide_succ, hbf]; rfl
      have hlet : letters k g (p.cons e) = letters k g p := by
        rw [letters_cons, dif_neg hb, List.append_nil]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro _
        refine ⟨⟨e.idx, ?_⟩, ?_⟩
        · rw [stt_cons]; exact hy
        · intro i hi
          rw [lidx_cons] at hi
          rw [Option.some.injEq] at hi
          rw [stt_cons, ← hi]; exact hy
      · intro h; rw [hside] at h; exact Bool.noConfusion h
      · rw [hlet, ih3, stt_cons, hlbl]
      · intro z hz; rw [hlet] at hz; exact ih4 z hz
      · intro h; rw [hside] at h; exact Bool.noConfusion h

theorem inv_structural {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)] {k : Option ι}
    {g : Monoid.CoprodI M} {y : Vertex M} (p : Quiver.Path (vtx k g) y) :
    (isLeafSide k p.length = true →
        (∃ i, y = vtx (some i) (stt k g p)) ∧
        (∀ i, lidx k g p = some i → y = vtx (some i) (stt k g p))) ∧
      (isLeafSide k p.length = false → y = vtx none (stt k g p)) ∧
      ((letters k g p).map (fun x => x.2)).prod = g⁻¹ * stt k g p ∧
      (∀ x ∈ letters k g p, x.2 ∈ factor M x.1) ∧
      (isLeafSide k p.length = false → llidx k g p = lidx k g p) :=
  invS_of_path p

end Work.ORLocInd.CoprodTree
