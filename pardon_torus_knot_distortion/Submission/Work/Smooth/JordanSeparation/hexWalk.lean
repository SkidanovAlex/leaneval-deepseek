import Mathlib

/-!
# The wall-following walk for the finite Hex duality

This file sets up the combinatorial machinery for the *hard direction* of the finite Hex
duality (`Work.Smooth.JordanSeparation.hex_rect_hard`): given a `W × H` grid of cells and a
predicate `blocked`, if there is **no** `8`-connected chain of blocked cells from the left
column to the right column, then there **is** a `4`-connected chain of free cells from the
bottom row to the top row.

The proof follows the boundary of the free region `A` (the union of the free `4`-components
touching the bottom row, together with a virtual free row just below the grid).  Walking along
this boundary with `A` on the left produces, on its right, a chain of blocked cells joining the
left and right columns.

## Coordinates

* `Cell := ℤ × ℤ` is a grid cell, `(i,j)` being the cell with corners `(i,j),(i+1,j),(i,j+1),(i+1,j+1)`.
* A "crack" is a directed unit segment between two adjacent integer lattice points; `lcell` and
  `rcell` are the cells on its left and on its right.

## The walk

`valid S p d` says the crack starting at lattice point `p` in direction `d` has its left cell in
`S` and its right cell not in `S`.  `nextD` is the "turn as far left as possible" rule, and
`step` is one step of the wall-following walk.  `walkN` iterates `step` from the starting crack
(below the bottom-left corner of the virtual free row).
-/

open Classical

namespace Work.Smooth.JordanSeparation

/-- The four axis directions. -/
inductive HDir where
  | E | N | W | S
  deriving DecidableEq

namespace HDir

/-- The displacement vector of a direction. -/
def vec : HDir → ℤ × ℤ
  | E => (1, 0) | N => (0, 1) | W => (-1, 0) | S => (0, -1)

/-- Rotation by 90° counterclockwise. -/
def rotL : HDir → HDir
  | E => N | N => W | W => S | S => E

/-- Rotation by 90° clockwise. -/
def rotR : HDir → HDir
  | E => S | N => E | W => N | S => W

/-- Reversal. -/
def opp : HDir → HDir
  | E => W | N => S | W => E | S => N

end HDir
open HDir

instance : Fintype HDir where
  elems := {HDir.E, HDir.N, HDir.W, HDir.S}
  complete := by intro x; cases x <;> simp

/-- A grid cell is a pair of integers (its lower-left corner). -/
abbrev Cell := ℤ × ℤ

/-- The cell on the **left** of the crack starting at lattice point `p` in direction `d`. -/
def lcell (p : Cell) : HDir → Cell
  | E => (p.1, p.2) | N => (p.1 - 1, p.2) | W => (p.1 - 1, p.2 - 1) | S => (p.1, p.2 - 1)
/-- The cell on the **right** of the crack starting at lattice point `p` in direction `d`. -/
def rcell (p : Cell) : HDir → Cell
  | E => (p.1, p.2 - 1) | N => (p.1, p.2) | W => (p.1 - 1, p.2) | S => (p.1 - 1, p.2 - 1)
/-- The endpoint of the crack starting at `p` in direction `d`. -/
def nxt (p : Cell) (d : HDir) : Cell := (p.1 + d.vec.1, p.2 + d.vec.2)

/-- The crack `(p,d)` has its left cell in `S` and its right cell outside `S`. -/
def valid (S : Cell → Prop) (p : Cell) (d : HDir) : Prop := S (lcell p d) ∧ ¬ S (rcell p d)

/-- The wall-following rule: turn as far left as possible. -/
noncomputable def nextD (S : Cell → Prop) (B : Cell) (d : HDir) : HDir :=
  if valid S B (rotL d) then rotL d else if valid S B d then d else rotR d

/-- One step of the walk. -/
noncomputable def step (S : Cell → Prop) (s : Cell × HDir) : Cell × HDir :=
  (nxt s.1 s.2, nextD S (nxt s.1 s.2) s.2)

lemma nextD_eq_rotL (S : Cell → Prop) (B : Cell) (d : HDir) (h : valid S B (rotL d)) :
    nextD S B d = rotL d := by simp only [nextD]; rw [if_pos h]

lemma nextD_eq_self (S : Cell → Prop) (B : Cell) (d : HDir)
    (h1 : ¬ valid S B (rotL d)) (h : valid S B d) : nextD S B d = d := by
  simp only [nextD]; rw [if_neg h1, if_pos h]

lemma nextD_eq_rotR (S : Cell → Prop) (B : Cell) (d : HDir)
    (h1 : ¬ valid S B (rotL d)) (h2 : ¬ valid S B d) : nextD S B d = rotR d := by
  simp only [nextD]; rw [if_neg h1, if_neg h2]

/-- **The walk never gets stuck**: a valid crack is followed by a valid crack. -/
lemma valid_step (S : Cell → Prop) (p : Cell) (d : HDir) (h : valid S p d) :
    valid S (nxt p d) (nextD S (nxt p d) d) := by
  rcases Classical.em (valid S (nxt p d) (rotL d)) with h1 | h1
  · rw [nextD_eq_rotL S _ _ h1]; exact h1
  · rcases Classical.em (valid S (nxt p d) d) with h2 | h2
    · rw [nextD_eq_self S _ _ h1 h2]; exact h2
    · rw [nextD_eq_rotR S _ _ h1 h2]
      cases d <;>
        simp only [valid, lcell, rcell, nxt, vec, HDir.rotL, HDir.rotR] at h h1 h2 ⊢ <;>
        (try ring_nf at h h1 h2 ⊢) <;> tauto

/-- **The step map is injective on valid cracks** (the wall trail never visits a directed crack
twice). -/
lemma step_inj (S : Cell → Prop) (p : Cell) (d : HDir) (p' : Cell) (d' : HDir)
    (h : valid S p d) (h' : valid S p' d')
    (heq : step S (p, d) = step S (p', d')) : (p, d) = (p', d') := by
  have hB : nxt p d = nxt p' d' := by
    have := congrArg Prod.fst heq; simpa only [step] using this
  have hnd : nextD S (nxt p d) d = nextD S (nxt p d) d' := by
    have := congrArg Prod.snd heq
    simp only [step] at this
    rw [← hB] at this
    exact this
  have hdd : d = d' := by
    have hpp : p = (p'.1 + ((HDir.vec d').1 - (HDir.vec d).1),
                    p'.2 + ((HDir.vec d').2 - (HDir.vec d).2)) := by
      have h1 := hB; simp only [nxt, Prod.mk.injEq] at h1
      exact Prod.ext (by omega) (by omega)
    subst hpp
    cases d <;> cases d' <;>
      simp only [valid, nextD, lcell, rcell, nxt, HDir.vec, HDir.rotL, HDir.rotR,
        Prod.mk.injEq] at * <;>
      (try (split_ifs at *)) <;> (try (ring_nf at *)) <;> simp_all
  subst hdd
  have hpp : p = p' := by
    have h1 := congrArg (fun c : Cell => (c.1 - (HDir.vec d).1, c.2 - (HDir.vec d).2)) hB
    simp only [nxt, Prod.mk.injEq] at h1
    exact Prod.ext (by omega) (by omega)
  exact Prod.ext hpp rfl

end Work.Smooth.JordanSeparation
