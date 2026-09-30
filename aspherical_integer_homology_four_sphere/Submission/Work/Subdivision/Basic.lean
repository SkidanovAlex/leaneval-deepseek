/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Polyhedral CW complexes and their subdivision

This file sets up the combinatorial substrate of the area `Work.Subdivision`:

* `PolyCW` — a finite polyhedral CW complex, presented as the **poset of its cells**
  graded by dimension.  This is the presentation in which all the algebra
  (cellular chains, the barycentric subdivision, its skeletal filtration) is
  naturally stated.  A cell `e` is a *face* of a cell `g` when `e ≤ g`; the
  dimension function `dim` is strictly increasing along strict comparisons.

  Compared with a "cellular atlas" presentation (one abstract face lattice per
  cell, plus a character map to cells and restriction order isomorphisms), the
  poset presentation needs no bookkeeping of identifications: the face lattice
  of `e` *is* the interval `Iic e`, whatever ambient cell `e` is viewed in.

* Incidence numbers `inc e f : ℤ` for `f ⋖ e` (codimension one), with the
  cocycle condition `HasDdZero` isolated as a hypothesis (the data supplier
  checks it; the algebra only needs it as a hypothesis, exactly as in the
  blueprint).

## Conventions

* `P.dim e` is the dimension of the cell `e`; `P.facets e` are the cells
  `f < e` with `P.dim f + 1 = P.dim e`.
* `P.faces k` is the set of cells of dimension `k`.
* `P.IsLower S` says `S` is closed downwards, i.e. a union of cells.
-/

namespace Work.Subdivision

universe u

/-- A finite **polyhedral CW complex**: a finite poset of cells, graded by
dimension, together with a (total, mostly junk) table of incidence numbers.

Fields `fintype`, `decEq`, `partialOrder`, `decLe` are instance fields. -/
structure PolyCW where
  /-- The type of cells. -/
  Cell : Type u
  [fintype : Fintype Cell]
  [decEq : DecidableEq Cell]
  [partialOrder : PartialOrder Cell]
  [decLe : DecidableRel (· ≤ · : Cell → Cell → Prop)]
  [decLt : DecidableRel (· < · : Cell → Cell → Prop)]
  /-- Dimension of a cell. -/
  dim : Cell → ℕ
  /-- Dimension is monotone for the face relation. -/
  dim_le : ∀ {a b : Cell}, a ≤ b → dim a ≤ dim b
  /-- Dimension strictly increases along strict comparisons. -/
  dim_lt : ∀ {a b : Cell}, a ≤ b → a ≠ b → dim a < dim b
  /-- Incidence numbers of codimension one faces; `inc e f` is only meaningful
  (and only ever used) when `f ⋖ e`. -/
  inc : Cell → Cell → ℤ

attribute [instance] PolyCW.fintype PolyCW.decEq PolyCW.partialOrder PolyCW.decLe PolyCW.decLt

namespace PolyCW

variable (P : PolyCW.{u})

instance : Fintype P.Cell := P.fintype
instance : DecidableEq P.Cell := P.decEq
instance : PartialOrder P.Cell := P.partialOrder
instance : DecidableRel (· ≤ · : P.Cell → P.Cell → Prop) := P.decLe
instance : DecidableRel (· < · : P.Cell → P.Cell → Prop) := P.decLt

theorem dim_lt' {a b : P.Cell} (h : a < b) : P.dim a < P.dim b :=
  P.dim_lt h.le (ne_of_lt h)

theorem dim_le_of_le' {a b : P.Cell} (h : a ≤ b) : P.dim a ≤ P.dim b := P.dim_le h

/-- The facets of a cell `e`: the cells `f` with `f ⋖ e`. -/
def facets (e : P.Cell) : Finset P.Cell :=
  Finset.univ.filter (fun f => f < e ∧ P.dim e = P.dim f + 1)

@[simp] theorem mem_facets (e f : P.Cell) :
    f ∈ P.facets e ↔ f < e ∧ P.dim e = P.dim f + 1 := by
  simp [facets]

theorem facet_lt {e f : P.Cell} (h : f ∈ P.facets e) : f < e := ((P.mem_facets e f).1 h).1

theorem dim_facet {e f : P.Cell} (h : f ∈ P.facets e) : P.dim f + 1 = P.dim e :=
  ((P.mem_facets e f).1 h).2.symm

/-- The cells of a given dimension. -/
def faces (k : ℕ) : Finset P.Cell := Finset.univ.filter (fun e => P.dim e = k)

@[simp] theorem mem_faces (k : ℕ) (e : P.Cell) : e ∈ P.faces k ↔ P.dim e = k := by
  simp [faces]

/-- An upper bound for the dimensions, `max` over all cells. -/
def maxDim : ℕ := Finset.univ.sup P.dim

theorem dim_le_maxDim (e : P.Cell) : P.dim e ≤ P.maxDim := Finset.le_sup (Finset.mem_univ e)

/-- A subset of cells is **lower** (a union of cells) if it is closed under taking faces. -/
def IsLower (S : Set P.Cell) : Prop := ∀ ⦃f e : P.Cell⦄, f ≤ e → e ∈ S → f ∈ S

theorem isLower_of_dim_le (n : ℕ) : P.IsLower {e | P.dim e ≤ n} :=
  fun _ _ hfe he => le_trans (P.dim_le hfe) he

theorem isLower_iic (e : P.Cell) : P.IsLower (Set.Iic e) := fun _ _ h h' => le_trans h h'

theorem isLower_iio (e : P.Cell) : P.IsLower (Set.Iio e) := fun _ _ h h' => lt_of_le_of_lt h h'

end PolyCW

end Work.Subdivision
