/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Brown
-/
import Mathlib
import Submission.Work.PL.Defs

/-!
# Brown's monotone union theorem: definitions

This file sets up the vocabulary for Morton Brown's theorem

> *The monotone union of open `n`-cells is an open `n`-cell*
> (M. Brown, Proc. Amer. Math. Soc. **12** (1961), 812–814),

in the form needed by the engulfing proof of the generalized Poincaré conjecture in
dimensions `≥ 5`: if a topological space is the union of an increasing sequence of open
subsets each homeomorphic to `ℝⁿ`, then the whole space is homeomorphic to `ℝⁿ`.

The shared vocabulary of the project (`PL.E`, `PL.IsOpenCell`, `PL.CellCover`, …) lives in
`Submission/Work/PL/Defs.lean` and is *frozen*; the definitions below are stated in terms of
it (or are genuinely new: `IsClosedCell`, `IsCellular`, `IsNearHomeo`).

## Main definitions

* `Work.Brown.IsOpenCell n U` — abbreviation for the frozen `PL.IsOpenCell`.
* `Work.Brown.IsClosedCell n K` — `K` is a closed `n`-cell.
* `Work.Brown.IsCellular n K` — `K` is a cellular subset: the intersection of a decreasing
  sequence of closed `n`-cells, each in the interior of the previous one.
* `Work.Brown.MonotoneOpenCellCover n U` — an increasing sequence of open `n`-cells covering
  the whole space.
* `Work.Brown.IsNearHomeo f` — quantitative near homeomorphism: `f` is a uniform limit of
  homeomorphisms.

The target `ℝⁿ` and sphere `𝕊ⁿ` are always `PL.E n = EuclideanSpace ℝ (Fin n)` and
`sphere (0 : PL.E (n+1)) 1` (`Metric.sphere`), matching the challenge statement.
-/

open Set Metric Function

namespace Work.Brown

/-! ### Cells -/

/-- An **open `n`-cell**: an open subset homeomorphic to `ℝⁿ`.  This is the frozen notion
`PL.IsOpenCell`; the abbreviation here just re-exports it into the `Work.Brown` namespace. -/
abbrev IsOpenCell (n : ℕ) {X : Type*} [TopologicalSpace X] (U : Set X) : Prop :=
  PL.IsOpenCell n U

/-- A **closed `n`-cell**: a closed subset homeomorphic to the closed unit ball of `ℝⁿ`. -/
def IsClosedCell (n : ℕ) {X : Type*} [TopologicalSpace X] (K : Set X) : Prop :=
  IsClosed K ∧ Nonempty (↥K ≃ₜ closedBall (0 : PL.E n) 1)

/-- A closed subset `K` of a space is **cellular** if it is the intersection of a decreasing
sequence `B : ℕ → Set X` of closed `n`-cells, each contained in the interior of the previous one.
For compact subsets of `𝕊ⁿ` this is equivalent to `𝕊ⁿ / K ≅ 𝕊ⁿ`, equivalently to `K` having a
neighbourhood basis of open `n`-cells; see `Work.Brown.Cellular`. -/
def IsCellular (n : ℕ) {X : Type*} [TopologicalSpace X] (K : Set X) : Prop :=
  ∃ B : ℕ → Set X, (∀ k, IsClosedCell n (B k)) ∧ (∀ k, K ⊆ interior (B k)) ∧ Antitone B ∧
    (⋂ k, B k) = K

/-! ### Monotone unions of open cells -/

/-- An increasing sequence of open `n`-cells whose union is the whole space.  This is the
hypothesis of Brown's monotone union theorem. -/
def MonotoneOpenCellCover (n : ℕ) {X : Type*} [TopologicalSpace X] (U : ℕ → Set X) : Prop :=
  (∀ k, IsOpen (U k)) ∧ Monotone U ∧ (∀ k, IsOpenCell n (U k)) ∧ (⋃ k, U k) = Set.univ

/-! ### Near homeomorphisms -/

/-- A map between (pseudo)metric spaces is a **near homeomorphism** if it is a uniform limit of
homeomorphisms.  This is the quantitative form of the notion used by Morton Brown in
*Some applications of an approximation theorem for inverse limits*, and it is the form in which
Bing's shrinking criterion is applied. -/
def IsNearHomeo {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : X → Y) : Prop :=
  ∀ ε > 0, ∃ h : X ≃ₜ Y, ∀ x, dist (h x) (f x) < ε

/-! ### Basic API -/

section Basic

variable {X : Type*} [TopologicalSpace X]

theorem isOpenCell_iff (n : ℕ) (U : Set X) :
    IsOpenCell n U ↔ IsOpen U ∧ Nonempty (↥U ≃ₜ PL.E n) := Iff.rfl

theorem IsOpenCell.isOpen {n : ℕ} {U : Set X} (h : IsOpenCell n U) : IsOpen U := h.1

theorem IsOpenCell.nonempty {n : ℕ} {U : Set X} (h : IsOpenCell n U) : U.Nonempty := by
  obtain ⟨e⟩ := h.2
  exact ⟨(e.symm 0 : ↥U), (e.symm 0 : ↥U).2⟩

theorem IsOpenCell.isConnected {n : ℕ} {U : Set X} (h : IsOpenCell n U) : IsConnected U := by
  obtain ⟨e⟩ := h.2
  have hU : U = range fun y : PL.E n => ((e.symm y : ↥U) : X) := by
    ext x
    constructor
    · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩
    · rintro ⟨y, rfl⟩; exact (e.symm y).2
  rw [hU]
  exact isConnected_range (continuous_subtype_val.comp e.symm.continuous)

end Basic

end Work.Brown
