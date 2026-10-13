import Mathlib
import Submission.Work.Wilkies.Defs

/-!
# The band count of a cylindrical cell

`WilkiesDesign.IsCell n κ` describes the cells of a cylindrical decomposition of `ℝⁿ`: the
cell is built up coordinate by coordinate, each step being either a *graph* step
(`z_last = f (init z)`) or a *band* step (`a (init z) < z_last < b (init z)`).

This file records the *number of band steps* of a cell as a predicate `CellBand n κ d`,
mirroring the `IsCell` constructors.  It is the combinatorial notion of "the dimension of a
cell" used in area H: the plan is

* `CellBand n κ d → IsCell n κ` (forget the count),
* `IsCell n κ → ∃ d, CellBand n κ d` (the count exists),
* `CellBand n κ d → DimLE κ d` (the dimension bound, BNZ: the number of band steps controls
  the dimension, because the graph steps add no freedom in the sense of `DimLE`).

The last statement is the one that fails for *arbitrary* continuous cells without any `Ω`
hypothesis (a band step followed by two graph steps can sweep out a square, the "Peano cell"),
and holds for `Ω`-cells by the level-set argument of BNZ §2.3.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign

/-- `CellBand n κ d`: `κ ⊆ ℝⁿ` is a cylindrical cell whose construction uses exactly `d` band
steps (the other steps being graph steps).  This mirrors `WilkiesDesign.IsCell` constructor by
constructor, with `d` counting the band steps. -/
inductive CellBand : (n : ℕ) → Set (Fin n → ℝ) → ℕ → Prop
  | zero : CellBand 0 Set.univ 0
  | graph {n : ℕ} {C : Set (Fin n → ℝ)} {d : ℕ} (hC : CellBand n C d)
      (f : (Fin n → ℝ) → ℝ) (hf : ContinuousOn f C) :
      CellBand (n + 1) {z | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} d
  | band {n : ℕ} {C : Set (Fin n → ℝ)} {d : ℕ} (hC : CellBand n C d)
      (a b : (Fin n → ℝ) → EReal) (ha : ContinuousOn a C) (hb : ContinuousOn b C)
      (hab : ∀ x ∈ C, a x < b x) :
      CellBand (n + 1) {z | Fin.init z ∈ C ∧ a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} (d + 1)

/-- `CellBand` implies `IsCell`. -/
theorem CellBand.isCell {n d : ℕ} {κ : Set (Fin n → ℝ)} (h : CellBand n κ d) :
    IsCell n κ := by
  induction h with
  | zero => exact IsCell.zero
  | graph hC f hf ih => exact IsCell.graph ih f hf
  | band hC a b ha hb hab ih => exact IsCell.band ih a b ha hb hab

/-- `IsCell` admits a band count. -/
theorem exists_cellBand_of_isCell : ∀ {n : ℕ} {κ : Set (Fin n → ℝ)}, IsCell n κ →
    ∃ d : ℕ, CellBand n κ d := by
  intro n κ h
  induction h with
  | zero => exact ⟨0, CellBand.zero⟩
  | graph hC f hf ih =>
      obtain ⟨d, hd⟩ := ih
      exact ⟨d, CellBand.graph hd f hf⟩
  | band hC a b ha hb hab ih =>
      obtain ⟨d, hd⟩ := ih
      exact ⟨d + 1, CellBand.band hd a b ha hb hab⟩

end Work.WilkiesH.Strat
