import Submission.Work.Wilkies.Defs

/-!
# Area H (counting) — dimensions of cells

The inductive description of cells (`WilkiesDesign.IsCell`) does not come with a
dimension.  For the counting argument we need one: the base case of the
dimension induction counts the points of a definable set of dimension `0`, and
for that we must know that a cell which is contained in a set of dimension `0`
is a singleton.

This file introduces the inductive predicate `CellDimLE n C k` — "the cell `C`
has dimension at most `k`" — with the same construction as `IsCell`: the
base cell `Set.univ ⊆ ℝ⁰` has dimension `0`, `graph` cells have the dimension
of their base, and `band` cells have the dimension of their base plus one.
-/

set_option autoImplicit false
noncomputable section

open Classical

namespace Work.WilkiesH

open WilkiesDesign WilkiesConjecture

/-- `CellDimLE n C k` says that the cell `C ⊆ ℝⁿ` has dimension at most `k`.
It is the dimension bookkeeping mirror of `WilkiesDesign.IsCell`: `graph` cells
inherit the dimension of their base, `band` cells add one. -/
inductive CellDimLE : (n : ℕ) → Set (Fin n → ℝ) → ℕ → Prop
  | zero : CellDimLE 0 Set.univ 0
  | graph {n : ℕ} {C : Set (Fin n → ℝ)} {k : ℕ} (hC : CellDimLE n C k)
      (f : (Fin n → ℝ) → ℝ) (hf : ContinuousOn f C) :
      CellDimLE (n + 1) {z | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} k
  | band {n : ℕ} {C : Set (Fin n → ℝ)} {k : ℕ} (hC : CellDimLE n C k)
      (a b : (Fin n → ℝ) → EReal) (ha : ContinuousOn a C) (hb : ContinuousOn b C)
      (hab : ∀ x ∈ C, a x < b x) :
      CellDimLE (n + 1)
        {z | Fin.init z ∈ C ∧ a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
          ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} (k + 1)
  /-- `CellDimLE` is monotone in the dimension bound, matching `DimLE`.  Without
  this constructor the predicate is *not* monotone in `k` (the `zero`
  constructor pins `k = 0`), and the main lemma relating it to `DimLE` fails. -/
  | mono {n : ℕ} {C : Set (Fin n → ℝ)} {k k' : ℕ} (hC : CellDimLE n C k) (h : k ≤ k') :
      CellDimLE n C k'

end Work.WilkiesH
