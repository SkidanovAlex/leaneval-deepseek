/-
  WilG1/Choice/PieceDefs — the four disjuncts of `selSet` and the symmetry sets of the
  auxiliary space `Fin (p+1+2)` used by the selection-membership proof.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.ChoiceDefs
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG1.Calc.le_mem
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG1.Choice.AffLast
import Submission.Work.WilG1.Choice.Helpers
import Submission.Work.WilG1.Choice.Blocks
import Submission.Work.WilG1.Choice.isAll_mem

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Choice

open WilkiesDesign WilkiesConjecture

/-! ## 1. The four disjuncts, as sets of `Fin (p+1) → ℝ` -/

/-- The fibre is all of `ℝ` and the selected value is `0`. -/
def selA {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  {z : Fin (p + 1) → ℝ | ∀ s : ℝ, Fin.snoc (Fin.init z) s ∈ K} ∩
    {z : Fin (p + 1) → ℝ | z (Fin.last p) = 0}

/-- The fibre is symmetric about the value, or about a unique centre. -/
def selB {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  {z : Fin (p + 1) → ℝ | ∀ s : ℝ,
      (Fin.snoc (Fin.init z) (z (Fin.last p) + s) ∈ K ↔
        Fin.snoc (Fin.init z) (z (Fin.last p) - s) ∈ K)} ∩
    {z : Fin (p + 1) → ℝ | ∃ c : ℝ,
      (∀ s : ℝ, (Fin.snoc (Fin.init z) (c + s) ∈ K ↔
        Fin.snoc (Fin.init z) (c - s) ∈ K)) ∧
      ∀ c' : ℝ, (∀ s : ℝ, (Fin.snoc (Fin.init z) (c' + s) ∈ K ↔
        Fin.snoc (Fin.init z) (c' - s) ∈ K)) → c' = c}

/-- The fibre is a half-line unbounded above, and the value is `inf + 1`. -/
def selC {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} ∩
    {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p) - 1) ∉ K} ∩
    {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
      Fin.snoc (Fin.init z) (z (Fin.last p) - 1 + s) ∈ K} ∩
    {z : Fin (p + 1) → ℝ | ∀ M : ℝ, ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ K ∧ M < s}

/-- The fibre is a half-line unbounded below, and the value is `sup - 1`. -/
def selD {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ K} ∩
    {z : Fin (p + 1) → ℝ | Fin.snoc (Fin.init z) (z (Fin.last p) + 1) ∉ K} ∩
    {z : Fin (p + 1) → ℝ | ∀ s : ℝ, 0 < s → s < 1 →
      Fin.snoc (Fin.init z) (z (Fin.last p) + 1 - s) ∈ K} ∩
    {z : Fin (p + 1) → ℝ | ∀ M : ℝ, ∃ s : ℝ, Fin.snoc (Fin.init z) s ∈ K ∧ s < M}

/-! ## 2. The three symmetry conditions attached to the coordinates of `Fin (p+1+2)` -/

/-- Symmetry of the fibre about the base value coordinate, in the space `Fin (p+1+2)`. -/
def ctrT2 {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1 + 2) → ℝ) :=
  {y | ∀ u : ℝ, (Fin.snoc (basePart y) (y (idxT p 2) + u) ∈ K ↔
    Fin.snoc (basePart y) (y (idxT p 2) - u) ∈ K)}

/-- Symmetry of the fibre about the first extra coordinate `c`. -/
def ctrE0 {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1 + 2) → ℝ) :=
  {y | ∀ u : ℝ, (Fin.snoc (basePart y) (y (idxE p 2 (0 : Fin 2)) + u) ∈ K ↔
    Fin.snoc (basePart y) (y (idxE p 2 (0 : Fin 2)) - u) ∈ K)}

/-- Symmetry of the fibre about the second extra coordinate `c'`. -/
def ctrE1 {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1 + 2) → ℝ) :=
  {y | ∀ u : ℝ, (Fin.snoc (basePart y) (y (idxE p 2 (1 : Fin 2)) + u) ∈ K ↔
    Fin.snoc (basePart y) (y (idxE p 2 (1 : Fin 2)) - u) ∈ K)}

/-- The relation `c' = c` between the two extra coordinates. -/
def eqE {p : ℕ} : Set (Fin (p + 1 + 2) → ℝ) :=
  {y | y (idxE p 2 (1 : Fin 2)) = y (idxE p 2 (0 : Fin 2))}


/-- Bound a sum whose first term is a `max` by bounding both branches. -/
theorem max_add_le {a b c T : ℕ} (ha : a + c ≤ T) (hb : b + c ≤ T) : max a b + c ≤ T := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

end Work.WilG1.Choice
