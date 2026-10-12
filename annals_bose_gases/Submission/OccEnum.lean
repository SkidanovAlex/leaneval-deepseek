import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import ChallengeDeps
import Submission.BracketCount
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Order-preserving enumeration of the occupied set of a cell

For an assignment `a : Assign m N` and a cell `j`, the *occupied set*

    occSet a j := {i : Fin N | a i = j}      (cardinality `cellCount a j`)

lists exactly the particles assigned to cell `j`.  This module records the
order-preserving bijection between `Fin (cellCount a j)` and `occSet a j`
(via `Finset.orderIsoOfFin`), together with the elementary structural facts:

  * `occSet` / `occSet_card` — the occupied set and its cardinality;
  * `occEquiv` — the order-preserving bijection
    `Fin (cellCount a j) ≃o occSet a j`;
  * `occEquiv_mem` — every enumerated particle is assigned to `j`;
  * `occEquiv_strictMono` — the enumeration is increasing in the particle
    index;
  * `occSet_disjoint` — occupied sets of distinct cells are disjoint;
  * `occSet_biUnion` — the occupied sets cover all particles.

These give the per-cell coordinate identification used by the single-cell
slice bracket: the positions of the `cellCount a j` particles of cell `j` are a
configuration in `X (cellCount a j)` via `occEquiv`; the full `N`-particle
coordinate space splits (up to particle relabelling, which is harmless because
the Hamiltonian is permutation invariant) into the occupied blocks of the
cells.
-/

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The set of particles assigned to the cell `j`. -/
def occSet {m N : ℕ} (a : Assign m N) (j : CellIdx m) : Finset (Fin N) :=
  Finset.univ.filter (fun i : Fin N => a i = j)

/-- The cardinality of the occupied set is the occupation number. -/
lemma occSet_card {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    (occSet a j).card = cellCount a j := by
  rfl

/-- The order-preserving bijection between `Fin (cellCount a j)` and the
particles assigned to cell `j`. -/
noncomputable def occEquiv {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    Fin (cellCount a j) ≃o {i : Fin N // i ∈ occSet a j} :=
  Finset.orderIsoOfFin (occSet a j) (occSet_card a j)

/-- Every enumerated particle is assigned to the cell. -/
lemma occEquiv_mem {m N : ℕ} (a : Assign m N) (j : CellIdx m) (t : Fin (cellCount a j)) :
    a (((occEquiv a j) t : {i : Fin N // i ∈ occSet a j}) : Fin N) = j := by
  classical
  have hx := (occEquiv a j t).property
  change ((occEquiv a j t : {i : Fin N // i ∈ occSet a j}) : Fin N) ∈
      (Finset.univ.filter (fun i : Fin N => a i = j)) at hx
  rw [Finset.mem_filter] at hx
  exact hx.2

/-- The enumeration is strictly increasing in the particle index. -/
lemma occEquiv_strictMono {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    {t₁ t₂ : Fin (cellCount a j)} (ht : t₁ < t₂) :
    (((occEquiv a j) t₁ : {i : Fin N // i ∈ occSet a j}) : Fin N).val <
      (((occEquiv a j) t₂ : {i : Fin N // i ∈ occSet a j}) : Fin N).val := by
  change (occEquiv a j) t₁ < (occEquiv a j) t₂
  exact (occEquiv a j).strictMono ht

/-- Occupied sets of distinct cells are disjoint. -/
lemma occSet_disjoint {m N : ℕ} (a : Assign m N) {j₁ j₂ : CellIdx m} (hj : j₁ ≠ j₂) :
    Disjoint (occSet a j₁) (occSet a j₂) := by
  rw [Finset.disjoint_left]
  intro i hi₁
  have h₁ : a i = j₁ := by simpa [occSet] using hi₁
  intro hi₂
  have h₂ : a i = j₂ := by simpa [occSet] using hi₂
  exact hj (h₁.symm.trans h₂)

/-- The occupied sets cover all particles: the cardinalities sum to `N`. -/
lemma occSet_biUnion {m N : ℕ} (a : Assign m N) :
    (∑ j : CellIdx m, (occSet a j).card) = N := by
  calc
    (∑ j : CellIdx m, (occSet a j).card) = ∑ j : CellIdx m, cellCount a j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact occSet_card a j
    _ = N := by
      exact cellCount_sum a

end BoseGases

end Submission
