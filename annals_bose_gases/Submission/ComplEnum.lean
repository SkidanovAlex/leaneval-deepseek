import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import ChallengeDeps
import Submission.Slice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Order-preserving enumeration of the complement of a cell's occupied set

For an assignment `a : Assign m N` and a cell `j`, the *complement* of the
occupied set

    occCompl a j := (occSet a j)ᶜ = {i : Fin N | a i ≠ j}

lists the particles NOT assigned to cell `j` (there are `N − cellCount a j` of
them).  This module records the order-preserving bijection between
`Fin (N − cellCount a j)` and `occCompl a j`, and the basic structural facts:

  * `occCompl` / `occCompl_card`;
  * `complEquiv` — `Fin (N − cellCount a j) ≃o occCompl a j` (order preserving);
  * `complEquiv_mem` — enumerated particles are not assigned to `j`;
  * the partition facts: `occSet` and `occCompl` are disjoint and cover all
    particles (`occSet_disjoint_compl`, `occSet_union_compl`).

Together with `occEquiv` this gives the coordinate split behind the
occupied-fiber measure identification (L1 of the bracket): the full space
`X N` is (up to the measure-preserving reordering by `occEquiv` ⊔ `complEquiv`)
the product `X (cellCount a j) × X (N − cellCount a j)` of the occupied and the
frozen-background fibers.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The set of particles NOT assigned to the cell `j` (the frozen background of
the slice). -/
def occCompl {m N : ℕ} (a : Assign m N) (j : CellIdx m) : Finset (Fin N) :=
  (occSet a j)ᶜ

/-- The cardinality of the complement is `N − cellCount a j`. -/
lemma occCompl_card {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    (occCompl a j).card = N - cellCount a j := by
  classical
  unfold occCompl occSet cellCount
  rw [Finset.card_compl]
  simp

/-- The order-preserving bijection between `Fin (N − cellCount a j)` and the
particles not assigned to cell `j`. -/
noncomputable def complEquiv {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    Fin (N - cellCount a j) ≃o {i : Fin N // i ∈ occCompl a j} :=
  Finset.orderIsoOfFin (occCompl a j) (occCompl_card a j)

/-- Every enumerated complement particle is assigned to a cell different from
`j`. -/
lemma complEquiv_mem {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (t : Fin (N - cellCount a j)) :
    a (((complEquiv a j) t : {i : Fin N // i ∈ occCompl a j}) : Fin N) ≠ j := by
  classical
  have hx := (complEquiv a j t).property
  simpa [occCompl, occSet] using hx

/-- The occupied set and its complement are disjoint. -/
lemma occSet_disjoint_compl {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    Disjoint (occSet a j) (occCompl a j) := by
  classical
  rw [Finset.disjoint_left]
  intro i hi hi'
  have hnot : i ∉ occSet a j := by
    simpa [occCompl] using hi'
  exact hnot hi

/-- The occupied set and its complement cover all particles. -/
lemma occSet_union_compl {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    occSet a j ∪ occCompl a j = Finset.univ := by
  classical
  ext i
  by_cases h : a i = j
  · simp [occSet, occCompl, h]
  · simp [occSet, occCompl, h]

/-- The restriction of a configuration to the complement particles (in
`complEquiv` order). -/
noncomputable def complRestrict {m N : ℕ} (a : Assign m N) (j : CellIdx m) (x : X N) :
    X (N - cellCount a j) :=
  fun t : Fin (N - cellCount a j) =>
    x (((complEquiv a j) t : {i : Fin N // i ∈ occCompl a j}) : Fin N)

/-- Insertion of the complement coordinates over an occupied background. -/
noncomputable def complInsert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (z : X (N - cellCount a j)) (x : X N) : X N :=
  fun i : Fin N => if h : i ∈ occCompl a j then
    z (((complEquiv a j).symm) ⟨i, h⟩)
  else
    x i

/-- Restricting an insertion recovers the inserted complement configuration. -/
lemma complRestrict_insert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (z : X (N - cellCount a j)) (x : X N) :
    complRestrict a j (complInsert a j z x) = z := by
  funext t
  unfold complRestrict complInsert
  rw [dif_pos]
  · congr 1
    simp
  · exact ((complEquiv a j) t).property

/-- Inserting the complement restriction of a configuration recovers it. -/
lemma complInsert_restrict {m N : ℕ} (a : Assign m N) (j : CellIdx m) (x : X N) :
    complInsert a j (complRestrict a j x) x = x := by
  funext i
  unfold complInsert complRestrict
  by_cases hi : i ∈ occCompl a j
  · rw [dif_pos hi]
    congr 1
    simp
  · rw [dif_neg hi]

/-- The full insertion map, writing both the occupied (`y`) and complement
(`z`) coordinates. -/
noncomputable def fullInsert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (y : X (cellCount a j)) (z : X (N - cellCount a j)) : X N :=
  occInsert a j y (complInsert a j z (0 : X N))

/-- Restricting the full insertion recovers the occupied part. -/
lemma occRestrict_fullInsert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (y : X (cellCount a j)) (z : X (N - cellCount a j)) :
    occRestrict a j (fullInsert a j y z) = y := by
  unfold fullInsert
  exact occRestrict_insert a j y (complInsert a j z (0 : X N))

/-- Inserting the occupied coordinates does not affect the complement
restriction (the two index sets are disjoint). -/
lemma complRestrict_occInsert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (y : X (cellCount a j)) (x : X N) :
    complRestrict a j (occInsert a j y x) = complRestrict a j x := by
  classical
  funext t
  unfold complRestrict occInsert
  have hi : (((complEquiv a j) t : {i : Fin N // i ∈ occCompl a j}) : Fin N) ∉ occSet a j := by
    have hx := (complEquiv a j t).property
    change (((complEquiv a j) t : {i : Fin N // i ∈ occCompl a j}) : Fin N) ∈ (occSet a j)ᶜ at hx
    exact (Finset.mem_compl.mp hx)
  rw [dif_neg hi]

/-- Restricting the full insertion recovers the complement part. -/
lemma complRestrict_fullInsert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (y : X (cellCount a j)) (z : X (N - cellCount a j)) :
    complRestrict a j (fullInsert a j y z) = z := by
  unfold fullInsert
  rw [complRestrict_occInsert]
  exact complRestrict_insert a j z (0 : X N)

end BoseGases

end Submission
