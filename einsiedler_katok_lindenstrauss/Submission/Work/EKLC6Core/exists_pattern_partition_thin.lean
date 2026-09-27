import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.Misiurewicz.frontier_finite_subset
import Submission.Work.EKLC6Core.exists_staircase_partition
import Submission.Work.EKLC6Core.measure_iUnion_smul_frontier_le

/-!
# `Work.EKLC6Core.exists_pattern_partition_thin`

**The "staircase" partition of a thin-frontier finite cover.**

Given a finite measurable family `U : Fin m → X₃` covering all but `< ε` of `μ` in measure, and
such that for every `i` the `V η`-neighbourhood of `∂U_i` (pushed to `X₃` by the action) has
measure `≤ c_i η`, we produce a finite measurable partition `P : Fin (m + 1) → X₃` together
with an exceptional cell `i₀` such that

* all other cells refine the given cover (`P i ⊆ U j` for some `j`),
* `μ (P i₀) < ε`,
* the frontier-neighbourhood estimate survives, with the explicit constant `∑_j c_j + 1`.

The partition is the staircase

  `P i = U i \ ⋃_{j < i} U j`  (`i < m`),   `P i₀ = (⋃_j U j)ᶜ`  (`i₀ = last`),

whose cells have frontiers inside `⋃_j ∂U_j` (frontier of a finite union/intersection/difference
of sets), so that `P` inherits the thinness of `U` cell by cell.

## Proof structure

The proof is the assembly of two independent pieces (delegated lemmas, both proved elsewhere in
this workspace):

* `Work.EKLC6Core.exists_staircase_partition` — the purely topological/measure-theoretic
  combinatorics producing `P`, `i₀` with disjointness, cover, refinement, measurability and the
  frontier inclusion `∂(P i) ⊆ ⋃_j ∂U_j`;
* `Work.EKLC6Core.measure_iUnion_smul_frontier_le` — the estimate transferring the individual
  bounds `μ (V η • ∂U_j) ≤ c_j η` to the union over the cells of `P`, giving the constant
  `∑_j c_j + 1`.
-/

namespace Work.EKLC6Core

open MeasureTheory
open scoped ENNReal

set_option linter.unusedVariables false

theorem exists_pattern_partition_thin (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure μ] {m : ℕ} (U : Fin m → Set Work.EKLContract.X3)
    (hUmeas : ∀ i, MeasurableSet (U i))
    (hthin : ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η →
      μ ((fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
          ((Work.EKLContract.V η) ×ˢ frontier (U i))) ≤ ENNReal.ofReal (c * η))
    (ε : ℝ) (hε : 0 < ε)
    (hcomp : μ ((⋃ i, U i))ᶜ < ENNReal.ofReal ε) :
    ∃ (N : ℕ) (P : Fin N → Set Work.EKLContract.X3) (i₀ : Fin N) (c : ℝ),
      0 < c ∧ (∀ i, MeasurableSet (P i)) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = Set.univ ∧
      (∀ i, i ≠ i₀ → ∃ j, P i ⊆ U j) ∧
      μ (P i₀) < ENNReal.ofReal ε ∧
      (∀ η : ℝ, 0 < η →
        μ (⋃ i, (fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
          ((Work.EKLContract.V η) ×ˢ (frontier (P i)))) ≤ ENNReal.ofReal (c * η)) := by
  classical
  -- Extract the individual thinness constants attached to the cells `U i`.
  let cU : Fin m → ℝ := fun i => Classical.choose (hthin i)
  have hcUpos : ∀ i, 0 < cU i := fun i => (Classical.choose_spec (hthin i)).1
  have hcUbound : ∀ i, ∀ η : ℝ, 0 < η →
      μ ((fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
          ((Work.EKLContract.V η) ×ˢ frontier (U i))) ≤ ENNReal.ofReal (cU i * η) :=
    fun i => (Classical.choose_spec (hthin i)).2
  -- The staircase partition of the cover.
  obtain ⟨P, i₀, hsub, hdisj, hcover, hi₀, hmeas, hfr⟩ := exists_staircase_partition U hUmeas
  refine ⟨m + 1, P, i₀, (∑ j, cU j) + 1, ?_, hmeas, hdisj, hcover, hsub, ?_, ?_⟩
  · -- positivity of the constant
    have hnn : (0 : ℝ) ≤ ∑ j, cU j := Finset.sum_nonneg fun j _ => (hcUpos j).le
    linarith
  · -- the exceptional cell carries less than `ε`
    rw [hi₀]
    exact hcomp
  · -- thinness is inherited by the staircase
    intro η hη
    exact measure_iUnion_smul_frontier_le μ hcUpos hη (fun i => hcUbound i η hη) P hfr

end Work.EKLC6Core
