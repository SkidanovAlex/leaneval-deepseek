import Mathlib
import Submission.Work.RatHurewicz.DiskPairDefs

set_option synthInstance.maxHeartbeats 400000

/-!
# `0`-connectedness of the pair `(D^{n+2}, D^{n+2} ∖ {0})`

The first hypothesis of the compression criterion
`Work.RatHurewicz.compression_of_relPiVanishing`: every point of the model cell is joined by a path
to a point of the punctured cell, the straight segment in the convex disc to the point
`(1/2) • e₀` (`halfE0Pt`).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- The first (and only) vector needed: `e₀` of the standard basis of `ℝ^{n+2}`. -/
def e₀ (n : ℕ) : CellVec n := EuclideanSpace.single (⟨0, by omega⟩ : Fin (n + 2)) 1

theorem e₀_norm (n : ℕ) : ‖e₀ n‖ = 1 := by
  rw [e₀, EuclideanSpace.norm_single]
  norm_num

theorem e₀_ne_zero (n : ℕ) : e₀ n ≠ 0 := by
  intro h
  have := e₀_norm n
  rw [h, norm_zero] at this
  norm_num at this

/-- The centre of the "small ball" point `(1/2) • e₀` of the punctured cell. -/
def halfE0 (n : ℕ) : CellVec n := (1 / 2 : ℝ) • e₀ n

theorem halfE0_norm (n : ℕ) : ‖halfE0 n‖ = 1 / 2 := by
  rw [halfE0, norm_smul, e₀_norm, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

theorem halfE0_mem_disk (n : ℕ) : halfE0 n ∈ Metric.closedBall (0 : CellVec n) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, halfE0_norm]
  norm_num

theorem halfE0_ne_zero (n : ℕ) : halfE0 n ≠ 0 := by
  intro h
  have := halfE0_norm n
  rw [h, norm_zero] at this
  norm_num at this

/-- The point `(1/2) • e₀` of the model cell. -/
def halfE0Pt (n : ℕ) : cellDisk n := ⟨halfE0 n, halfE0_mem_disk n⟩

/-- The point `(1/2) • e₀` of the punctured model cell, the base point of the pair. -/
def halfE0Punctured (n : ℕ) : ↥(puncturedCellDisk n) :=
  ⟨halfE0Pt n, by rw [mem_puncturedCellDisk]; exact halfE0_ne_zero n⟩

@[simp] theorem coe_halfE0Punctured (n : ℕ) :
    ((halfE0Punctured n : ↥(puncturedCellDisk n)) : cellDisk n) = halfE0Pt n := rfl

/-- **The pair `(D^{n+2}, D^{n+2} ∖ {0})` is `0`-connected**: every point of the model cell is
joined to `(1/2) • e₀` by the straight segment in the convex disc. -/
theorem diskPair_zerothConnected (n : ℕ) :
    ∀ y : cellDisk n, ∃ a : ↥(puncturedCellDisk n), Nonempty (Path y a) :=
  fun y => ⟨halfE0Punctured n, ⟨diskSegPath n y (halfE0Pt n)⟩⟩

end

end Work.RatHurewicz
