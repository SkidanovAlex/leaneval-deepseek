import Submission.DS.CircCorr

open scoped Nat ENNReal NNReal
open Set Filter MeasureTheory Metric
open DuffinSchaefferConjecture

/-!
# Boundary sets on the circle are null

The `≤`-membership of `mem_Acopr_iff_circle` and the `<`-membership defining
`approxAddOrderOf` differ only along the spheres of radius `ψ(q)/q` around the reduced
fractions `m/q`.  On the circle such a sphere contains at most two points, hence has
measure zero, and only finitely many fractions `m/q` occur for a fixed `q`.

Suggested route: prove `sphere_measure_zero` by showing the sphere is finite:
lift points to a real fundamental domain, where distance to a fixed class is
`min (|t|, 1 - |t|)`-shaped, so the equation `dist = r` has at most two solutions.
`Set.Finite.measure_zero` (needs `NullSingletonClass volume`) then gives the measure.
-/

namespace Submission.DS

/-- The sphere of radius `r` around `c` is exactly the boundary of the closed ball:
`‖x - c‖ = r` iff `x` is in the closed ball but not in the open ball. -/
lemma sphere_eq_closedBall_sdiff_ball (c : AddCircle (1 : ℝ)) (r : ℝ) :
    {x : AddCircle (1 : ℝ) | ‖x - c‖ = r} = closedBall c r \ ball c r := by
  ext x
  simp

/-- On the unit circle a sphere of radius `r` has measure zero (it has ≤ 2 points). -/
lemma sphere_measure_zero (c : AddCircle (1 : ℝ)) (r : ℝ) :
    volume ({x : AddCircle (1 : ℝ) | ‖x - c‖ = r}) = 0 := by
  rw [sphere_eq_closedBall_sdiff_ball]
  have h := AddCircle.closedBall_ae_eq_ball (x := c) (ε := r)
  exact (ae_eq_set.mp h).1

/-- For a fixed denominator `q`, the points exactly at distance `r` from a reduced
fraction `m/q` form a null set. -/
lemma circle_boundary_measure_zero (q : ℕ+) (r : NNReal) :
    volume ({x : AddCircle (1 : ℝ) | ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
      ‖x - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ))‖ = (r : ℝ)}) = 0 := by
  let B : Fin (q : ℕ) → Set (AddCircle (1 : ℝ)) :=
    fun m => {x : AddCircle (1 : ℝ) | ‖x - (((m.1 : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ))‖ = (r : ℝ)}
  have hB0 : ∀ m : Fin (q : ℕ), volume (B m) = 0 := by
    intro m
    exact sphere_measure_zero ((((m.1 : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ))) (r : ℝ)
  have hsub : ({x : AddCircle (1 : ℝ) | ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
      ‖x - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ))‖ = (r : ℝ)}) ⊆ ⋃ m : Fin (q : ℕ), B m := by
    intro x hx
    rcases hx with ⟨m, hmq, hcop, hn⟩
    refine mem_iUnion.mpr ?_
    refine ⟨⟨m, hmq⟩, ?_⟩
    exact hn
  have hle : volume ({x : AddCircle (1 : ℝ) | ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
      ‖x - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ))‖ = (r : ℝ)}) ≤ 0 := by
    calc
      volume ({x : AddCircle (1 : ℝ) | ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
        ‖x - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ))‖ = (r : ℝ)}) ≤ volume (⋃ m : Fin (q : ℕ), B m) :=
          measure_mono hsub
      _ ≤ ∑' m : Fin (q : ℕ), volume (B m) := measure_iUnion_le _
      _ = 0 := by
        simp [hB0]
  exact le_antisymm hle bot_le

end Submission.DS
