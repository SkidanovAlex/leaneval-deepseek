import Mathlib
import Submission.Work.WilE9G.Sard.rankDefs

namespace Work.WilE9G.Sard

/-- The preimage of a closed ball under any "insert-a-coordinate" map
`w ↦ Fin.insertNth j c w` is bounded: each coordinate `w i` is one of the
coordinates of `insertNth j c w`, hence within distance `ρ` of the
corresponding coordinate of `y₀`. -/
theorem isBounded_insertNth_preimage_closedBall {k : ℕ} (j : Fin (k + 1)) (c : ℝ)
    (y₀ : Fin (k + 1) → ℝ) (ρ : ℝ) :
    Bornology.IsBounded
      {w : Fin k → ℝ | Fin.insertNth (α := fun _ => ℝ) j c w ∈ Metric.closedBall y₀ ρ} := by
  -- `s` is contained in the product of the bounded coordinate-wise closed balls,
  -- and a product of bounded sets is bounded (`Bornology.IsBounded.pi`).
  apply Bornology.IsBounded.subset
    (Bornology.IsBounded.pi
      (fun i => Metric.isBounded_closedBall (x := y₀ (j.succAbove i)) (r := ρ)))
  intro w hw
  rw [Set.mem_pi]
  intro i _
  simp only [Set.mem_ofPred_eq] at hw
  rw [Metric.mem_closedBall] at hw ⊢
  -- the `i`-th coordinate of `insertNth j c w` is exactly `w i`
  have hcoord : Fin.insertNth (α := fun _ => ℝ) j c w (j.succAbove i) = w i :=
    Fin.insertNth_apply_succAbove (α := fun _ => ℝ) j c w i
  calc dist (w i) (y₀ (j.succAbove i))
      = ‖(Fin.insertNth (α := fun _ => ℝ) j c w - y₀) (j.succAbove i)‖ := by
        rw [Pi.sub_apply, hcoord, dist_eq_norm]
    _ ≤ ‖Fin.insertNth (α := fun _ => ℝ) j c w - y₀‖ := norm_le_pi_norm _ _
    _ = dist (Fin.insertNth (α := fun _ => ℝ) j c w) y₀ := by rw [dist_eq_norm]
    _ ≤ ρ := hw

end Work.WilE9G.Sard
