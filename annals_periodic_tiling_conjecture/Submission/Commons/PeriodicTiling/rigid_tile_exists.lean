import Mathlib
import Submission.Commons.PeriodicTiling.rigid_tile_rigid

namespace Commons.PeriodicTiling

open Filter Bornology MeasureTheory

theorem rigid_tile_exists
    {d : ℕ} (hd : 0 < d) :
    ∃ R : Set (Fin d → ℝ), IsBounded R ∧ MeasurableSet R ∧ 0 < volume R ∧
      IsContinuousTiling R {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)} ∧
      ∀ Λ : Set (Fin d → ℝ), IsContinuousTiling R Λ →
        ∃ t : Fin d → ℝ,
          Λ = (fun x : Fin d → ℝ => x + t) ''
            {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)} := by
  exact rigid_tile_rigid hd

end Commons.PeriodicTiling
