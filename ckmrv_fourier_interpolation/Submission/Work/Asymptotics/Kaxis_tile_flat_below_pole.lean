import Mathlib
import Submission.Work.Asymptotics.Kaxis_tile_aux
import Submission.Work.Asymptotics.Tile.tile_divisor_lower
import Submission.Work.Asymptotics.Tile.Kplus_tile_bound
import Submission.Work.Asymptotics.Tile.Kminus_tile_bound

namespace Work.Asymptotics

/-- The `K_+` half of the tile bound, in the `e^{-c/t}` form consumed by
`Work.Asymptotics.Kaxis_tile_flat_of_parts` (with `c = π`). -/
theorem Kplus_tile_bound' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hdiv : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
      (1 / 4 : ℝ) ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
        (Work.Kernels.jInvariantFun w -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖)
    (hjne : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
      Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) ≠
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C N K c : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ K ∧ 0 < c ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
          ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
            ≤ C * (Work.Kernels.scale w) ^ N * (1 + t⁻¹) ^ K * Real.exp (-(c / t)) := by
  obtain ⟨C, N, K, hC, hN, hK, hb⟩ := Tile.Kplus_tile_bound ℓ d hd hdiv hjne
  exact ⟨C, N, K, Real.pi, hC, hN, hK, Real.pi_pos, hb⟩

theorem Kaxis_tile_flat_below_pole (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (N : ℝ) (hN : 0 ≤ N) :
    ∃ c N' : ℝ, 0 ≤ c ∧ 0 ≤ N' ∧ ∀ (w : UpperHalfPlane) (n : ℤ),
      (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon → ∀ t : ℝ, 0 < t →
      t ≤ min 1 (w.im / 2) →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t‖
        ≤ c * (Work.Kernels.scale w) ^ N' * t ^ N :=
  Kaxis_tile_flat_of_parts ℓ d
    (Kplus_tile_bound' ℓ d hd
      (fun w _n _hn hw t ht htle => Tile.tile_divisor_lower w hw t ht htle)
      (fun w n hn hw t ht htle => tile_noncoincidence w hw n hn t ht htle))
    (Tile.Kminus_tile_bound ℓ d hd
      (fun w _n _hn hw t ht htle => Tile.tile_divisor_lower w hw t ht htle)
      (fun w n hn hw t ht htle => tile_noncoincidence w hw n hn t ht htle))
    N hN

end Work.Asymptotics
