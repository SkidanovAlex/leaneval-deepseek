import Mathlib
import Submission.Work.Asymptotics.Tile.tileTB
import Submission.Work.Asymptotics.Tile.tileDivisorSharp
import Submission.Work.Asymptotics.Tile.SharpTB8
import Submission.Work.Asymptotics.Tile.SharpTB24

namespace Work.Asymptotics.Tile

/-- **The sharp `K_+` tail on the cusp-`±1` tiles.**

The crude tile calculus `Work.Asymptotics.Tile.TB` proves the bound
`‖K_+^{(d)} (n +ᵥ w) z − 𝒢_+^{(d)} (n +ᵥ w) z‖ ≤ C (scale w)^N (1+t)^M e^{π Im(S•w) − π t}`
for `z = i t` with `t ≥ 2 Im (S • w) + 1` (see `Work.Asymptotics.Tile.KPlusTileTail`).
Here the threshold is improved to the *sharp* one `t ≥ Im (S • w) + 1`, which is the threshold
at which the divisor `Δ(z)(j(n+w) − j z)` is bounded below by `1/16`
(`Work.Asymptotics.Tile.tileDivisorLowerSharp`) and at which every analytic ingredient
(the `τ`-atoms and the `z`-atoms) is available.

The proof is the sharp-threshold `τ`/`z`-atom calculus `Work.Asymptotics.Tile.TBS`
(`Submission/Work/Asymptotics/Tile/SharpTB.lean`): the two dimension-specific halves
`TBS8TileTail` (`SharpTB8.lean`) and `TBS24TileTail` (`SharpTB24.lean`) are proved exactly as in
`KPlus8TileTail`/`KPlus24TileTail`, with the sole change that the final absorption

  `e^{2π Im(S•w) − 2π t} ≤ e^{π Im(S•w) − π t}`

is now possible already at `t ≥ Im (S • w)` (rather than `t ≥ 2 Im (S • w)`), because the
combination `Δ(z) · j(n +ᵥ w)` contributes the full decay `e^{−2π(t − Im(S•w))}`. -/
theorem KPlusTileTailSharp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
        (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        (z : ℂ) = (t : ℂ) * Complex.I → (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) z‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
            * Real.exp (Real.pi * ((ModularGroup.S • w).im - t)) := by
  have _hℓ : Work.Kernels.LogLambdaData := ℓ
  rcases hd with rfl | rfl
  · obtain ⟨C, N, M, hC, hN, hM, hb⟩ := TBS8TileTail
    exact ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht => by
      have h := hb w n z t hn hw hz ht
      rwa [show Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t
            = Real.pi * ((ModularGroup.S • w).im - t) from by ring] at h⟩
  · obtain ⟨C, N, M, hC, hN, hM, hb⟩ := TBS24TileTail
    exact ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht => by
      have h := hb w n z t hn hw hz ht
      rwa [show Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t
            = Real.pi * ((ModularGroup.S • w).im - t) from by ring] at h⟩

end Work.Asymptotics.Tile
