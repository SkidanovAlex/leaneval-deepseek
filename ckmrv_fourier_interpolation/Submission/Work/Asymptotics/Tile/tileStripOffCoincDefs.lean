/-
# The resonant-strip deviation on the cusp-`±1` tiles, away from the coincidences

The below-pole window `1 ≤ t ≤ 2 Im (S • w) + 1` of the tile deviation

  `dev ℓ d τ t = Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t`

is split into three `t`-regimes:

* `1 ≤ t ≤ Im (S • w) - 1`  : `Work.Asymptotics.Tile.TileBelowPoleFar` (no coincidence occurs there);
* `Im (S • w) - 1 ≤ t ≤ Im (S • w) + 1` : `TileBelowPoleStripOffCoinc` (this file) — the *non*-
  coincidence hypothesis is essential here (at `j ((n : ℝ) +ᵥ w) = j (i t)` the formula defining
  `Kfun` takes Lean's junk value `0⁻¹ = 0`, which is exponentially large);
* `Im (S • w) + 1 ≤ t ≤ 2 Im (S • w) + 1` : `Work.Asymptotics.Tile.TileBelowPoleTop` (proved).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs

namespace Work.Asymptotics.Tile

/-- **The resonant strip of the tile deviation, away from the coincidences.**  For `w ∈ E = KEpsilon`,
`n = ±1` and `t` in the resonant window `Im (S • w) - 1 ≤ t ≤ Im (S • w) + 1`, the deviation of the
CKMRV kernel from its cusp model is bounded by `C (scale w)^N t^M` *provided* `j (n +ᵥ w) ≠ j (i t)`.

The non-coincidence hypothesis is not removable: at a coincidence Lean's `Kfun` is the algebraic
junk value obtained by setting `(j τ - j z)⁻¹ := 0`, which is exponentially large in `scale w`
along the tile (numerically confirmed in `_tileStripCuspNeg1_FINDINGS.md`).  On the strip the
divisor `Δ(z)(j(n +ᵥ w) - j(z))` is *not* bounded below, which is why this regime is the crux of
the below-pole window. -/
def TileBelowPoleStripOffCoinc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), (ModularGroup.S • w).im - 1 ≤ t →
        t ≤ (ModularGroup.S • w).im + 1 →
        Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
            ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M

end Work.Asymptotics.Tile
