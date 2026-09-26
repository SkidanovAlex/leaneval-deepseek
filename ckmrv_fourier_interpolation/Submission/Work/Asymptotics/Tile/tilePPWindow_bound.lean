/-
# The tile principal-part window (assembly)

The statement `Work.Asymptotics.Tile.tilePPWindow_bound` is by definition
(`Work.Asymptotics.TilePPWindow`, `Submission/Work/Asymptotics/Tile/tileLayerDefs.lean`) the
principal-part window on the cusp-`±1` tiles: for `w ∈ E = KEpsilon`, `n = ±1` and
`Im w / 2 ≤ t ≤ 1` the kernel `K(n +ᵥ w, i t)` differs from the principal part of its translate
pole `z = w` by at most `C (scale w)^N`.

The window is assembled in `Submission/Work/Asymptotics/Tile/tilePPWindowGoal.lean` from

* `Work.Asymptotics.TileWindow.tile_pp_window_full` — the *unguarded* window bound for `i t ≠ w`
  (the cone-separated bound plus the maximum-modulus spike bound), and
* `Work.Asymptotics.Tile.tilePPWindow_coincidence` — the value at the coincidence `i t = w`,
  where the principal part vanishes and the target is the translated diagonal value of `Kfun`,
  controlled by the cusp bounds `norm_Eisenstein_imagAxis_atZero` and `MFix`.

This file therefore only has to unfold `TilePPWindow`.
-/
import Mathlib
import Submission.Work.Asymptotics.Tile.tileLayerDefs
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Tile.tilePPWindowGoal

noncomputable section

namespace Work.Asymptotics.Tile

/-- **The tile principal-part window `Work.Asymptotics.TilePPWindow`.** -/
theorem tilePPWindow_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ, (n = 1 ∨ n = -1) →
        ∀ t : ℝ, w.im / 2 ≤ t → t ≤ 1 →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
          ≤ C * (Work.Kernels.scale w) ^ N :=
  tilePPWindowGoal ℓ d hd

end Work.Asymptotics.Tile
