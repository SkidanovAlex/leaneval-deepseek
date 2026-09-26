/-
# The `K_+` cusp-`i∞` tail on the cusp-`±1` tiles

Assembly of the two dimension-specific halves
`Work.Asymptotics.Tile.KPlus8TileTail` (`Submission/Work/Asymptotics/Tile/KPlus8TileTail.lean`)
and `Work.Asymptotics.Tile.KPlus24TileTail` (`Submission/Work/Asymptotics/Tile/KPlus24TileTail.lean`).
-/
import Mathlib
import Submission.Work.Asymptotics.Tile.tileTB
import Submission.Work.Asymptotics.Tile.KPlus8TileTail
import Submission.Work.Asymptotics.Tile.KPlus24TileTail

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane
open Work.Kernels Work.Asymptotics

noncomputable section

/-- **The `K_+` half of the sharp cusp-`i∞` tail on the cusp-`±1` tiles.** -/
theorem KPlusTileTail (d : ℕ) (hd : d = 8 ∨ d = 24) :
    TB Real.pi 1
      (fun (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) =>
        Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) z) := by
  rcases hd with rfl | rfl
  · exact KPlus8TileTail
  · exact KPlus24TileTail

end

end Work.Asymptotics.Tile
