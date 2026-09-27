import Mathlib
import Submission.Work.Drive.affRepSymm
import Submission.Work.Drive.perturbedTripleIdentity

/-!
# The affine invariance of the design's plane presentations

The unrestricted rows-1/2 producer (`ROW1_ENDTRIPLEREG_STATUS.md` §6) needs the presentations to be
invariant under the affine representatives `x ↦ (ε i * x i + 2 m i)` with `ε i = ±1`.  This file proves
it for the design's own presentations (`blockPlane Ξ Q u τ k`, hence for `diskPlane` and every rotated
plane as well): they all factor through `foldBox`, and `foldFun` is invariant under `x ↦ x + 2m` and
`x ↦ -x` (`Work.Drive.foldFun_foldRep`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-- **`foldBox` is invariant under the affine representatives.** -/
lemma foldBox_affRep {ε : Fin 2 → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) (m : Fin 2 → ℤ)
    (y : EuclideanSpace ℝ (Fin 2)) : foldBox (affRep ε m y) = foldBox y := by
  simp only [foldBox, affRep_apply]
  rw [foldFun_foldRep (hε 0) (y 0) (m 0), foldFun_foldRep (hε 1) (y 1) (m 1)]

/-- **The plane presentations are invariant under the affine representatives.** -/
lemma diskPlane_affRep {ε : Fin 2 → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) (m : Fin 2 → ℤ)
    (Q : ℂ → Work.Drive.CappingSpace) (y : EuclideanSpace ℝ (Fin 2)) :
    diskPlane Q (affRep ε m y) = diskPlane Q y := by
  simp only [diskPlane_apply, foldBox_affRep hε m y]

/-- **The rotated plane presentations are invariant under the affine representatives.** -/
lemma rotPresentation_affRep {ε : Fin 2 → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) (m : Fin 2 → ℤ)
    (Q : ℂ → Work.Drive.CappingSpace) (w : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2)) :
    rotPresentation Q w (affRep ε m y) = rotPresentation Q w y := by
  simp only [rotPresentation, diskPlane_apply, foldBox_affRep hε m y]

/-- **The design's plane presentations are invariant under the affine representatives** — the `hinv`
input of the intended unrestricted rows-1/2 producer. -/
lemma blockPlane_affRep {ε : Fin 2 → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) (m : Fin 2 → ℤ)
    (Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (u : Fin 3 → UnitAddCircle)
    (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)) :
    blockPlane Ξ Q u τ k (affRep ε m y) = blockPlane Ξ Q u τ k y := by
  simp only [blockPlane, rotPresentation_affRep hε m Q (u k) y]

end

end Work.Drive
