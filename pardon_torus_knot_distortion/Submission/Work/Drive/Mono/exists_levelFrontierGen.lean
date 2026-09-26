import Mathlib
import Submission.Work.Drive.Mono.LevelFrontierGen
import Submission.Work.Drive.Mono.exists_badLevels

/-!
# The genericity of the level frontier outside a finite set of levels

`Work.Drive.Mono.LevelFrontierGen` is the genericity of the tilt data which the (proved) brick
`Work.Drive.Mono.tiltedLevel_disjoint_spheres` needs — the geometric input of clause 1 of the tilted
sweep.  This module turns it into a *choice of the data*: given the tilt data and a window containing
the `ℓ`-range of the closed box, there is a finite set `exc` of levels, inside the window, outside
which all three conditions hold.

The content is `Work.Drive.Mono.exists_badLevels` (proved): the levels at which a condition fails are
the `ℓ`-values of the box edges in a direction in which `ℓ` vanishes, the `ℓ`-values of the vertices,
and the three seam values `Q₊, Q₋, β` — all of them `ℓ`-values of points of the closed box, hence
inside any window containing the `ℓ`-range of the box.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **The genericity of the level frontier holds outside a finite set of levels** (all of them in
the window). -/
theorem exists_levelFrontierGen (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ)
    (hv : ‖v‖ = 1) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (hwin : ∀ y ∈ closure (Submission.PBox s c σ), lam0 < ℓ y ∧ ℓ y < lam1) :
    ∃ exc : Finset ℝ, (∀ t ∈ exc, lam0 < t ∧ t < lam1) ∧
      LevelFrontierGen s c σ u v h ℓ exc lam0 lam1 := by
  obtain ⟨B, hBwin, hB⟩ := exists_badLevels (c := c) (σ := σ) (v := v) (h := h) (ℓ := ℓ)
    (exc := ∅) (lam0 := lam0) (lam1 := lam1) (s := s) (u := u) hh hℓv hℓne hcut hwin
  exact ⟨B, hBwin, fun lam hlam hne => hB lam hlam (by simpa using hne)⟩

end

end Work.Drive.Mono
