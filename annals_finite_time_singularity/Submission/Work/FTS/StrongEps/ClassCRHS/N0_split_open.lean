import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Construction.Terms
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real

/-- **The `N₀`-split on the open quadrant**, for the local hypothesis `SmoothOpen w` alone.

`N₀ α (F_* + w) w` is a sum of six products, and the only place where `F = F_* + w` enters is
through `∂_θF` (in `N₀₄`) and `D_zF` (in `N₀₅`).  On the open quadrant both operators are
*additive* (`Rl1.openSlice_pth_add`, `Rl1.openSlice_pz_add` via `Pieces.Dz_add_of_diff`),
because the slices of `F_*` and `w` are differentiable there; splitting them turns `N₀₄` into
`N₀₄ᵃ + N₀₄ᵇ` and `N₀₅` into `N₀₅ᵃ + N₀₅ᵇ`, while `N₀₁ + N₀₂` (which involve only `F_*`) is
`N0fix`.  This is the first conjunct of `Work.FTS.NonlinRows.SplitsAll`, with the `ClassC`
context of that statement replaced by the bare smoothness of `w` that its proof actually uses. -/
theorem N0_split_open {α : ℝ} (hα : 0 < α) {w : Work.FTS.Galerkin.Fn}
    (hw : Work.FTS.EllipticEst.SmoothOpen w) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Work.Construction.Ftot α w) w z θ
        = Work.FTS.Nonlin.N0fix α z θ
          + (Work.FTS.Nonlin.N03g α w z θ
            + (Work.FTS.Nonlin.N04aF α w z θ
              + (Work.FTS.Nonlin.N04bF α w z θ
                + (Work.FTS.Nonlin.N05aF α w z θ
                  + (Work.FTS.Nonlin.N05bF α w z θ
                    + Work.FTS.Nonlin.N06F α w z θ))))) := by
  have _ := hα
  intro z θ hq
  have hz : 0 < z := hq.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
  -- `F_*` is `C^∞` on the open quadrant, for every real `α`
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  -- additivity of `∂_θ` and of `D_z` on `F = F_* + w`
  have hpth : Work.Spaces.pth (Work.Construction.Ftot α w) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth w z θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add hF hw hz hθ
  have hDz : Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz w z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hF hw hz hθ)
  simp only [Work.Construction.N0, Work.FTS.Nonlin.N0fix, Work.FTS.Nonlin.N03g,
    Work.FTS.Nonlin.N04aF, Work.FTS.Nonlin.N04bF, Work.FTS.Nonlin.N05aF,
    Work.FTS.Nonlin.N05bF, Work.FTS.Nonlin.N06F, Work.Construction.N01,
    Work.Construction.N02, Work.Construction.N03, Work.Construction.N04a,
    Work.Construction.N04b, Work.Construction.N05a, Work.Construction.N05b,
    Work.Construction.N06]
  rw [hpth, hDz]
  ring

end Work.FTS.StrongEps.ClassCRHS
