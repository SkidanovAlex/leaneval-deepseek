import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

/-- Pointwise (in `(z,θ)`) uniform-in-`σ` bound for a single mixed jet of `∂_τ g`, extracted from
the local bounds packaged in `GdotLoc S g`.  In `GdotLoc` the bounds are stated on compact boxes
`Icc a b × Icc c d` with `a > 0` and `d < π/2`; instantiating the box at the *single point*
`(z,θ)` (i.e. `a = b = z`, `c = d = θ`) gives the bound at that point, uniformly for
`σ ∈ Ioc 0 S`.  The constant is clamped to `≥ 0` (harmless: a bound on a nonempty range already
forces nonnegativity, and the vacuous case `Ioc 0 S = ∅` admits `C = 0`). -/
theorem abs_mixed_gdot_le_of_GdotLoc {S : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hG : Work.FTS.RegExportIface.RXT.GdotLoc S g) {j i : ℕ} (hji : j + i ≤ 2)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Ioc (0 : ℝ) S,
      |Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ) z θ| ≤ C := by
  -- the degenerate box `[z,z] × [θ,θ]`: all side conditions of `GdotLoc` are immediate
  obtain ⟨C₀, hC₀⟩ := hG.2 z z θ θ hz le_rfl hθ0 le_rfl hθ1
  refine ⟨max 0 C₀, le_max_left 0 C₀, fun σ hσ => ?_⟩
  have hz' : z ∈ Set.Icc z z := Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
  have hθ' : θ ∈ Set.Icc θ θ := Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
  exact le_trans ((hC₀ σ hσ z hz' θ hθ').1 j i hji) (le_max_right 0 C₀)

end Work.FTS_RegExport.RXT.Sys
