import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.SmoothCompact_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.EllipticEst

open Set

/-- The angular interval `[0,π/2]` is contained in the open interval on which
`SmoothNbhd` gives smoothness in the `θ`-variable. -/
theorem Iθ_subset_Ioo : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (π / 2 + 1) := by
  intro θ hθ
  obtain ⟨h0, h1⟩ := hθ
  exact ⟨by linarith, by linarith⟩

/-- `∂_z^k u` is jointly continuous on the half-open rectangle `(-1,∞) × [0,π/2]`
whenever `u` is smooth on a neighbourhood of the closed quadrant. -/
theorem continuousOn_uncurry_pzIter {u : ℝ → ℝ → ℝ} (hu : Work.Spaces.SmoothNbhd u)
    (k : ℕ) :
    ContinuousOn (Function.uncurry (Work.Spaces.pzIter k u))
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) :=
  ((Work.Spaces.smoothNbhd_pzIter hu k).continuousOn).mono
    (Set.prod_mono Subset.rfl Iθ_subset_Ioo)

theorem pzIter_uncurry_continuousOn (u : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hu : Work.Spaces.SmoothNbhd u) (hφ : ContinuousOn φ Work.Spaces.Iθ) (k : ℕ) :
    ContinuousOn (Function.uncurry fun z θ => Work.Spaces.pzIter k u z θ * φ θ)
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) := by
  have hpz := continuousOn_uncurry_pzIter hu k
  have hφ' : ContinuousOn (fun p : ℝ × ℝ => φ p.2) (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) :=
    hφ.comp continuous_snd.continuousOn fun p hp => hp.2
  exact hpz.mul hφ'

end Work.FTS.EllipticEst
