/-
# `Work.FTS.LocData.hLoc_vanishing` — the bump `hLoc` vanishes on the angular boundary and at
the axis `z = 0`

The localised data chapter (`Submission/Work/FTS/LocData/`) builds the admissible perturbation of
the self-similar profile out of the bump `hLoc α z θ = φ(z)·Γ(θ)` of `Defs.lean`, with the radial
factor `φ = bumpZ` (`= χ(4z-5)`, supported in `(3/4, 7/4)`) and the angular factor
`Γ(θ) = (sinθ cos²θ)^{α/3}`.

This module proves the two vanishing properties that make `hLoc` *admissible*
(`DataAdm` of `Defs.lean`):

* `VanishTheta (hLoc α)`: `hLoc α z 0 = 0` and `hLoc α z (π/2) = 0` for every `z` — this is the
  vanishing of the angular factor `Γ` at the two ends of `Iθ` (`Work.Spaces.Gam_zero_left`,
  `Work.Spaces.Gam_zero_right`), and it is what makes the physical `e_θ`-field smooth in the frame
  and divergence-free (`Work.ConstructionInstance`).
* `hLoc α 0 θ = 0` and `∂_z (hLoc α) 0 θ = 0` for `θ ∈ Iθ`: the radial factor `bumpZ` vanishes
  *on a neighbourhood of* `z = 0` (`|4z - 5| > 2` for `|z| < 1/2`, where `χ = 0`), so both the
  value and the `z`-derivative vanish there — the quadratic vanishing at the axis that makes the
  weight `w = (1+z)²/z²` harmless.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.LocData

/-- **The radial bump vanishes near `z = 0`.**  For `|z| < 1/2` one has `4z - 5 ∈ (-7,-3)`, hence
`|4z - 5| > 2` and `χ(4z-5) = 0` (`Work.Stability.chi_eq_zero`). -/
theorem bumpZ_eventuallyEq_zero : ∀ᶠ z in 𝓝 (0 : ℝ), bumpZ z = 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  rw [Metric.mem_ball, Real.dist_eq] at hz
  have hz' : |z| < 1 / 2 := by simpa using hz
  rw [bumpZ_apply, Work.Stability.chi_eq_zero]
  have hzlt : z < 1 / 2 := (abs_lt.mp hz').2
  have hneg : 4 * z - 5 < 0 := by linarith
  rw [abs_of_neg hneg]
  linarith

/-- The radial bump vanishes at `z = 0` (specialisation of `bumpZ_eventuallyEq_zero`). -/
theorem bumpZ_zero : bumpZ 0 = 0 := by
  rw [bumpZ_apply, show (4 : ℝ) * 0 - 5 = -5 by norm_num]
  exact Work.Stability.chi_eq_zero (by norm_num)

theorem hLoc_vanishing (α : ℝ) (hα : 0 < α) :
    Work.Spaces.VanishTheta (hLoc α) ∧
      (∀ θ ∈ Work.Spaces.Iθ, hLoc α 0 θ = 0 ∧ Work.Spaces.pz (hLoc α) 0 θ = 0) := by
  have hG0 : Work.Spaces.Gam α 0 = 0 := Work.Spaces.Gam_zero_left α (ne_of_gt hα)
  have hGpi : Work.Spaces.Gam α (π / 2) = 0 := Work.Spaces.Gam_zero_right α (ne_of_gt hα)
  -- The radial factor vanishes at `z = 0`, so both `hLoc α 0 θ` and its `z`-derivative vanish.
  have hz0 : ∀ θ : ℝ, hLoc α 0 θ = 0 := by
    intro θ
    rw [hLoc_apply, bumpZ_zero, zero_mul]
  have hdz0 : ∀ θ : ℝ, Work.Spaces.pz (hLoc α) 0 θ = 0 := by
    intro θ
    have hev : (fun z => hLoc α z θ) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [bumpZ_eventuallyEq_zero] with z hz
      rw [hLoc_apply, hz, zero_mul]
    show deriv (fun z => hLoc α z θ) 0 = 0
    rw [hev.deriv_eq, deriv_const]
  refine ⟨⟨fun z => ?_, fun z => ?_⟩, fun θ _ => ⟨hz0 θ, hdz0 θ⟩⟩
  · rw [hLoc_apply, hG0, mul_zero]
  · rw [hLoc_apply, hGpi, mul_zero]

end Work.FTS.LocData
