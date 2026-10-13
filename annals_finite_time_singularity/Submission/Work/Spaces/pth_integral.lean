/-
Copyright: work module for the Elgindi finite-time singularity project.

# The fundamental theorem of calculus for `∂_θ`

For a function `g` that is smooth on a neighbourhood of the closed quadrant (the
regularity hypothesis `SmoothNbhd g` of this project), all the angular
derivatives `∂_θ g`, evaluated at a fixed radial variable `z ≥ 0`, obey the
fundamental theorem of calculus.  Equivalently, on every compact angular
interval `[0, θ]` with `θ ∈ [0, π/2]` the function `s ↦ ∂_θ g z s` is continuous
and the integral against `ds` recovers the increment `g z θ - g z 0`.

This is the FTC used in §H2 of T. M. Elgindi, *Finite-time singularity formation
for C^{1,α} solutions to the incompressible Euler equations on ℝ³*, Annals of
Math. 194 (3) 2021, where one passes back and forth between the derivative `D_θ`
and a difference of values at `θ = 0` and `θ = π/2` (cf. `VanishTheta`).
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- **Fundamental theorem of calculus for `∂_θ`.**

If `g` is smooth on an open neighbourhood of the closed quadrant (so in
particular `θ ↦ g z θ` is smooth on an open interval containing `[0, π/2]`)
and `z ≥ 0`, then for every `θ ∈ [0, π/2]` the angular derivative
`s ↦ ∂_θ g z s = pth g z s` is continuous on `[0, θ]` and

`∫_0^θ ∂_θ g z s ds = g z θ - g z 0`.

The smoothness is obtained by restricting the two-variable smoothness of `g` to
the line `z = const` (`ContDiffOn.comp`), after which Mathlib's second
fundamental theorem of calculus for `C^1` functions
(`intervalIntegral.integral_deriv_of_contDiffOn_Icc`) applies on `[0, θ]`. -/
theorem pth_integral (g : ℝ → ℝ → ℝ) (z : ℝ) (hsm : Work.Spaces.SmoothNbhd g) (hz : 0 ≤ z) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (∫ s in (0 : ℝ)..θ, Work.Spaces.pth g z s = g z θ - g z 0) ∧
        ContinuousOn (fun s => Work.Spaces.pth g z s) (Set.Icc 0 θ) := by
  intro θ hθ
  obtain ⟨h0θ, hθpi⟩ := hθ
  -- `z` lies in the open left endpoint `-1` of the radial half-strip
  have hz1 : (-1 : ℝ) < z := by linarith
  -- the one-variable function `θ' ↦ g z θ'` is smooth on an open interval `U`
  -- containing the whole angular range `[0, π/2]`
  have hφU : ContDiffOn ℝ ⊤ (fun t : ℝ => g z t) (Set.Ioo (-1 : ℝ) (π/2 + 1)) := by
    have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1 : ℝ) (π/2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have h := hsm.comp hp (fun t ht => ⟨hz1, ht⟩)
    simpa [Function.comp_def, Function.uncurry] using h
  -- `[0, θ]` is contained in `U`
  have hsub : Set.Icc (0 : ℝ) θ ⊆ Set.Ioo (-1 : ℝ) (π/2 + 1) := by
    intro t ht
    refine ⟨by linarith [ht.1], ?_⟩
    have := Real.pi_pos
    linarith [ht.2]
  constructor
  · -- second fundamental theorem of calculus on `[0, θ]`
    have h := intervalIntegral.integral_deriv_of_contDiffOn_Icc (a := 0) (b := θ)
      ((hφU.of_le le_top).mono hsub) h0θ
    simpa [Work.Spaces.pth] using h
  · -- continuity of the derivative, from `C^∞` on the open set `U`
    have hcont : ContinuousOn (deriv (fun t : ℝ => g z t)) (Set.Icc 0 θ) :=
      (hφU.continuousOn_deriv_of_isOpen isOpen_Ioo le_top).mono hsub
    simpa [Work.Spaces.pth] using hcont

end Work.Spaces
