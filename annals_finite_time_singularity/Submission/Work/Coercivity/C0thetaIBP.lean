import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.Coercivity.C0Defs
import Submission.Work.Coercivity.C0h_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- `C0h` has derivative `C0g` everywhere (i.e. `C0g = C0h'`); from `C0h_deriv`. -/
theorem C0h_hasDerivAt (θ : ℝ) : HasDerivAt C0h (C0g θ) θ := by
  rw [← C0h_deriv]
  show HasDerivAt C0h (deriv C0h θ) θ
  rw [hasDerivAt_deriv_iff]
  show DifferentiableAt ℝ C0h θ
  unfold C0h Spaces.K
  fun_prop

/-- `C0h` vanishes at the two endpoints of `Iθ = [0, π/2]`. -/
theorem C0h_zero : C0h 0 = 0 ∧ C0h (π / 2) = 0 := by
  constructor
  · simp [C0h, Spaces.K]
  · rw [C0h, Spaces.K]
    have h2 : 2 * (π / 2) = π := by ring
    rw [h2, Real.sin_pi]
    ring

/-- **Angular integration by parts.** For `g` differentiable on `[0, π/2]` with
interval-integrable derivative `g'`,
  `∫_{Iθ} C0h · g' = -∫_{Iθ} C0g · g`,
the boundary terms being killed by `C0h 0 = C0h (π/2) = 0`. -/
theorem C0thetaIBP (g g' : ℝ → ℝ)
    (hg : ∀ θ ∈ Set.Icc 0 (π / 2), HasDerivAt g (g' θ) θ)
    (hg' : IntervalIntegrable g' volume 0 (π / 2)) :
    ∫ θ in Spaces.Iθ, C0h θ * g' θ = -(∫ θ in Spaces.Iθ, C0g θ * g θ) := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  -- replace the set integral over `Iθ = Icc 0 (π/2)` by the interval integral over `0..π/2`
  have hIcc : ∀ f : ℝ → ℝ, ∫ θ in Spaces.Iθ, f θ = ∫ θ in (0 : ℝ)..(π / 2), f θ := by
    intro f
    rw [show Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
        MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [hIcc (fun θ => C0h θ * g' θ)]
  rw [hIcc (fun θ => C0g θ * g θ)]
  -- integration by parts
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) (π / 2), HasDerivAt C0h (C0g x) x :=
    fun x _ => C0h_hasDerivAt x
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) (π / 2), HasDerivAt g (g' x) x := by
    rw [Set.uIcc_of_le hle]
    exact hg
  have hcont : Continuous C0g := by
    unfold C0g
    fun_prop
  have hu' : IntervalIntegrable C0g volume 0 (π / 2) := hcont.intervalIntegrable 0 (π / 2)
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hg'
  rw [hIBP, C0h_zero.1, C0h_zero.2]
  ring

end Work.Coercivity
