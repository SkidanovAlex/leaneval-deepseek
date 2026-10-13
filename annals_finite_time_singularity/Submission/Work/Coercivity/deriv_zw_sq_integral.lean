import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.pz_mul_w
import Submission.Work.Spaces.HardyZ

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

/-- The `z`-slice `z ↦ z (u(z,θ) w(z))²` is differentiable at every `x > 0`, with the
derivative `deriv` of itself.  This only uses the smoothness half of the hypothesis
`IBP u` (via `SmoothNbhd`), so that the fundamental theorem of calculus on `(0,∞)` can be
applied to it. -/
theorem hasDerivAt_zw_sq {u : ℝ → ℝ → ℝ} (hu : IBP u) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => z * (u z θ * Spaces.w z) ^ 2)
      (deriv (fun z => z * (u z θ * Spaces.w z) ^ 2) x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hu_d : HasDerivAt (fun z => u z θ) (Spaces.pz u x θ) x :=
    Spaces.hardyZ_hasDerivAt_slice u hu.smooth hθ hx1
  have hw_d : HasDerivAt Spaces.w (-2 * (1 + x) / x ^ 3) x := hasDerivAt_w hx0
  have huW : HasDerivAt (fun z => u z θ * Spaces.w z)
      (Spaces.pz u x θ * Spaces.w x + u x θ * (-2 * (1 + x) / x ^ 3)) x := hu_d.mul hw_d
  have h := (hasDerivAt_id x).mul (huW.pow 2)
  exact h.congr_deriv h.deriv.symm

/-- **The boundary term of the `z`-integration by parts of §6 vanishes identically in
integral form**: for `u` satisfying the analytic hypotheses `IBP` and every `θ ∈ Iθ`,
`∫_0^∞ ∂_z (z (u(z,θ) w(z))²) dz = 0`.

This is the fundamental theorem of calculus on `(0,∞)`: the integrand is the derivative of
`z ↦ z (u w)²`, which has limit `0` both at `z = 0⁺` and at `z = ∞` by the boundary
hypotheses `IBP.bd0`/`IBP.bdTop` of the hypothesis package. -/
theorem deriv_zw_sq_integral {u : ℝ → ℝ → ℝ} (hu : Work.Coercivity.IBP u) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ∫ z in Set.Ioi (0:ℝ), deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z = 0 := by
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun z => z * (u z θ * Spaces.w z) ^ 2)
        (deriv (fun z => z * (u z θ * Spaces.w z) ^ 2) x) x :=
    fun x hx => hasDerivAt_zw_sq hu hθ hx
  have hint : IntegrableOn (fun z => deriv (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) z)
      (Set.Ioi (0:ℝ)) := hu.intDeriv θ hθ
  have htop : Tendsto (fun z => z * (u z θ * Spaces.w z) ^ 2) atTop (𝓝 0) := hu.bdTop θ hθ
  -- Continuity of the boundary term at `0` from the one-sided limit `IBP.bd0`, the value
  -- at `0` being `0 * ... = 0`.
  have hcont : ContinuousWithinAt (fun z => z * (u z θ * Spaces.w z) ^ 2) (Set.Ici (0:ℝ)) 0 := by
    have h2 : Tendsto (fun z => z * (u z θ * Spaces.w z) ^ 2) (𝓝[{(0:ℝ)}] 0)
        (𝓝 (0 * (u 0 θ * Spaces.w 0) ^ 2)) := by
      rw [nhdsWithin_singleton]
      exact tendsto_pure_nhds _ 0
    have h1 : Tendsto (fun z => z * (u z θ * Spaces.w z) ^ 2) (𝓝[>] (0:ℝ))
        (𝓝 (0 * (u 0 θ * Spaces.w 0) ^ 2)) := by
      simpa using hu.bd0 θ hθ
    have h3 : Tendsto (fun z => z * (u z θ * Spaces.w z) ^ 2)
        (𝓝[>] (0:ℝ) ⊔ 𝓝[{(0:ℝ)}] 0) (𝓝 (0 * (u 0 θ * Spaces.w 0) ^ 2)) := h1.sup h2
    rw [nhdsGT_sup_nhdsWithin_singleton] at h3
    exact h3
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htop
  simpa using key

end Work.Coercivity
