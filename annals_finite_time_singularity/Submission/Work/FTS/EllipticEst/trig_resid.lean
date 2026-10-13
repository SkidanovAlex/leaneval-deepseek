import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- Elementary trigonometric residues used in the elliptic estimates: the three `L²` masses of
`sin (2θ)`, `cos (2θ)` and `2 cos (2θ)` on the angular interval `(0, π/2)`, together with the two
first-derivative identities for `sin (2θ)` and `2 cos (2θ)`.

The integrals are reduced by the affine substitution `θ ↦ 2θ` (`integral_comp_mul_left`) to the
Mathlib values `∫₀^π sin² = π/2` and `∫₀^π cos² = π/2`; the factor `2` inside `(2 cos (2θ))²` is
pulled out with `integral_const_mul`.  The derivatives are `HasDerivAt` computations (chain rule
applied to `Real.hasDerivAt_sin`/`Real.hasDerivAt_cos` composed with `θ ↦ 2θ`), converted to
`deriv` form. -/
theorem trig_resid :
    (∫ θ in (0:ℝ)..(Real.pi/2), (Real.sin (2*θ))^2 = Real.pi/4) ∧
    (∫ θ in (0:ℝ)..(Real.pi/2), (Real.cos (2*θ))^2 = Real.pi/4) ∧
    (∫ θ in (0:ℝ)..(Real.pi/2), (2*Real.cos (2*θ))^2 = Real.pi) ∧
    (∀ θ : ℝ, deriv (fun θ : ℝ => Real.sin (2*θ)) θ = 2*Real.cos (2*θ)) ∧
    (∀ θ : ℝ, deriv (fun θ : ℝ => 2*Real.cos (2*θ)) θ = -4*Real.sin (2*θ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `∫₀^{π/2} sin²(2θ) = π/4`
    rw [intervalIntegral.integral_comp_mul_left (f := fun x : ℝ => Real.sin x ^ 2)
      (by norm_num : (2:ℝ) ≠ 0)]
    rw [show (2:ℝ) * (Real.pi/2) = Real.pi by ring]
    simp [Real.sin_pi, Real.cos_pi]
    ring
  · -- `∫₀^{π/2} cos²(2θ) = π/4`
    rw [intervalIntegral.integral_comp_mul_left (f := fun x : ℝ => Real.cos x ^ 2)
      (by norm_num : (2:ℝ) ≠ 0)]
    rw [show (2:ℝ) * (Real.pi/2) = Real.pi by ring]
    simp [Real.sin_pi, Real.cos_pi]
    ring
  · -- `∫₀^{π/2} (2 cos (2θ))² = π`
    have h : (fun θ : ℝ => (2*Real.cos (2*θ))^2) = (fun θ : ℝ => 4 * (Real.cos (2*θ))^2) := by
      funext θ; ring
    rw [h, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_mul_left (f := fun x : ℝ => Real.cos x ^ 2)
      (by norm_num : (2:ℝ) ≠ 0)]
    rw [show (2:ℝ) * (Real.pi/2) = Real.pi by ring]
    simp [Real.sin_pi, Real.cos_pi]
    ring
  · -- `deriv (sin (2θ)) = 2 cos (2θ)`
    intro θ
    have hg : HasDerivAt (fun θ : ℝ => 2*θ) (2:ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    simpa [Function.comp_def, mul_comm] using
      ((Real.hasDerivAt_sin (2*θ)).comp θ hg).deriv
  · -- `deriv (2 cos (2θ)) = -4 sin (2θ)`
    intro θ
    have hg : HasDerivAt (fun θ : ℝ => 2*θ) (2:ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    have h1 : HasDerivAt (fun x : ℝ => Real.cos (2*x)) (-(Real.sin (2*θ)) * 2) θ := by
      simpa [Function.comp_def] using (Real.hasDerivAt_cos (2*θ)).comp θ hg
    have h2 : HasDerivAt (fun x : ℝ => 2*Real.cos (2*x)) (2 * (-(Real.sin (2*θ)) * 2)) θ :=
      h1.const_mul (2:ℝ)
    rw [h2.deriv]; ring

end Work.FTS.EllipticEst
