/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary for the open-class angular Agmon inequality `sliceAgmonOpenCore`

`sliceAgmonOpenCore` is the one-dimensional (angular) weighted Agmon estimate

  `c ∫_{Iθ} (f')² σ  ≤  - ∫_{Iθ} f f'' σ + C ∫_{Iθ} f² σ`,   `σ = thEta = sin(2θ)^{-η}`,

for `f` of class `C²` on the **open** interval `(0, π/2)` whose two traces vanish and whose
three weighted energies are finite.  This is the open-class companion of
`Work.EllipticEst.Core.thetaAgmonCompact` (which asks the function to be `C²` on the closed
interval and to vanish off a compact sub-interval of `(0, π/2)`).

The proof (see `NOTES_sliceAgmonOpenCore.md`) runs through the two quantities defined here:

* `Phi f θ = f θ · f' θ · σ θ + (η/2) f θ² · (s'/s)(θ) · σ θ` is the primitive whose derivative
  is `(f')²σ + f f'' σ - 2η f² σ - 2η(1+η) f² cos²(2θ) sin(2θ)^{-(2+η)}`  (the exact
  sub-interval integration by parts, `thetaInterpIBPSub`, in primitive form);
* `rho f θ = f θ · sin(2θ)^{-(1+η)/2}` is the flat variable in which the **sharp** Hardy step
  becomes an algebraic identity:

  `∫_a^b (f')² σ = ∫_a^b sin(2θ) (ρ')² + (1+η)² ∫_a^b f² sin(2θ)^{-(2+η)} + (1-η²) ∫_a^b f²σ
      + ((1+η)/2) [ sin(2θ) ρ² ]_a^b`,

so that dropping the non-negative first term and letting `a → 0`, `b → π/2` gives the sharp
inequality `(1+η)² ∫ f² sin(2θ)^{-(2+η)} ≤ ∫ (f')²σ` — with the constant `1/(1+η)²` that the
proof of the main theorem needs (`2η/(1+η) < 1`).

Also defined: `beta f θ = f θ² sin(2θ)^{η}`, which satisfies `beta' = 2 sin(2θ)^{2η} · Phi` and
vanishes at both endpoints; this is what forces `Phi(0⁺) ≥ 0 ≥ Phi((π/2)⁻)` and hence the
vanishing of the boundary terms of the integration by parts.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

/-- The flat angular variable `ρ = f · sin(2θ)^{-(1+η)/2}`. -/
def rho (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  f θ * (Real.sin (2 * θ)) ^ (-((1 + Work.Spaces.eta) / 2))

/-- The primitive of the weighted `θ`-integration by parts:
`Φ = f f' σ + (η/2) f² (s'/s) σ` with `s = sin(2θ)`, `σ = s^{-η}`. -/
def Phi (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  f θ * deriv f θ * Work.FTS.EllipticEst.thEta θ
    + (Work.Spaces.eta / 2) * (f θ) ^ 2 * (2 * Real.cos (2 * θ))
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))

/-- `β = f² sin(2θ)^{η}`; its derivative is `2 sin(2θ)^{2η} · Φ`. -/
def beta (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)

theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem thEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ := Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- `rho² = f² sin(2θ)^{-(1+η)}`. -/
theorem rho_sq (f : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (rho f θ) ^ 2 = (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
  have hs := sin_two_pos hθ
  have h2 : ((Real.sin (2 * θ)) ^ (-((1 + Work.Spaces.eta) / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    push_cast
    ring
  rw [rho, mul_pow, h2]

/-- `beta = rho² · sin(2θ)^{1+2η}`. -/
theorem beta_eq (f : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    beta f θ = (rho f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 + 2 * Work.Spaces.eta) := by
  have hs := sin_two_pos hθ
  rw [beta, rho_sq f hθ, mul_assoc, ← Real.rpow_add hs]
  congr 1
  ring

/-- The defining identity of the primitive: `Φ = f f' σ + (η/2) f² (s'/s) σ` written with
`cot` in place of `s'/s`. -/
theorem Phi_eq_cot (f : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Phi f θ = f θ * deriv f θ * Work.FTS.EllipticEst.thEta θ
      + Work.Spaces.eta * (f θ) ^ 2 * Real.cot (2 * θ) * Work.FTS.EllipticEst.thEta θ := by
  have hs := sin_two_pos hθ
  have h1 : (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / Real.sin (2 * θ) := by
    rw [show -(1 + Work.Spaces.eta) = -(Work.Spaces.eta) + (-1) by ring,
      Real.rpow_add hs, Real.rpow_neg_one]
    ring
  rw [Phi, Real.cot_eq_cos_div_sin, h1]
  simp only [Work.FTS.EllipticEst.thEta]
  field_simp

end Work.EllipticEst.Core.i0Aux
