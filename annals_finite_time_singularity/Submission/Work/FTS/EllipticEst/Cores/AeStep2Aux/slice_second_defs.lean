/-
Copyright: work module for the Elgindi finite-time singularity project.

# The 1-D slice inequality `∫ sin(2θ)^{-η} f f'' ≤ 0`: definitions

This file fixes the notation for the leaf
`Cores.AeStep2Aux.slice_second_nonpos` and for the pieces it is assembled from.

Let `η = Work.Spaces.eta = 99/100`, `σ θ = sin(2θ)^{-η}`, `s = sin(2θ)`, `c = cos(2θ)`.

The whole proof rests on the **algebraic identity**

  `σ θ * (f θ * f'' θ) = (Phi f)' θ - Psi f θ`

where

  `Phi f θ = σ θ * f θ * f' θ - c * s^{-(1+η)} * f θ ^ 2`
  `Psi f θ = 2 * σ θ * f θ ^ 2 + (1 - η^2) * c^2 * s^{-(2+η)} * f θ ^ 2
              + s^{-(2+η)} * (f' θ * s - (1+η) * c * f θ)^2 ≥ 0`.

`Psi ≥ 0` is manifest.  With `J θ = f θ^2 / s θ`, `τ = -J'`, one has moreover

  `Phi f θ = s θ^{1-η} * J' θ / 2`
  `Psi f θ = s θ^{1-η} * τ θ^2 / (4 * J θ) + η * c * s θ^{-η} * τ θ
              + c^2 * s θ^{-(1+η)} * J θ + 2 * s θ^{1-η} * J θ`.

These are the identities that make the endpoint analysis go.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

set_option autoImplicit false

/-- The angular weight `σ θ = sin(2θ)^{-η}`. -/
def sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The angular weight with exponent `-(1+η)`: `sin(2θ)^{-(1+η)}`. -/
def sig1 (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))

/-- The angular weight with exponent `-(2+η)`: `sin(2θ)^{-(2+η)}`. -/
def sig2 (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))

/-- The boundary function `Phi f θ = σ θ * f θ * f' θ - cos(2θ) * sin(2θ)^{-(1+η)} * f θ^2`. -/
def Phi (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  sig θ * (f θ * deriv f θ) - Real.cos (2 * θ) * sig1 θ * (f θ) ^ 2

/-- The (nonnegative) bulk term `Psi f`. -/
def Psi (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  2 * sig θ * (f θ) ^ 2
    + (1 - Work.Spaces.eta ^ 2) * (Real.cos (2 * θ)) ^ 2 * sig2 θ * (f θ) ^ 2
    + sig2 θ * (deriv f θ * Real.sin (2 * θ) - (1 + Work.Spaces.eta) * Real.cos (2 * θ) * f θ) ^ 2

/-- The integrand `θ ↦ σ θ * (f θ * f'' θ)`. -/
def sliceIntegrand (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  sig θ * (f θ * deriv (deriv f) θ)

/-- `J θ = f θ^2 / sin(2θ)`. -/
def Jfun (f : ℝ → ℝ) (θ : ℝ) : ℝ := (f θ) ^ 2 / Real.sin (2 * θ)

theorem sig_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sig θ := by
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2]
  exact Real.rpow_pos_of_pos hs _

theorem sig1_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sig1 θ := by
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2]
  exact Real.rpow_pos_of_pos hs _

theorem sig2_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sig2 θ := by
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2]
  exact Real.rpow_pos_of_pos hs _

theorem one_sub_eta_sq_pos : (0 : ℝ) < 1 - Work.Spaces.eta ^ 2 := by
  rw [Work.Spaces.eta]; norm_num

theorem Psi_nonneg {f : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Psi f θ := by
  have h2 : (0:ℝ) < 1 - Work.Spaces.eta ^ 2 := one_sub_eta_sq_pos
  have h3 : (0:ℝ) < sig θ := sig_pos hθ
  have h4 : (0:ℝ) < sig2 θ := sig2_pos hθ
  have h5 : (0:ℝ) ≤ (f θ) ^ 2 := sq_nonneg _
  have h6 : (0:ℝ) ≤ (Real.cos (2 * θ)) ^ 2 := sq_nonneg _
  have h7 : (0:ℝ) ≤ (deriv f θ * Real.sin (2 * θ)
      - (1 + Work.Spaces.eta) * Real.cos (2 * θ) * f θ) ^ 2 := sq_nonneg _
  have hA : (0:ℝ) ≤ 2 * sig θ * (f θ) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt h3)) h5
  have hB : (0:ℝ) ≤ (1 - Work.Spaces.eta ^ 2) * (Real.cos (2 * θ)) ^ 2 * sig2 θ * (f θ) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt h2) h6) (le_of_lt h4)) h5
  have hC : (0:ℝ) ≤ sig2 θ * (deriv f θ * Real.sin (2 * θ)
      - (1 + Work.Spaces.eta) * Real.cos (2 * θ) * f θ) ^ 2 := mul_nonneg (le_of_lt h4) h7
  simp only [Psi]
  exact add_nonneg (add_nonneg hA hB) hC

end Work.FTS.EllipticEst.Cores.AeStep2Aux
