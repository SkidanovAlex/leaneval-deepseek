/-
# The auxiliary quantities `σ`, `D₁`, `θ₁`, `N₁` for the `K_+^{(8)}` cusp decay

This file sets up the algebraic rearrangement of `K_+^{(8)}` used in
`Work.Asymptotics.CuspDecay.KPlusEightBound`.

Notation: `z` is the "cusp" variable and `σ = S•z = -1/z` its `S`-image.  Writing
`e₂,e₄,e₆ = E₂,E₄,E₆` at `τ` and `ẽ₂,ẽ₄,ẽ₆ = E₂,E₄,E₆` at `σ`, `Δ = Δ(τ)`, `Δ̃ = Δ(σ)`,
the CKMRV decomposition of `K_+^{(8)}` (Theorem 4.9, section 4.4) is equivalent, after
using `E₄(z) = z⁻⁴ẽ₄`, `E₆(z) = z⁻⁶ẽ₆`, `E_{2}|₂S(z) = z⁻²ẽ₂`, `Δ(z) = z⁻¹²Δ̃` and
`E₈ = E₄²`, `E₁₀ = E₄E₆`, `E₁₄ = E₄²E₆`, to

  `36π⁻² i · K_+^{(8)}(τ,z) = z² N₁/D₁`,

where

  `D₁ = Δ̃ e₄³ - Δ e₄(σ)³`  and  `N₁ = (τe₆ - 2φ₀e₄) D₁ + φ₂e₄²e₆Δ̃ + Δ θ₁`,
  `θ₁ = τ e₆ ẽ₄²ẽ₂² - 2φ₀e₄ ẽ₄ẽ₆ẽ₂`.

The point of the grouping is that both `N₁` and `D₁` vanish at the coincidence
`τ = σ` (`j τ = j z`), and that `N₁` is *doubly* small:
`N₁ = Δ̃ e₄² P + Δ Q` with `P = (τe₆-2φ₀e₄)e₄ + φ₂e₆` (small because it vanishes at
`e₂ = e₄ = e₆ = 1`, the cusp `τ → i∞`) and `Q = θ₁ - (τe₆-2φ₀e₄)ẽ₄³` (small because it
vanishes at `ẽ₂ = ẽ₄ = ẽ₆ = 1`, the cusp `z → i0`).
-/
import Mathlib
import Submission.Work.Asymptotics.Xi8_eq
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Rigidity.Basic

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics.CuspDecay

open Work.Kernels

/-- `σ = S•z = -1/z`, the `S`-image of `z`. -/
def sg (z : UpperHalfPlane) : UpperHalfPlane := ModularGroup.S • z

lemma sg_coe (z : UpperHalfPlane) : ((sg z : UpperHalfPlane) : ℂ) = -1 / (z : ℂ) := by
  rw [sg, Work.Rigidity.coe_S_smul]
  ring

lemma jInvariantFun_sg (z : UpperHalfPlane) :
    jInvariantFun (sg z) = jInvariantFun z := by
  rw [sg]; exact Work.Kernels.KernelFacts.jInvariantFun_S_smul z

/-- `D₁(τ,z) = Δ(σ)E₄(τ)³ - Δ(τ)E₄(σ)³`, the "denominator" of the regrouped kernel. -/
def DOne (τ z : UpperHalfPlane) : ℂ :=
  DeltaFun (sg z) * E4Fun τ ^ 3 - DeltaFun τ * E4Fun (sg z) ^ 3

/-- `θ₁(τ,z) = τE₆(τ)E₄(σ)²E₂(σ)² - 2φ₀(τ)E₄(τ)E₄(σ)E₆(σ)E₂(σ)`. -/
def thetaOne (τ z : UpperHalfPlane) : ℂ :=
  (τ : ℂ) * E6Fun τ * E4Fun (sg z) ^ 2 * E2Fun (sg z) ^ 2
    - 2 * phi0 τ * E4Fun τ * E4Fun (sg z) * E6Fun (sg z) * E2Fun (sg z)

/-- `N₁(τ,z) = (τE₆(τ) - 2φ₀(τ)E₄(τ))D₁ + φ₂(τ)E₄(τ)²E₆(τ)Δ(σ) + Δ(τ)θ₁(τ,z)`. -/
def NOne (τ z : UpperHalfPlane) : ℂ :=
  ((τ : ℂ) * E6Fun τ - 2 * phi0 τ * E4Fun τ) * DOne τ z
    + phi2 τ * E4Fun τ ^ 2 * E6Fun τ * DeltaFun (sg z)
    + DeltaFun τ * thetaOne τ z

/-- The `τ`-side factor `P = (τe₆-2φ₀e₄)e₄ + φ₂e₆` of `N₁`. -/
def PFac (τ : UpperHalfPlane) : ℂ :=
  ((τ : ℂ) * E6Fun τ - 2 * phi0 τ * E4Fun τ) * E4Fun τ + phi2 τ * E6Fun τ

/-- The crossed factor `Q = θ₁ - (τe₆-2φ₀e₄)E₄(σ)³` of `N₁`. -/
def QFac (τ z : UpperHalfPlane) : ℂ :=
  thetaOne τ z - ((τ : ℂ) * E6Fun τ - 2 * phi0 τ * E4Fun τ) * E4Fun (sg z) ^ 3

end Work.Asymptotics.CuspDecay
