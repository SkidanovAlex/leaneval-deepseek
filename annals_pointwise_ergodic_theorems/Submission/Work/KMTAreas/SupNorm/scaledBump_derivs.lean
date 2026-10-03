/-
# Derivatives of the rescaled KMT cutoff

For `x₀ δ : ℝ` the *rescaled cutoff* is `scaledBump x₀ δ = fun ξ ↦ η((ξ - x₀)/δ)`, where
`η = Work.KMTContract.kmtEta`.  This file records the two chain-rule identities

* `scaledBump_deriv` — `(scaledBump x₀ δ)' ξ = (1/δ) · η'((ξ - x₀)/δ)`;
* `scaledBump_iteratedDeriv_two` — `(scaledBump x₀ δ)'' ξ = (1/δ²) · η''((ξ - x₀)/δ)`,

as equalities of functions (no hypothesis on `δ`: for `δ = 0` both sides are the junk value `0`).
They are the inputs of the pointwise/`L¹` analysis of the `SupNorm` area; the `L¹` norms of the
scaled bump and its first two derivatives are `δ ηI0`, `ηI1`, `ηI2/δ`.
-/
import Mathlib
import Submission.Work.KMTAreas.SupNorm.WavePacket

set_option autoImplicit false

open MeasureTheory

namespace Work.KMTAreas.SupNorm

open Work.KMTContract

/-- First derivative of the rescaled cutoff. -/
theorem scaledBump_deriv (x₀ δ : ℝ) :
    deriv (scaledBump x₀ δ)
      = fun ξ : ℝ => ((1 / δ : ℝ) : ℂ) * deriv kmtEta ((ξ - x₀) / δ) := by
  funext ξ
  change deriv (fun ξ : ℝ => kmtEta ((ξ - x₀) / δ)) ξ = _
  set F : ℝ → ℂ := fun u => kmtEta (u / δ) with hF
  have hfun : (fun ξ : ℝ => kmtEta ((ξ - x₀) / δ)) = fun ξ : ℝ => F (ξ - x₀) := by
    funext ξ; rw [hF]
  rw [hfun, deriv_comp_sub_const]
  rw [show F = fun u : ℝ => kmtEta ((1 / δ) * u) from by
        funext u; rw [hF]; ring_nf,
      deriv_comp_mul_left, Complex.real_smul,
      show (1 / δ) * (ξ - x₀) = (ξ - x₀) / δ from by ring]

/-- Second derivative of the rescaled cutoff. -/
theorem scaledBump_iteratedDeriv_two (x₀ δ : ℝ) :
    iteratedDeriv 2 (scaledBump x₀ δ)
      = fun ξ : ℝ => ((1 / δ ^ 2 : ℝ) : ℂ) * iteratedDeriv 2 kmtEta ((ξ - x₀) / δ) := by
  funext ξ
  change iteratedDeriv 2 (fun ξ : ℝ => kmtEta ((ξ - x₀) / δ)) ξ = _
  have h2 : ContDiff ℝ 2 kmtEta :=
    Work.KMTAreas.A7.etaMult_kmtEta_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
  set F : ℝ → ℂ := fun u => kmtEta (u / δ) with hF
  have hfun : (fun ξ : ℝ => kmtEta ((ξ - x₀) / δ)) = fun ξ : ℝ => F (ξ - x₀) := by
    funext ξ; rw [hF]
  rw [hfun, iteratedDeriv_comp_sub_const]
  change iteratedDeriv 2 F (ξ - x₀) = _
  have hF2 : iteratedDeriv 2 F
      = fun u : ℝ => (1 / δ) ^ 2 • iteratedDeriv 2 kmtEta ((1 / δ) * u) := by
    rw [hF]
    rw [show (fun u : ℝ => kmtEta (u / δ)) = fun u : ℝ => kmtEta ((1 / δ) * u) from by
          funext u; ring_nf]
    exact iteratedDeriv_comp_const_smul h2 (1 / δ)
  rw [hF2]
  change (1 / δ) ^ 2 • iteratedDeriv 2 kmtEta ((1 / δ) * (ξ - x₀)) = _
  rw [Complex.real_smul, show (1 / δ) * (ξ - x₀) = (ξ - x₀) / δ from by ring]
  congr 1
  ring_nf

end Work.KMTAreas.SupNorm
