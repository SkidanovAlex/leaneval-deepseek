/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular "boundary layer" objects of the slice interior estimate

This module fixes the one-dimensional angular vocabulary used to prove
`Work.FTS.EllipticEst.sliceInteriorBound`, the *interior* (boundary-condition free) pointwise
bound for a slice `u` at the mid-angle `π/4`, in terms of the two weighted energies

  `Gη u = ∫_{Iθ} (u'')² sin(2θ)^{-η}`,   `Fη u = ∫_{Iθ} (Lzero1 u)² sin(2θ)^{-η}`.

The angular operator `Lzero1` annihilates `sin 2θ`; writing `u = sin 2θ · φ` its action becomes
*first order in `φ'`*, and the resulting first-order equation has the explicit solution

  `Φ(θ) := sin²θ · φ'(θ) = (2 cos³θ)⁻¹ ∫_θ^{π/2} sin σ cos²σ · (Lzero1 u)(σ) dσ`,

i.e. `Φ` is determined by the *data* `g = Lzero1 u` alone (`PhiG` below).  Consequently

  `u(π/4) = c + Ψ(π/4)`,  `u'(π/4) = 2 Φ(π/4)`,

with `Ψ θ = -∫_θ^{π/2} Φ_g σ / sin²σ dσ` (`PsiG` below) and a single free constant `c` — the
amplitude of the kernel direction `sin 2θ` — which is controlled by `Gη` alone.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.SliceLocal

set_option autoImplicit false

/-- The data-determined angular function `Φ_g`: for `g = Lzero1 u`,
`Φ_g θ = (2 cos³θ)⁻¹ ∫_θ^{π/2} sin σ cos²σ g σ dσ`.  It equals `sin²θ · ∂_θ(u / sin 2θ)` for
every slice `u` of the weak class (see `PhiOf` and `PhiOf_eq_PhiG`). -/
def PhiG (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (2 * (Real.cos θ) ^ 3)⁻¹ * ∫ σ in θ..(Real.pi / 2), Real.sin σ * (Real.cos σ) ^ 2 * g σ

/-- `Φ u θ = sin²θ · ∂_θ (u / sin 2θ)`, the angular function attached to a slice `u`. -/
def PhiOf (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (Real.sin θ) ^ 2 * deriv (fun t => u t / Real.sin (2 * t)) θ

/-- `Ψ_g θ = -∫_θ^{π/2} Φ_g σ / sin²σ dσ`: the `u`-part of the slice that is determined by the
data.  The full slice is `sin 2θ · (c + Ψ_g)` with a single constant `c ∈ ℝ`. -/
def PsiG (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -∫ σ in θ..(Real.pi / 2), PhiG g σ / (Real.sin σ) ^ 2

/-- `Q_g θ = sin 2θ · Ψ_g θ`, the data-determined part of the slice. -/
def QG (g : ℝ → ℝ) (θ : ℝ) : ℝ := Real.sin (2 * θ) * PsiG g θ

/-- The reciprocal of the angular weight is bounded by `1` on `Iθ` (so the weighted `L²` norm
dominates the `L¹` norm, with the endpoint values `sin(2θ) = 0` giving `sEta = 0`). -/
theorem sEta_inv_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.EllipticEst.sEta θ)⁻¹ ≤ 1 := by
  rcases eq_or_lt_of_le (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ) with h | h
  · have h0 : Work.FTS.EllipticEst.sEta θ = 0 := by
      rw [Work.FTS.EllipticEst.sEta, ← h, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
    rw [h0]; norm_num
  · have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have h1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [Work.FTS.EllipticEst.sEta]
      calc (1 : ℝ) = (1 : ℝ) ^ (-(Work.Spaces.eta)) := by rw [Real.one_rpow]
        _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            Real.rpow_le_rpow_of_nonpos h hle1 (by norm_num [Work.Spaces.eta])
    exact inv_le_one_of_one_le₀ h1

end Work.FTS.EllipticEst.SliceLocal
