import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.T1HardSlice
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `Work.H2.T1Q.SlotBoundQ` — the five top-order slots of the `ℋ⁴`-integrand at a fixed `z`

For `g` of class `SmoothQuad` with `HkMem α 4 g` and `z > 0`, the five top-order summands of the
`ℋ⁴`-integrand of `g` — the pure slot `(D_z⁴g)² sin(2θ)^{-η}` and the four mixed slots
`(D_z^jD_θ^ig)² sin(2θ)^{-γ}` with `i + j = 4`, `i ≥ 1` — are:

* integrable in `θ` on `Iθ` (the `η`-slot and each of the ten mixed slots with `1 ≤ i`,
  `i + j ≤ 4`), and
* their `w(z)²`-weighted `θ`-integral is bounded by `∫_θ HkIntegrand α 4 g z θ`.

The integrability comes from the summands of the (integrable) `ℋ⁴`-integrand
(`sq_le_HkIntegrand_z`, `sq_le_HkIntegrand_mixed`); the inequality is the pointwise comparison
`HkIntegrandSlotSum` together with the two squaring identities `slotQ_whz_sq` and `slotQ_wt_sq`
for the weights `w/sin(2θ)^{η/2}` and `W = w·sin(2θ)^{-γ/2}`.  No positivity hypothesis on `α` is
needed: both squaring identities are pure `rpow` algebra on the nonnegative base `sin(2θ)`.
-/

/-! ## Squaring the two weights of `HkIntegrand` -/

/-- `(a^p)^2 = a^(p*2)` for a nonnegative base (the `rpow` form of `mul_pow` for a real
exponent). -/
theorem slotQ_rpow_sq_two {a : ℝ} (ha : 0 ≤ a) (p : ℝ) : (a ^ p) ^ 2 = a ^ (p * 2) := by
  rw [← Real.rpow_natCast (a ^ p) 2]
  exact (Real.rpow_mul ha p 2).symm

/-- Squaring the weight `w(z)/sin(2θ)^{η/2}` of the pure `D_z`-slots. -/
theorem slotQ_whz_sq (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  have ha : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  rw [div_eq_mul_inv, ← Real.rpow_neg ha (Work.Spaces.eta / 2), mul_pow,
    slotQ_rpow_sq_two ha (-(Work.Spaces.eta / 2)),
    show (-(Work.Spaces.eta / 2)) * 2 = -Work.Spaces.eta by ring]

/-- Squaring the mixed weight `W = Wt α = w·sin(2θ)^{-γ/2}`. -/
theorem slotQ_wt_sq (α z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have ha : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  have hW : Work.Spaces.Wt α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  rw [hW, mul_pow, slotQ_rpow_sq_two ha (-(Work.Spaces.gam α / 2)),
    show (-(Work.Spaces.gam α / 2)) * 2 = -(Work.Spaces.gam α) by ring]

/-! ## The pointwise slot inequality -/


/-! ## Continuity and almost-everywhere strong measurability of the pure slot -/





/-! ## The target -/


end Work.H2.T1Q
