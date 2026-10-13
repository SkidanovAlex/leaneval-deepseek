/-
# `Work.StabilityFar.Decay.biotSavart_sub` — additivity of the Biot–Savart operator

The `C^{1,α}` far-field layer (`St4`) needs the Biot–Savart operator `Work.LWP.biotSavart` to be
*linear* in its vorticity argument.  This file proves the additive half of that linearity: for
two vorticity fields `f`, `g` which are almost everywhere strongly measurable, bounded by `M` and
supported in the closed ball `B(0,R)`,

  `BS(f - g) = BS(f) - BS(g)`   pointwise.

## The mathematics

`biotSavart ω x = (4π)⁻¹ • ∫ y, bsK ω x y` with integrand
`bsK ω x y = (‖x - y‖³)⁻¹ • (ω y × (x - y))`, which is linear in `ω`: the cross product is
additive in its first slot (`bsK_sub` below, a pointwise algebraic identity).

So the only content is the *integrability* of the integrand, which is what lets `integral_sub`
split the Bochner integral.  The support hypothesis makes `bsK ω x` vanish off `B(0,R)` and
dominate it there by `M · ‖x - y‖⁻²` (`Work.StabilityFar.Decay.norm_bsK_le_indicator`), and the
singular weight `‖x - y‖⁻²` is integrable over a ball of `ℝ³` — the borderline case
`2 < 3 = dim` (`Work.StabilityFar.Decay.integrable_indicator_inv_sq`, resting on the radial
computation `Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_le`).  No separation of `x` from
the support ball is needed: the singularity sits at the *centre* of the ball `B(x, ‖x‖ + R)`
containing `B(0,R)`, and the radial computation is finite there.

The hypothesis `0 ≤ R` is not used by the proof: for `R < 0` the support hypothesis is vacuous
and forces both fields to vanish.
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.StabilityFar.Defs
import Submission.Work.LWP.Defs
import Submission.Work.StabilityFar.Decay.norm_bsK_le_indicator
import Submission.Work.StabilityFar.Decay.integrable_indicator_inv_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped Topology ENNReal

namespace Work.StabilityFar.Decay

/-! ## Integrability of the Biot–Savart integrand -/

/-- For a vorticity `ω` that is ae-strongly-measurable, bounded by `M` and supported in the
closed ball `B(0,R)`, the Biot–Savart integrand `bsK ω x` is Bochner-integrable at every point
`x` — including the points *inside* the support ball, where the kernel `‖x - y‖⁻³` is singular.

The dominating function is `M · ‖x - y‖⁻²` on `B(0,R)`, which is integrable in `ℝ³`
(`integrable_indicator_inv_sq`), and the pointwise bound is `norm_bsK_le_indicator`. -/
lemma integrable_bsK_supported {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M) (hω : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) (x : R3) :
    Integrable (Work.LWP.BiotSavart.bsK ω x) volume :=
  Integrable.mono' (integrable_indicator_inv_sq x hM)
    (Work.LWP.BiotSavart.aestronglyMeasurable_bsK hmeas x)
    (Filter.Eventually.of_forall fun y => norm_bsK_le_indicator hM hω hsupp x y)

/-! ## Linearity of the integrand -/

/-- The Biot–Savart integrand is additive in the vorticity.  After unfolding the definitions this
is the additivity of the cross product in its first slot, transported through the scalar
multiplication by `(‖x - y‖³)⁻¹` and through `WithLp.toLp 2`. -/
lemma bsK_sub (f g : R3 → R3) (x y : R3) :
    Work.LWP.BiotSavart.bsK (f - g) x y
      = Work.LWP.BiotSavart.bsK f x y - Work.LWP.BiotSavart.bsK g x y := by
  simp only [Work.LWP.BiotSavart.bsK, Pi.sub_apply, WithLp.ofLp_sub, map_sub, LinearMap.sub_apply,
    smul_sub, WithLp.toLp_sub]
  abel

/-! ## Additivity of the Biot–Savart operator -/

/-- **Additivity of the Biot–Savart operator.**  `biotSavart` is `(4π)⁻¹` times the Bochner
integral of its integrand; the integrands of `BS(f - g)`, `BS f` and `BS g` differ pointwise by
`bsK_sub`, and the two integrals on the right may be split by `integral_sub` because both
integrands are integrable (`integrable_bsK_supported`).  Dividing the resulting identity by
`4π` is the final `smul_sub`. -/
theorem biotSavart_sub {f g : Work.StabilityFar.R3 → Work.StabilityFar.R3} {R M : ℝ} (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hf : ∀ y, ‖f y‖ ≤ M) (hg : ∀ y, ‖g y‖ ≤ M)
    (hfs : ∀ y, f y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hgs : ∀ y, g y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hfm : MeasureTheory.AEStronglyMeasurable f volume)
    (hgm : MeasureTheory.AEStronglyMeasurable g volume) (x : Work.StabilityFar.R3) :
    Work.LWP.biotSavart (f - g) x = Work.LWP.biotSavart f x - Work.LWP.biotSavart g x := by
  -- `hR` is not needed: it is recorded here only because the statement carries it.
  have _hR : (0 : ℝ) ≤ R := hR
  have hfi : Integrable (Work.LWP.BiotSavart.bsK f x) volume :=
    integrable_bsK_supported hM hf hfs hfm x
  have hgi : Integrable (Work.LWP.BiotSavart.bsK g x) volume :=
    integrable_bsK_supported hM hg hgs hgm x
  rw [Work.LWP.BiotSavart.biotSavart_apply, Work.LWP.BiotSavart.biotSavart_apply,
    Work.LWP.BiotSavart.biotSavart_apply]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => bsK_sub f g x y)]
  rw [MeasureTheory.integral_sub hfi hgi, smul_sub]

end Work.StabilityFar.Decay
