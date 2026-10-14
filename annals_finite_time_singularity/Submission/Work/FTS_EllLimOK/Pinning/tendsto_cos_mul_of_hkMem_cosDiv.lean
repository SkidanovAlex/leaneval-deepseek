import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.Pinning

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Pinning of `Ψ` at the corner `θ = π/2`

`Work.FTS_EllLimOK.Reconstruct` records the `θ`-reconstruction of a solution from the
coefficient `Vop Ψ = ∂_θΨ - tan θ · Ψ`: the identity

`cos θ · Vop Ψ z θ = ∂_θ (cos θ · Ψ z θ)`

shows that `cos θ · Vop Ψ` is the derivative of `θ ↦ cos θ · Ψ z θ`, so a bound
`|Vop Ψ| ≤ K` on the open quadrant makes that function `K`-Lipschitz there and gives the
*existence* of the corner value `lim_{θ → π/2⁻} cos θ · Ψ z θ`.

What the reconstruction deliberately does not supply — and what the pinning lemma below does —
is that this corner value *vanishes*.  That comes from the honest `ℋ⁰`-membership of
`Ψ / cos`: since `1/cos²` is not integrable at `π/2`, a non-zero limit would force
`∫ (Ψ z θ / cos θ)² = ∞` on a whole tail `(t, π/2)`.

The two analytic ingredients are delegated and live in this same directory:

* `Work.FTS.EllLimOK.Pinning.leftLimitOfBoundedDeriv` — `φ` with `|φ'| ≤ M` on a left
  neighbourhood of `x` has a finite left limit at `x`;
* `Work.FTS.EllLimOK.Pinning.tendsto_cos_mul_eq_zero_of_integrable_div_cos_sq` — a finite limit
  of `θ ↦ cos θ · f θ` at `π/2⁻` together with the integrability of `(f θ/cos θ)²` forces that
  limit to be `0`;
* `Work.FTS.EllLimOK.Pinning.integrableOn_div_cos_sq_of_HkMem` — `ℋ⁰`-membership of
  `Ψ z θ / cos θ` gives the plain square-integrability of the angular slice `(Ψ z ·/cos ·)²`.
-/


end Work.FTS_EllLimOK.Pinning
