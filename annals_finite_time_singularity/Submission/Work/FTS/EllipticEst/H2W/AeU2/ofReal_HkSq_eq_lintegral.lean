import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeU2

set_option autoImplicit false

/-! ## The collapse of the level-`0` integrand

At `k = 0` the second (mixed) sum of `Work.Spaces.HkIntegrand` is empty, so the integrand is the
single square `(g z θ · w z / sin(2θ)^{η/2})²`, whose weight square is `w z ^ 2 · sin(2θ)^{-η}`.
The angular factor is exactly `Work.FTS.EllipticEst.sEta`. -/

/-- **The level-`0` `ℋ^k`-integrand is a single weighted square.**  For `θ ∈ Iθ`,
`HkIntegrand α 0 g z θ = (w z)² · (g z θ)² · sEta θ`.  (The hypothesis `θ ∈ Iθ` is used only to
know `sin (2θ) ≥ 0`, so that `(sin(2θ)^{η/2})² = sin(2θ)^η`.) -/
theorem HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  -- the empty mixed sum, and the single `D_z`-slot at `i = 0`
  rw [show Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 by
    simp [Work.Spaces.HkIntegrand]]
  -- unfold the angular weight `sEta`
  rw [show Work.FTS.EllipticEst.sEta θ
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hη : (0 : ℝ) < Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hη2 : (0 : ℝ) < Work.Spaces.eta / 2 := by linarith
  -- `(sin(2θ)^{η/2})² = sin(2θ)^η`
  have h2 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h, Real.zero_rpow (ne_of_gt hη2), Real.zero_rpow (ne_of_gt hη)]
      norm_num
    · rw [sq, ← Real.rpow_add h (Work.Spaces.eta / 2) (Work.Spaces.eta / 2)]
      congr 1
      ring
  rw [mul_pow, div_pow, h2, div_eq_mul_inv, ← Real.rpow_neg hs]
  ring

/-- **`HkSq α 0 g` as a double `∫⁻` against the radial weight and `σ`.** -/
theorem ofReal_HkSq_eq_lintegral (α : ℝ) (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.HkMem α 0 g) :
    ENNReal.ofReal (Work.Spaces.HkSq α 0 g)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  -- Step 1: the outer Bochner integral over `Iz` is the `lintegral` of its `ofReal`
  -- (`HkSq` is the iterated Bochner integral of the nonnegative integrand `HkIntegrand`).
  have hboch : ENNReal.ofReal (Work.Spaces.HkSq α 0 g)
      = ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg.2
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)
  rw [hboch]
  -- Step 2: pointwise in `z ∈ Iz`, the inner Bochner integral is the `∫⁻` of the collapsed
  -- integrand, and the `z`-weight is a constant that comes out of the angular `∫⁻`.
  refine MeasureTheory.lintegral_congr_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_)
  have hnn_inner : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      fun θ => Work.Spaces.HkIntegrand α 0 g z θ :=
    Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ
  have hA : ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hg.1 z hz) hnn_inner
  have hB : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    MeasureTheory.lintegral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => by
        show ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ)
          = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ)
        rw [HkIntegrand_zero_eq α g hθ, ENNReal.ofReal_mul (sq_nonneg _)])
  have hC : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ))
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  show ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ)
  rw [hA, hB, hC]

end Work.FTS.EllipticEst.H2W.AeU2
