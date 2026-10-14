import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Have
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.H1IP_upper =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.L2TransportSharp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The sharp projector bound -/


/-! ## The final numerical inequality -/

/-- `√58 · A · B ≤ A²/20 + 1000 B²` for `A, B ≥ 0`: with `A/√20` and `√290 B` this is
AM–GM, using `√58 = 2√290/√20`. -/
theorem sqrt58_amgm (A B : ℝ) (_hA : 0 ≤ A) (_hB : 0 ≤ B) :
    Real.sqrt 58 * A * B ≤ A ^ 2 / 20 + 1000 * B ^ 2 := by
  have h20 : Real.sqrt 20 ^ 2 = 20 := Real.sq_sqrt (by norm_num)
  have h20pos : 0 < Real.sqrt 20 := Real.sqrt_pos_of_pos (by norm_num)
  have h20ne : Real.sqrt 20 ≠ 0 := ne_of_gt h20pos
  have hsq : (2 * Real.sqrt 290 / Real.sqrt 20) ^ 2 = 58 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 290), h20]
    norm_num
  have hsqrt : Real.sqrt 58 = 2 * Real.sqrt 290 / Real.sqrt 20 := by
    rw [← hsq, Real.sqrt_sq (by positivity)]
  have hkey : 0 ≤ (A / Real.sqrt 20 - Real.sqrt 290 * B) ^ 2 := sq_nonneg _
  have hAM : 2 * (A / Real.sqrt 20) * (Real.sqrt 290 * B)
      ≤ (A / Real.sqrt 20) ^ 2 + (Real.sqrt 290 * B) ^ 2 := by nlinarith [hkey]
  have h1 : (A / Real.sqrt 20) ^ 2 = A ^ 2 / 20 := by rw [div_pow, h20]
  have h2 : (Real.sqrt 290 * B) ^ 2 = 290 * B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 290)]
  rw [h1, h2] at hAM
  have h3 : 2 * (A / Real.sqrt 20) * (Real.sqrt 290 * B) = Real.sqrt 58 * A * B := by
    rw [hsqrt]
    ring
  rw [h3] at hAM
  nlinarith [hAM, sq_nonneg B]

/-! ## The main theorem -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.bound_Z4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The product measure of the two restricted Lebesgue measures -/




/-! ## Auxiliary measure-theoretic lemmas -/





/-! ## Non-vanishing of the weights, a.e. -/








/-! ## Almost everywhere strong measurability of the ingredients -/






/-! ## The pointwise estimate for the `Z4` term -/




/-! ## Integrability of the dominating terms -/





/-! ## Almost everywhere strong measurability of the target integrand -/


/-! ## The main estimate -/


end

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.bound_Z5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The product measure of the two restricted Lebesgue measures -/




/-! ## The pointwise AM–GM inequality -/








/-! ## Almost-everywhere strong measurability of the ingredients -/






/-! ## The algebraic identity behind the integrand -/


/-! ## The main estimate -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.bound_Z7 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The product measure and the a.e. algebra of `f` and `D_z f` -/

















/-! ## The angular and radial one-dimensional bounds -/






/-! ## The pointwise AM-GM bound -/


/-! ## The main theorem -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.coerc_LZ6_Dz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.thetaDerivative =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- Congruence of `wip` in its first argument under an a.e. equality of the two
`(z,θ)`-functions, in the iterated-integral form adapted to `wip`. -/
theorem wip_congr_ae {ρ g₁ g₁' g₂ : ℝ → ℝ → ℝ}
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Spaces.Iθ), g₁ z θ = g₁' z θ) :
    wip ρ g₁ g₂ = wip ρ g₁' g₂ := by
  simp only [wip]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [h] with z hz
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hz] with θ hθ
  rw [hθ]


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Step.Coercive =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.CoercivityStep.Norm (HkAdm_mono)

namespace Work.FTS.CoercivityStep

set_option autoImplicit false





end Work.FTS.CoercivityStep
end
end
