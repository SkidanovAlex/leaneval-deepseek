import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.BiotSavart.norm_bsField_diff_bound
import Submission.Work.CoreResiduals.BiotSavart.setIntegral_norm_sub_rpow_le
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_holder_le_sup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric
open scoped Topology
open Work.StabilityFar.Decay (kf kDerivCLM crossL)

/-- **The order-`(-1)` estimates for the Biot–Savart operator, with constants uniform over all bounded supported fields.**

For a field `h` with `‖h‖_∞ ≤ G` supported in `closedBall 0 R` (`R > 0`) and ae-strongly-measurable,
and `0 < α < 1`, there is `K ≥ 0` depending only on `α, R, R'` with

`‖BS h x‖ ≤ K * G` and `‖BS h x - BS h y‖ ≤ K * G * ‖x - y‖^α` for all `x, y` with `‖x‖, ‖y‖ ≤ R'`.

No regularity of `h` beyond boundedness/measurability is needed: the kernel `kf b = ‖b‖⁻³ • b` has
`‖kf b‖ = ‖b‖⁻²`, locally integrable in `ℝ³` (`∫_{B(0,R)}‖x-a‖⁻² ≤ 4π(R+R')` uniformly for `‖x‖ ≤ R'`),
and the difference estimate is the classical `δ log(1/δ) ≤ C(α) δ^α` for `0 < α < 1`
(`‖kf (x-a) - kf (y-a)‖ ≤ min(2‖x-a‖⁻², ‖x-y‖ sup ‖D kf‖)`). -/
theorem biotSavart_holder_le_sup {R R' α : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : Work.LWP.R3 → Work.LWP.R3) (G : ℝ), 0 ≤ G →
      (∀ a, ‖h a‖ ≤ G) → (∀ a, h a ≠ 0 → a ∈ Metric.closedBall 0 R) →
      MeasureTheory.AEStronglyMeasurable h MeasureTheory.volume →
      (∀ x : Work.LWP.R3, ‖x‖ ≤ R' → ‖Work.LWP.biotSavart h x‖ ≤ K * G) ∧
      (∀ x y : Work.LWP.R3, ‖x‖ ≤ R' → ‖y‖ ≤ R' →
        ‖Work.LWP.biotSavart h x - Work.LWP.biotSavart h y‖ ≤ K * G * ‖x - y‖ ^ α) := by
  -- the pointwise Hölder bound for the Newtonian kernel `kf` (order `-2`, exponent `-2-α`)
  obtain ⟨Ck, hCk0, hCk⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : Work.LWP.R3,
      ‖kf p - kf q‖ ≤ C * ‖p - q‖ ^ α * (‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α)) :=
    kf_sub_le_rpow hα hα1
  -- the order-`(-1)` sup-norm bound (uniform, explicit constant)
  have hsup_lem : ∀ (ω : Work.LWP.R3 → Work.LWP.R3) (M : ℝ), 0 ≤ M → (∀ a, ‖ω a‖ ≤ M) →
      (∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R) →
      MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume → ∀ x : Work.LWP.R3,
      ‖Work.LWP.biotSavart ω x‖ ≤ M * (‖x‖ + R + 1) :=
    fun ω M hM hb hs hm x => biotSavart_norm_le_of_bounded_supported hR hM hb hs hm x
  -- the sub-critical radial weight integrated over `closedBall 0 R`
  have hrad_lem : ∀ z : Work.LWP.R3,
      ∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖z - a‖ ^ (-2 - α)
        ≤ 4 * Real.pi * (‖z‖ + R + 1) ^ (1 - α) / (1 - α) :=
    fun z => setIntegral_norm_sub_rpow_le hR hα1 z
  rcases lt_or_ge R' 0 with hR'neg | hR'nn
  · refine ⟨0, le_refl 0, fun h G hG hbdd hsupp hm => ⟨?_, ?_⟩⟩
    · intro x hx
      have h1 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
      linarith
    · intro x y hx hy
      have h1 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
      linarith
  set ρ : ℝ := R' + R + 1 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hαlt : 0 < 1 - α := by linarith
  have hρpow : 0 ≤ ρ ^ (1 - α) := Real.rpow_nonneg hρpos.le _
  have hTnn : 0 ≤ (2 * Ck * ρ ^ (1 - α)) / (1 - α) := by positivity
  set K : ℝ := 2 * ρ + (2 * Ck * ρ ^ (1 - α)) / (1 - α) + 1 with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; linarith
  have hK1 : ρ ≤ K := by rw [hKdef]; linarith
  have hK2 : 2 * ρ ≤ K := by rw [hKdef]; linarith
  have hK3 : 2 * Ck * ρ ^ (1 - α) / (1 - α) ≤ K := by rw [hKdef]; linarith
  refine ⟨K, hKnn, ?_⟩
  intro h G hG hbdd hsupp hm
  constructor
  · -- the sup-norm bound
    intro x hx
    have h1 : ‖Work.LWP.biotSavart h x‖ ≤ G * (‖x‖ + R + 1) :=
      hsup_lem h G hG hbdd hsupp hm x
    have h2 : ‖x‖ + R + 1 ≤ ρ := by rw [hρdef]; linarith
    calc ‖Work.LWP.biotSavart h x‖ ≤ G * (‖x‖ + R + 1) := h1
      _ ≤ G * ρ := by gcongr
      _ ≤ K * G := by
          have h3 : G * ρ = ρ * G := by ring
          rw [h3]
          exact mul_le_mul_of_nonneg_right hK1 hG
  · -- the Hölder bound
    intro x y hx hy
    by_cases hxy : x = y
    · subst hxy
      rw [sub_self, norm_zero, sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero]
    have hδpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    rcases lt_or_ge 1 ‖x - y‖ with hδ1 | hδ1
    · -- far field: both sup bounds and `‖x-y‖^α ≥ 1`
      have h1 : ‖Work.LWP.biotSavart h x‖ ≤ G * (‖x‖ + R + 1) :=
        hsup_lem h G hG hbdd hsupp hm x
      have h2 : ‖Work.LWP.biotSavart h y‖ ≤ G * (‖y‖ + R + 1) :=
        hsup_lem h G hG hbdd hsupp hm y
      have hxρ : ‖x‖ + R + 1 ≤ ρ := by rw [hρdef]; linarith
      have hyρ : ‖y‖ + R + 1 ≤ ρ := by rw [hρdef]; linarith
      have hone : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow (le_of_lt hδ1) hα.le
      have hKG : 0 ≤ K * G := mul_nonneg hKnn hG
      calc ‖Work.LWP.biotSavart h x - Work.LWP.biotSavart h y‖
          ≤ ‖Work.LWP.biotSavart h x‖ + ‖Work.LWP.biotSavart h y‖ := norm_sub_le _ _
        _ ≤ G * (‖x‖ + R + 1) + G * (‖y‖ + R + 1) := add_le_add h1 h2
        _ ≤ G * ρ + G * ρ := by
            exact add_le_add (mul_le_mul_of_nonneg_left hxρ hG)
              (mul_le_mul_of_nonneg_left hyρ hG)
        _ = (2 * ρ) * G := by ring
        _ ≤ K * G := mul_le_mul_of_nonneg_right hK2 hG
        _ = K * G * 1 := (mul_one _).symm
        _ ≤ K * G * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hone hKG
    · -- near field: integrate the kernel difference
      have hsub : Metric.closedBall (0 : Work.LWP.R3) R ⊆ Metric.ball (0 : Work.LWP.R3) (R + 1) := by
        intro a ha
        rw [Metric.mem_closedBall, dist_zero_right] at ha
        rw [Metric.mem_ball, dist_zero_right]
        linarith
      have hIx : IntegrableOn (fun a : Work.LWP.R3 => ‖x - a‖ ^ (-2 - α))
          (Metric.closedBall (0 : Work.LWP.R3) R) volume :=
        (integrableOn_norm_sub_rpow_ball_origin x (-2 - α) (by linarith) (R + 1)).mono_set hsub
      have hIy : IntegrableOn (fun a : Work.LWP.R3 => ‖y - a‖ ^ (-2 - α))
          (Metric.closedBall (0 : Work.LWP.R3) R) volume :=
        (integrableOn_norm_sub_rpow_ball_origin y (-2 - α) (by linarith) (R + 1)).mono_set hsub
      have hS : MeasurableSet (Metric.closedBall (0 : Work.LWP.R3) R) :=
        Metric.isClosed_closedBall.measurableSet
      have hcle : ∀ z : Work.LWP.R3, ‖z‖ ≤ R' →
          ∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖z - a‖ ^ (-2 - α)
            ≤ 4 * Real.pi * ρ ^ (1 - α) / (1 - α) := by
        intro z hz
        refine (hrad_lem z).trans ?_
        have h1 : ‖z‖ + R + 1 ≤ ρ := by rw [hρdef]; linarith
        have h2 : (‖z‖ + R + 1) ^ (1 - α) ≤ ρ ^ (1 - α) :=
          Real.rpow_le_rpow (by positivity) h1 hαlt.le
        calc 4 * Real.pi * (‖z‖ + R + 1) ^ (1 - α) / (1 - α)
            = 4 * Real.pi * ((‖z‖ + R + 1) ^ (1 - α) / (1 - α)) := by ring
          _ ≤ 4 * Real.pi * (ρ ^ (1 - α) / (1 - α)) :=
              mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right h2 hαlt.le)
                (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
          _ = 4 * Real.pi * ρ ^ (1 - α) / (1 - α) := by ring
      have hbk : ∀ a, Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a
          = crossL (h a) (kf (x - a) - kf (y - a)) := by
        intro a
        rw [Work.StabilityFar.Decay.bsK_eq_crossL, Work.StabilityFar.Decay.bsK_eq_crossL]
        exact (ContinuousLinearMap.map_sub (crossL (h a)) (kf (x - a)) (kf (y - a))).symm
      have hpt : ∀ a : Work.LWP.R3, ‖crossL (h a) (kf (x - a) - kf (y - a))‖
          ≤ Ck * ‖x - y‖ ^ α * G * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α)) := by
        intro a
        have h1 : ‖crossL (h a) (kf (x - a) - kf (y - a))‖
            ≤ ‖h a‖ * ‖kf (x - a) - kf (y - a)‖ := by
          calc ‖crossL (h a) (kf (x - a) - kf (y - a))‖
              ≤ ‖crossL (h a)‖ * ‖kf (x - a) - kf (y - a)‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ ‖h a‖ * ‖kf (x - a) - kf (y - a)‖ :=
                mul_le_mul_of_nonneg_right (Work.StabilityFar.Decay.norm_crossL_le _)
                  (norm_nonneg _)
        have h2 := hCk (x - a) (y - a)
        have h3 : ‖(x - a) - (y - a)‖ = ‖x - y‖ := by
          rw [show (x - a) - (y - a) = x - y by abel]
        rw [h3] at h2
        have h4 : ‖h a‖ * ‖kf (x - a) - kf (y - a)‖
            ≤ G * (Ck * ‖x - y‖ ^ α * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α))) :=
          mul_le_mul (hbdd a) h2 (norm_nonneg _) hG
        calc ‖crossL (h a) (kf (x - a) - kf (y - a))‖
            ≤ ‖h a‖ * ‖kf (x - a) - kf (y - a)‖ := h1
          _ ≤ G * (Ck * ‖x - y‖ ^ α * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α))) := h4
          _ = Ck * ‖x - y‖ ^ α * G * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α)) := by ring
      have hmaj : IntegrableOn (fun a : Work.LWP.R3 =>
          Ck * ‖x - y‖ ^ α * G * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α)))
          (Metric.closedBall (0 : Work.LWP.R3) R) volume :=
        (hIx.add hIy).const_mul (Ck * ‖x - y‖ ^ α * G)
      have hFint : Integrable (Work.LWP.BiotSavart.bsK h x) volume :=
        Work.StabilityFar.Decay.integrable_bsK_supported hG hbdd hsupp hm x
      have hGint : Integrable (Work.LWP.BiotSavart.bsK h y) volume :=
        Work.StabilityFar.Decay.integrable_bsK_supported hG hbdd hsupp hm y
      have hdiff : Work.LWP.biotSavart h x - Work.LWP.biotSavart h y
          = (4 * Real.pi)⁻¹ •
              ∫ a, (Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a) := by
        rw [Work.LWP.BiotSavart.biotSavart_apply, Work.LWP.BiotSavart.biotSavart_apply,
          ← smul_sub, ← MeasureTheory.integral_sub hFint hGint]
      have step1 : ‖∫ a, (Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a)‖
          ≤ ∫ a in Metric.closedBall (0 : Work.LWP.R3) R,
              ‖crossL (h a) (kf (x - a) - kf (y - a))‖ := by
        have e1 : (∫ a, (Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a))
            = ∫ a, crossL (h a) (kf (x - a) - kf (y - a)) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hbk)
        rw [e1]
        calc ‖∫ a, crossL (h a) (kf (x - a) - kf (y - a))‖
            ≤ ∫ a, ‖crossL (h a) (kf (x - a) - kf (y - a))‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ = ∫ a in Metric.closedBall (0 : Work.LWP.R3) R,
                ‖crossL (h a) (kf (x - a) - kf (y - a))‖ := by
              rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
              intro a ha
              have ha0 : h a = 0 := by
                by_contra hne
                exact ha (hsupp a hne)
              rw [ha0, Work.CoreResiduals.BiotSavart.crossL_zero,
                zero_apply, norm_zero]
      have step2 : (∫ a in Metric.closedBall (0 : Work.LWP.R3) R,
              ‖crossL (h a) (kf (x - a) - kf (y - a))‖)
          ≤ ∫ a in Metric.closedBall (0 : Work.LWP.R3) R,
              Ck * ‖x - y‖ ^ α * G * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α)) := by
        have h := MeasureTheory.norm_integral_le_of_norm_le (μ := volume.restrict
          (Metric.closedBall (0 : Work.LWP.R3) R)) hmaj
          (Filter.Eventually.of_forall (fun a => by
            rw [Real.norm_of_nonneg (norm_nonneg (crossL (h a) (kf (x - a) - kf (y - a))))]
            exact hpt a))
        rwa [Real.norm_of_nonneg (setIntegral_nonneg hS (fun a _ => norm_nonneg _))] at h
      have step3 : (∫ a in Metric.closedBall (0 : Work.LWP.R3) R,
              Ck * ‖x - y‖ ^ α * G * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α)))
          = Ck * ‖x - y‖ ^ α * G *
              ((∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖x - a‖ ^ (-2 - α))
                + (∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖y - a‖ ^ (-2 - α))) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hIx hIy]
      have step4 : Ck * ‖x - y‖ ^ α * G *
            ((∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖x - a‖ ^ (-2 - α))
              + (∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖y - a‖ ^ (-2 - α)))
          ≤ Ck * ‖x - y‖ ^ α * G * (2 * (4 * Real.pi * ρ ^ (1 - α) / (1 - α))) := by
        have h1 := hcle x hx
        have h2 := hcle y hy
        have h3 : (∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖x - a‖ ^ (-2 - α))
            + (∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖y - a‖ ^ (-2 - α))
            ≤ 2 * (4 * Real.pi * ρ ^ (1 - α) / (1 - α)) := by linarith
        have h4 : 0 ≤ Ck * ‖x - y‖ ^ α * G :=
          mul_nonneg (mul_nonneg hCk0 (Real.rpow_nonneg (norm_nonneg _) _)) hG
        exact mul_le_mul_of_nonneg_left h3 h4
      have hchain : ‖∫ a, (Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a)‖
          ≤ Ck * ‖x - y‖ ^ α * G * (2 * (4 * Real.pi * ρ ^ (1 - α) / (1 - α))) :=
        step1.trans (step2.trans (step3.le.trans step4))
      calc ‖Work.LWP.biotSavart h x - Work.LWP.biotSavart h y‖
          = (4 * Real.pi)⁻¹ *
              ‖∫ a, (Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a)‖ := by
            rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ (4 * Real.pi)⁻¹ *
              (Ck * ‖x - y‖ ^ α * G * (2 * (4 * Real.pi * ρ ^ (1 - α) / (1 - α)))) :=
            mul_le_mul_of_nonneg_left hchain (by positivity)
        _ = 2 * Ck * G * ‖x - y‖ ^ α * ρ ^ (1 - α) / (1 - α) := by
            field_simp
        _ ≤ K * G * ‖x - y‖ ^ α := by
            have h4 : 0 ≤ G * ‖x - y‖ ^ α :=
              mul_nonneg hG (Real.rpow_nonneg (norm_nonneg _) _)
            calc 2 * Ck * G * ‖x - y‖ ^ α * ρ ^ (1 - α) / (1 - α)
                = (2 * Ck * ρ ^ (1 - α) / (1 - α)) * (G * ‖x - y‖ ^ α) := by ring
              _ ≤ K * (G * ‖x - y‖ ^ α) := mul_le_mul_of_nonneg_right hK3 h4
              _ = K * G * ‖x - y‖ ^ α := by ring

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.hasFDerivAt_biotSavart_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Filter
open scoped Topology

/-- **The `x`-derivative of the Biot–Savart field of a single slice.**  This is the pointwise form
of `Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one`: for a vorticity `ω` that is bounded,
supported in `closedBall 0 R`, ae-strongly-measurable and Hölder of exponent `c > 0`, the map
`x ↦ biotSavart ω x` is differentiable at every `x` with derivative `(4π)⁻¹ • bsDerivCLM ω ρ x`
for any `ρ > R + ‖x‖`.

Proof: exactly the body of `biotSavart_contDiff_one`, at the single point `x` instead of on a ball:
apply `holder_reduce` to get an exponent `c' < 1`, `hasFDerivAt_bsField` for the un-normalised
field `bsField ω ρ` (valid because `R + ‖x‖ < ρ`), multiply by the constant `(4π)⁻¹`, and rewrite
`biotSavart ω = (4π)⁻¹ • bsField ω ρ` on a neighbourhood of `x` via `biotSavart_ball_integral`
(`HasFDerivAt.congr_of_eventuallyEq`). -/
theorem hasFDerivAt_biotSavart_slice {ω : Work.CoreResiduals.R3 → Work.CoreResiduals.R3}
    {R M C c ρ : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hc : 0 < c)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hhold : ∀ a b : Work.CoreResiduals.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    {x : Work.CoreResiduals.R3} (hρ : R + ‖x‖ < ρ) :
    HasFDerivAt (Work.LWP.biotSavart ω)
      ((4 * Real.pi)⁻¹ • Work.CoreResiduals.BiotSavart.bsDerivCLM ω ρ x) x := by
  -- Reduce the Hölder exponent below `1`, as in `biotSavart_contDiff_one`.
  obtain ⟨c', C', hc'0, hc'1, hC'0, hhold'⟩ := holder_reduce hc hM hbdd hhold
  -- Differentiability of the un-normalised field `bsField ω ρ` at the single point `x`.
  have hd : HasFDerivAt (bsField ω ρ) (bsDerivCLM ω ρ x) x :=
    hasFDerivAt_bsField hR hM hc'0 hc'1 hC'0 hbdd hs hm hhold' hρ
  -- Multiply the field and its derivative by the normalisation constant `(4π)⁻¹`.
  have hd2 : HasFDerivAt ((4 * Real.pi)⁻¹ • bsField ω ρ)
      ((4 * Real.pi)⁻¹ • bsDerivCLM ω ρ x) x := hd.const_smul _
  -- On a neighbourhood of `x` the Biot–Savart field agrees with the normalised `bsField`.
  refine hd2.congr_of_eventuallyEq ?_
  have hcont : ContinuousAt (fun y : R3 => R + ‖y‖) x :=
    continuousAt_const.add continuous_norm.continuousAt
  have hev : ∀ᶠ y in 𝓝 x, R + ‖y‖ < ρ := hcont.eventually_lt continuousAt_const hρ
  filter_upwards [hev] with y hy
  exact biotSavart_ball_integral hM hbdd hs hm (le_of_lt hy)

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.Reductions =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-! ## R3 -/



/-! ## R3: the far-field half, unconditionally

Outside the support ball there is no singularity in the Biot–Savart integral, so the `C¹` clause of
R3 holds *for real* on `{x | 2R < ‖x‖}`, with no hypothesis beyond the profile data. -/


/-! ## R2 -/

/-- **The full strip bundle of R2 for the explicit field**: the strip admissibility
(`solVort_BSAdmissibleStrip`), the time-regularity (`solVort_timeDerivStrip`) and the second-order
time-regularity of `∂ₜω` (`timeDerivStripHolder_of_locallyLipschitz`, which turns the local
Lipschitzness of `∂ₜω` — R3's second-order condition — into the strip form; for the model data it
is also the content of R4, `TimeHolderDeriv`).  This is the hypothesis of `BiotSavartSpaceTime α`. -/
theorem solVort_BSAdmissibleStripFull {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hlip : TimeDerivLocallyLipschitz (solVort P) P.T)
    {S : ℝ} (hS : 0 < S) (hST : S < P.T) :
    BSAdmissibleStripFull α (solVort P) P.R S :=
  ⟨solVort_BSAdmissibleStrip P hS hST, solVort_timeDerivStrip P hS hST,
    timeDerivStripHolder_of_locallyLipschitz P hlip hS hST⟩




/-! ## R4 -/


/-! ## R1 -/


end Work.CoreResiduals
end
end
-- ===== merged: Submission.Work.CoreResiduals.solVort_BSAdmissibleOnWindow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `solVort_BSAdmissibleOnWindow` — the admissibility bundle of the constructed vorticity

## The measurability clause, and why it must be local in `t`

`Work.CoreResiduals.BSAdmissibleOnWindow` constrains the measurability of the slices only *near the
times of the half-window* `preWindow T = Ioo (-2) T`:

  `∀ t₀ ∈ preWindow T, ∃ ε > 0, ∀ t ∈ Ioo (t₀-ε) (t₀+ε), AEStronglyMeasurable (ω · t) volume`.

A *global* clause `∀ t : ℝ, AEStronglyMeasurable (ω · t) volume` would be **false** for
`ω = solVort P`, for every `P` whose modulation `λ̄` takes a negative value (e.g. the delivered model
data `T = 2`, `λ̄(t) = 1 - t/2`, at `t = 4`, where `λ̄(4) = -1`), because `solVort` evaluates the
profile at the self-similar variable `z = ρ(x)^p / λ̄(t)` (`p = profExp α`): for `λ̄(t) < 0` that
argument is **negative**, and `ProfileData` constrains the perturbation `g` only on `{z > -1}`
(`hsmooth : SmoothNbhd`) and on `{z ≥ 0}` (all remaining `g`-fields: `hvan`, `hzk`, `hzth`, `hg2`,
`hgdiff`, `hmem`, `hCgbig`, and `hmeasP`, which composes `g` with `Rc p x = ρ(x)^p ≥ 0`) — plus the
two lines `θ = 0, π/2` (`hvt`).  So `g` may be an arbitrary non-measurable function of `z` on
`{z ≤ -1}`, and choosing `g(z,θ) = 1_A(-z)·ϕ(θ)` there (with `A` non-measurable, `ϕ` smooth and
vanishing at `θ = 0, π/2`) keeps every `ProfileData` field satisfied while making the `t = 4` slice
`-χ(ρ(x)/L)·(F_*(-ρ(x)^p, θ(x)) + 1_A(ρ(x)^p)·ϕ(θ(x)))·e_θ(x)` non-measurable (its inner product
with `e₂` is a non-vanishing measurable multiple of `1_A(‖x‖)` on the positive-measure set
`{1 < ‖x‖ < L, x₁ > 0, x₃ > 0}`; Fubini in polar coordinates then forces `A ∩ (1,L)` to be
Lebesgue measurable).

Localising the clause is also exactly what the consumer `BiotSavartSpacetimeC1` needs — its
conclusion is claimed only at `t₀ ∈ preWindow T` — and `Defs.lean` now states the bundle in that
local form.  With it, the bundle **is** provable, which is what this file does.

## The eight conjuncts

Every conjunct is proved separately (the names are listed in the assembly at the bottom), from the
lemmas named in the original docstring plus the localisation helper
`CoreResiduals.exists_eps_min_lam` (a positive lower bound `m ≤ λ̄` and a two-sided neighbourhood
inside the open window `preWindow T`):

* support (global in `t`): `Work.ConstructionInstance.solVort_supp`;
* local boundedness: `Work.ConstructionInstance.solVort_bdd` (`CoreResiduals.solVort_localBdd_preWindow`);
* local `x`-Hölder regularity: `Work.ConstructionInstance.solVort_holder`
  (`CoreResiduals.solVort_localHolder_preWindow`);
* slice measurability near `preWindow T`: `solVort_cont` +
  `aestronglyMeasurable_of_continuousOn_core_of_support` (`solVort_aesm_preWindow`,
  `solVort_aesm_local`);
* time differentiability: `Work.ConstructionInstance.hasDerivAt_selfSimVort_slice`
  (`solVort_hasDerivAt_local`);
* the `∂ₜ`-bound: `Work.ConstructionInstance.solVort_bddDt` (`solVort_bddDt_local`);
* measurability of the `∂ₜ`-slices: `CoreResiduals.solVort_timeDeriv_aesm_preWindow`
  (difference quotients of the nearby measurable slices, `solVort_timeDeriv_aesm_local`).
-/

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-! ## The conjuncts for `solVort P` -/

/-- The support radius is positive: `R ≥ 2L > 0`. -/
theorem solVort_R_pos {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : 0 < P.R := by
  have hL2 : 0 < 2 * P.L := by linarith [P.hL]
  linarith [P.hRbig]

/-- The support conjunct, in the global-in-`t` form of the bundle
(`Work.ConstructionInstance.solVort_supp`). -/
theorem solVort_supp_all {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t : ℝ, ∀ y : R3, solVort P y t ≠ 0 → y ∈ Metric.closedBall 0 P.R :=
  Work.ConstructionInstance.solVort_supp P

/-- **Measurability of the slices on the half-window** (`∀ t ∈ preWindow T` form).  For such a `t`
the modulation is positive, the slice is continuous on the core ball (`solVort_cont`), and it is
supported in `B(0,R)`, so `aestronglyMeasurable_of_continuousOn_core_of_support` applies. -/
theorem solVort_aesm_preWindow {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      MeasureTheory.AEStronglyMeasurable (fun y : R3 => solVort P y t) MeasureTheory.volume := by
  intro t ht
  have hcont : ContinuousOn (fun y : R3 => solVort P y t)
      (Work.StabilityFar.coreRegion (P.R + 1)) := by
    have hmaps : Set.MapsTo (fun y : R3 => (y, t)) (Work.StabilityFar.coreRegion (P.R + 1))
        (Work.StabilityFar.coreRegion (P.R + 1) ×ˢ Work.ConstructionInstance.preWindow P.T) :=
      fun y hy => ⟨hy, ht⟩
    exact (Work.ConstructionInstance.solVort_cont P).comp
      (continuous_id.prodMk continuous_const).continuousOn hmaps
  exact Work.ConstructionInstance.aestronglyMeasurable_of_continuousOn_core_of_support
    (R := P.R) (R' := P.R + 1) (by linarith [P.hR]) hcont
    (fun y hy => Work.ConstructionInstance.solVort_supp P t y hy)

/-- **The fifth conjunct** (measurability of the slices near the half-window), in the
`ε`-neighbourhood shape in which the bundle states it: take the neighbourhood inside `preWindow T`
and apply `solVort_aesm_preWindow`. -/
theorem solVort_aesm_local {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        MeasureTheory.AEStronglyMeasurable (fun y : R3 => solVort P y t) MeasureTheory.volume := by
  intro t₀ ht₀
  obtain ⟨ε, hε, hsub, m, hm, hmle⟩ := exists_eps_min_lam P.hlam P.hlamdif ht₀
  exact ⟨ε, hε, fun t ht => solVort_aesm_preWindow P t (hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩)⟩

/-- **The sixth conjunct** (time differentiability near the half-window).  On a two-sided
neighbourhood of `t₀ ∈ preWindow T`, chosen inside the half-window (where `λ̄ > 0` and `λ̄` is
differentiable), the slice is differentiable in `t` with derivative
`timeDeriv (solVort P) · · t`: this is `Work.ConstructionInstance.hasDerivAt_selfSimVort_slice`. -/
theorem solVort_hasDerivAt_local {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : R3,
        HasDerivAt (fun s : ℝ => solVort P y s)
          (FiniteTimeSingularity.timeDeriv (solVort P) y t) t := by
  intro t₀ ht₀
  obtain ⟨ε, hε, hsub, m, hm, hmle⟩ := exists_eps_min_lam P.hlam P.hlamdif ht₀
  refine ⟨ε, hε, fun t ht y => ?_⟩
  have htpre : t ∈ Work.ConstructionInstance.preWindow P.T :=
    hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hd := Work.ConstructionInstance.hasDerivAt_selfSimVort_slice
    (p := Work.ConstructionInstance.profExp α) (g := P.g) (L := P.L) (lam := P.lam) (T := P.T)
    P.hgdiff P.hlam P.hlamdif htpre y
  simpa only [Work.ConstructionInstance.solVort] using hd

/-- **The seventh conjunct** (`∂ₜ`-bound near the half-window), from the box
`Work.ConstructionInstance.solVort_bddDt`.  The bundle's clause is un-normalised (no `λ̄²` weight),
and on the neighbourhood `λ̄ ≥ m > 0`, so `M₁ := P.M₁ / m²`. -/
theorem solVort_bddDt_local {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧ ∃ M₁ : ℝ,
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : R3,
        ‖FiniteTimeSingularity.timeDeriv (solVort P) y t‖ ≤ M₁ := by
  intro t₀ ht₀
  obtain ⟨ε, hε, hsub, m, hm, hmle⟩ := exists_eps_min_lam P.hlam P.hlamdif ht₀
  refine ⟨ε, hε, P.M₁ / m ^ 2, fun t ht y => ?_⟩
  have htpre : t ∈ Work.ConstructionInstance.preWindow P.T :=
    hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hmle' : m ≤ P.lam t := hmle t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hlt : 0 < P.lam t := P.hlam t htpre
  have hm2 : m ^ 2 ≤ (P.lam t) ^ 2 := by nlinarith [hm, hmle']
  have hm2pos : (0 : ℝ) < m ^ 2 := by positivity
  have hb := Work.ConstructionInstance.solVort_bddDt P t htpre y
  have h1 : ‖FiniteTimeSingularity.timeDeriv (solVort P) y t‖ ≤ P.M₁ / (P.lam t) ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (P.lam t) ^ 2), mul_comm]
    exact hb
  have h2 : P.M₁ / (P.lam t) ^ 2 ≤ P.M₁ / m ^ 2 :=
    div_le_div_of_nonneg_left P.hM₁ hm2pos hm2
  linarith

/-- **The eighth conjunct** (measurability of the `∂ₜ`-slices near the half-window), in the
`ε`-neighbourhood shape of the bundle, from the `preWindow`-global statement
`CoreResiduals.solVort_timeDeriv_aesm_preWindow`. -/
theorem solVort_timeDeriv_aesm_local {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), MeasureTheory.AEStronglyMeasurable
        (fun y : R3 => FiniteTimeSingularity.timeDeriv (solVort P) y t) MeasureTheory.volume := by
  intro t₀ ht₀
  obtain ⟨ε, hε, hsub, m, hm, hmle⟩ := exists_eps_min_lam P.hlam P.hlamdif ht₀
  refine ⟨ε, hε, fun t ht => ?_⟩
  exact solVort_timeDeriv_aesm_preWindow P t (hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩)

/-! ## The bundle -/

/-- The model data satisfies the half-window admissibility bundle of `Work.CoreResiduals.BSAdmissibleOnWindow`. Support and measurability of the slices are global; local boundedness, local x-Hölder regularity, time differentiability, the bound on the time derivative and the measurability of the derivative slice are claimed only near times t₀ in preWindow P.T, where the modulation is positive and locally bounded away from zero. The time differentiability is hasDerivAt_selfSimVort_slice, the derivative bound is bddDt_selfSimVort, and the local x-Hölder regularity comes from solVort_holder. -/
theorem solVort_BSAdmissibleOnWindow {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    Work.CoreResiduals.BSAdmissibleOnWindow (Work.ConstructionInstance.solVort P) P.R P.T :=
  ⟨solVort_R_pos P, solVort_supp_all P, solVort_localBdd_preWindow P,
    solVort_localHolder_preWindow P, solVort_aesm_local P, solVort_hasDerivAt_local P,
    solVort_bddDt_local P, solVort_timeDeriv_aesm_local P⟩

end Work.CoreResiduals
end
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.PsiWt.continuousOn_box_of_regPkg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.PsiWt

open Set

/-- **A `Jet` is continuous on the box `Iz ×ˢ Iθ` at every strip time.**

The joint `α`-Hölder clause of `Work.FTS.Regularity.Jet` controls
`|h z θ τ - h z' θ' τ'|` by `N · (|z-z'| + |θ-θ'| + |τ-τ'|)^α`.  At fixed `τ` this is the
`α`-Hölder (hence, since `α > 0`, continuous) estimate for the slice `(z,θ) ↦ h z θ τ` on the
box `Iz ×ˢ Iθ = [0,∞) × [0,π/2]`: the product metric `dist a b = max |Δz| |Δθ|` dominates half
the `ℓ¹`-distance used by the Hölder clause, and `x ↦ x^α` is increasing on `[0,∞)` for `α > 0`.

Only the shape `0 ≤ N ∧ _ ∧ (Hölder clause)` of `Jet` is used, so this applies to each of the
three jets `g`, `∂_zg`, `∂_τg` bundled in the regularity packages. -/
theorem continuousOn_box_of_jet {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.Regularity.Jet α S N h) (hα : 0 < α) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2 τ) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  obtain ⟨hN0, _, hNh⟩ := H
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have hN1 : 0 < N + 1 := by linarith
  have hden : 0 < 2 * (N + 1) := by linarith
  have hq : 0 < ε / (2 * (N + 1)) := div_pos hε hden
  refine ⟨(ε / (2 * (N + 1))) ^ (α⁻¹) / 2, ?_, ?_⟩
  · exact div_pos (Real.rpow_pos_of_pos hq α⁻¹) (by norm_num)
  · intro a ha hab
    have haz : 0 ≤ a.1 := ha.1
    have hbz : 0 ≤ b.1 := hb.1
    have hdx : |a.1 - b.1| ≤ dist a b := by
      have h := le_max_left (dist a.1 b.1) (dist a.2 b.2)
      simp only [Prod.dist_eq, Real.dist_eq] at h ⊢
      exact h
    have hdy : |a.2 - b.2| ≤ dist a b := by
      have h := le_max_right (dist a.1 b.1) (dist a.2 b.2)
      simp only [Prod.dist_eq, Real.dist_eq] at h ⊢
      exact h
    have hsum0 : 0 ≤ |a.1 - b.1| + |a.2 - b.2| := by positivity
    have hsum : |a.1 - b.1| + |a.2 - b.2| ≤ 2 * dist a b := by linarith
    have hΔ : |h a.1 a.2 τ - h b.1 b.2 τ| ≤ N * (|a.1 - b.1| + |a.2 - b.2|) ^ α := by
      have hh := hNh a.1 b.1 a.2 b.2 τ τ haz hbz ha.2 hb.2 hτ hτ
      simpa using hh
    have hle : |a.1 - b.1| + |a.2 - b.2| < (ε / (2 * (N + 1))) ^ (α⁻¹) := by
      have h2 : 2 * ((ε / (2 * (N + 1))) ^ (α⁻¹) / 2) = (ε / (2 * (N + 1))) ^ (α⁻¹) := by ring
      linarith
    have hlt : (|a.1 - b.1| + |a.2 - b.2|) ^ α < ε / (2 * (N + 1)) := by
      calc (|a.1 - b.1| + |a.2 - b.2|) ^ α
          < ((ε / (2 * (N + 1))) ^ (α⁻¹)) ^ α := Real.rpow_lt_rpow hsum0 hle hα
        _ = ε / (2 * (N + 1)) := Real.rpow_inv_rpow hq.le hα.ne'
    rw [Real.dist_eq]
    calc |h a.1 a.2 τ - h b.1 b.2 τ|
        ≤ N * (|a.1 - b.1| + |a.2 - b.2|) ^ α := hΔ
      _ ≤ (N + 1) * (|a.1 - b.1| + |a.2 - b.2|) ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hsum0 α)
      _ < (N + 1) * (ε / (2 * (N + 1))) := mul_lt_mul_of_pos_left hlt hN1
      _ = ε / 2 := by field_simp
      _ < ε := by linarith

/-- **The box-continuity clause `PsiWt` of the `FireFix` assembly**: the profile `g` of a
corrected regularity package `RegPkg'` is continuous on `Iz ×ˢ Iθ` at every strip time.

Immediate from the joint `α`-Hölder field `RegPkg'.hg` of the package and
`continuousOn_box_of_jet`. -/
theorem continuousOn_box_of_regPkg {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 τ)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  obtain ⟨N, hN⟩ := h.hg
  exact continuousOn_box_of_jet hN h.hα hτ

end Work.FTS.FireFix.Clauses.PsiWt
end
-- ===== merged: Submission.Work.FTS.FireFix.Prime.clockBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-- **Uniform bounds on the clock and its first-order combinations.**  On the fake-time strip
`[0,S]` the amplitude `A` and the scaling `B` are bounded away from `0` and their derivatives are
bounded, so all four quantities appearing in the dynamic-rescaling chain rule —
`A⁻¹`, `A'/A²`, `B⁻¹`, `B'/B` — are uniformly bounded by a single constant

  `M = max (max a₀⁻¹ b₀⁻¹) (max (|a₂|/a₀²) (|b₂|/b₀))`,

where `a₀`/`b₀` are the positive lower bounds of `A`/`B` and `a₂`/`b₂` the bounds on
`|A'|`/`|B'|`.  This is the elementary input of the time-Hölder estimates for `∂_τω`. -/
theorem clockBounds {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S,
      |(A τ)⁻¹| ≤ M ∧ |deriv A τ / (A τ) ^ 2| ≤ M ∧ |(B τ)⁻¹| ≤ M ∧
        |deriv B τ / B τ| ≤ M := by
  obtain ⟨a₀, a₁, ha₀, ha⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hb⟩ := h.hBb
  obtain ⟨a₂, ha₂⟩ := h.hAd
  obtain ⟨b₂, hb₂⟩ := h.hBd
  refine ⟨max (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀)), ?_, ?_⟩
  · have h1 : 0 ≤ a₀⁻¹ := inv_nonneg.mpr ha₀.le
    exact le_trans h1 (le_trans (le_max_left a₀⁻¹ b₀⁻¹)
      (le_max_left (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
  · intro τ hτ
    have hApos : 0 < A τ := h.hA τ hτ
    have hBpos : 0 < B τ := h.hB τ hτ
    have hAle : a₀ ≤ A τ := (ha τ hτ).1
    have hBle : b₀ ≤ B τ := (hb τ hτ).1
    have hP : |(A τ)⁻¹| ≤ a₀⁻¹ := by
      rw [abs_inv, abs_of_pos hApos, inv_le_inv₀ hApos ha₀]
      exact hAle
    have hQ : |(B τ)⁻¹| ≤ b₀⁻¹ := by
      rw [abs_inv, abs_of_pos hBpos, inv_le_inv₀ hBpos hb₀]
      exact hBle
    have hR : |deriv A τ / (A τ) ^ 2| ≤ |a₂| / a₀ ^ 2 := by
      rw [abs_div, abs_of_nonneg (sq_nonneg (A τ))]
      exact div_le_div₀ (abs_nonneg a₂) (le_trans (ha₂ τ hτ) (le_abs_self a₂))
        (pow_pos ha₀ 2) (pow_le_pow_left₀ ha₀.le hAle 2)
    have hT : |deriv B τ / B τ| ≤ |b₂| / b₀ := by
      rw [abs_div, abs_of_pos hBpos]
      exact div_le_div₀ (abs_nonneg b₂) (le_trans (hb₂ τ hτ) (le_abs_self b₂)) hb₀ hBle
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact le_trans hP (le_trans (le_max_left a₀⁻¹ b₀⁻¹)
        (le_max_left (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
    · exact le_trans hR (le_trans (le_max_left (|a₂| / a₀ ^ 2) (|b₂| / b₀))
        (le_max_right (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
    · exact le_trans hQ (le_trans (le_max_right a₀⁻¹ b₀⁻¹)
        (le_max_left (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))
    · exact le_trans hT (le_trans (le_max_right (|a₂| / a₀ ^ 2) (|b₂| / b₀))
        (le_max_right (max a₀⁻¹ b₀⁻¹) (max (|a₂| / a₀ ^ 2) (|b₂| / b₀))))

end Work.FTS.FireFix.Prime
end
-- ===== merged: Submission.Work.FTS.FireFix.Prime.clockLipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-- **The self-similar clock `B` is Lipschitz on the fake-time strip `[0,S]`.**

`RegPkg'` makes `B` differentiable on `[0,S]` with bounded `deriv`; the mean value theorem on the
convex interval `[0,S]` then turns that bound into a global Lipschitz constant
`K = max b₂ 0`, where `b₂` bounds `deriv B`.  (The `max` with `0` is what makes `K` nonnegative
regardless of the sign of the supplied bound.) -/
theorem clockLipschitz {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |B τ - B τ'| ≤ K * |τ - τ'| := by
  obtain ⟨b₂, hb₂⟩ := h.hBd
  refine ⟨max b₂ 0, le_max_right _ _, fun τ hτ τ' hτ' => ?_⟩
  have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) S, DifferentiableAt ℝ B x :=
    fun x hx => (h.hBdiff x hx).differentiableAt
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) S, ‖deriv B x‖ ≤ max b₂ 0 := fun x hx => by
    rw [Real.norm_eq_abs]
    exact le_trans (hb₂ x hx) (le_max_left _ _)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc 0 S) hτ' hτ
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  simpa [abs_sub_comm] using hmvt

end Work.FTS.FireFix.Prime
end
-- ===== merged: Submission.Work.FTS.FireFix.Prime.dtgZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

theorem dtgZero {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∃ L : ℝ, 0 < L ∧ ∀ z θ τ : ℝ, L < z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => g z θ s) τ = 0 := by
  obtain ⟨L, hLpos, hL⟩ := h.hsupp
  refine ⟨L, hLpos, fun z θ τ hz _ hτ => ?_⟩
  -- The full profile vanishes at every time of the strip above the support radius `L`, and the
  -- leading profile `F_*` is time-independent, so `s ↦ g z θ s` is constant on `[0,S]`.
  refine deriv_eq_zero_of_const_on_Icc h.hS ?_ τ hτ
  intro s hs t ht
  have h1 : Work.Construction.Fstar (pExp α) z θ + g z θ s = 0 := hL s hs z θ hz.le
  have h2 : Work.Construction.Fstar (pExp α) z θ + g z θ t = 0 := hL t ht z θ hz.le
  linarith

end Work.FTS.FireFix.Prime
end
-- ===== merged: Submission.Work.FTS.FireFix.Prime.dzProfFullUniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.Regularity.dzProfFullUniform` — the uniform `z`-derivative of the full profile

For a regularity package `h : RegPkg' α S A B g` and a radius `R ≥ 0`, the `z`-derivative of the
full self-similar profile `F = F_* + g` (`profFull α g`) enjoys, uniformly on `z ∈ [0,R]`,
`θ ∈ Iθ`, `τ ∈ [0,S]`:

1. the **splitting** `∂_z F = ∂_z F_* + ∂_z g` (plain additivity of `deriv`, available because
   `RegPkg'.hcont` makes `(z,τ) ↦ g z θ τ` jointly `C¹` at each fixed `θ` while `F_*` is smooth);
2. a **uniform bound** `|∂_z F| ≤ M`;
3. a **joint `α`-Hölder estimate in `(z,τ)`**:
   `|∂_zF(z,θ,τ) - ∂_zF(z',θ,τ')| ≤ N * (|z-z'| + |τ-τ'|)^α`.

The sum is estimated on its two parts:

* the **static part** `∂_z F_*` is bounded and `α`-Hölder on `[0,R]`; this is the content of the
  sibling module `Submission.Work.FTS.Regularity.fstarDzUniform`
  (`Work.FTS.Regularity.fstarDzUniform`);
* the **perturbation part** `∂_z g` is bounded and jointly `α`-Hölder in `(z,θ,τ)` by the jet
  field `RegPkg'.hpz` (restricted to `θ = θ'`).
-/

noncomputable section

open FiniteTimeSingularity Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-- **The `z`-slices of the perturbation are differentiable.**  `RegPkg'.hcont` states that
`(z,τ) ↦ g z θ τ` is `C¹` on `Ioi (-1) ×ˢ Ioo (-1) (S+1)` at each fixed `θ ∈ Iθ`; since
`z ≥ 0 > -1` and `τ ∈ [0,S] ⊂ (-1, S+1)`, composing with `z' ↦ (z',τ)` gives differentiability of
the `z`-slice `z' ↦ g z' θ τ` at `z`. -/
theorem gSlice_differentiableAt {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∀ θ ∈ Work.Spaces.Iθ, ∀ z τ : ℝ, 0 ≤ z → τ ∈ Set.Icc 0 S →
      DifferentiableAt ℝ (fun z' => g z' θ τ) z := by
  intro θ hθ z τ hz hτ
  have hz1 : -1 < z := by linarith
  have hτ1 : -1 < τ := by linarith [hτ.1]
  have hτ2 : τ < S + 1 := by linarith [hτ.2, h.hS]
  have hmem : (z, τ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) : Set (ℝ × ℝ)) :=
    ⟨hz1, hτ1, hτ2⟩
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2) (z, τ) :=
    (h.hcont θ hθ).contDiffAt (hopen.mem_nhds hmem)
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => g q.1 θ q.2) (z, τ) :=
    hcd.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (fun z' : ℝ => (z', τ)) z := by fun_prop
  exact hdiff.comp z hg

/-- **The `z`-slices of the fundamental profile are differentiable** on `z > -1`: `F_*` is a
constant (in `z`; the `θ`-dependence enters only through the factor `Γ(θ)/c`) multiple of
`Work.FM.Fstar z = 2z/(1+z)²`, whose derivative is explicit
(`Work.FM.hasDerivAt_Fstar`). -/
theorem fstarSlice_differentiableAt {α : ℝ} (z θ : ℝ) (hz : -1 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.Fstar (pExp α) z' θ) z := by
  have hfun : (fun z' => Work.Construction.Fstar (pExp α) z' θ)
      = fun z' => (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
          * Work.FM.Fstar z' := by
    funext z'
    rw [Work.Construction.Fstar]
  rw [hfun]
  exact (Work.FM.hasDerivAt_Fstar z hz).const_mul _ |>.differentiableAt

theorem dzProfFullUniform {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) (R : ℝ) (hR : 0 ≤ R) :
    (∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
        deriv (fun z' => profFull α g z' θ τ) z
          = deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z
            + Work.Spaces.pz (gSlice g τ) z θ) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ z θ τ : ℝ, 0 ≤ z → z ≤ R → θ ∈ Work.Spaces.Iθ →
        τ ∈ Set.Icc 0 S → |deriv (fun z' => profFull α g z' θ τ) z| ≤ M) ∧
      (∃ N : ℝ, 0 ≤ N ∧ ∀ z z' θ τ τ' : ℝ, 0 ≤ z → z ≤ R → 0 ≤ z' → z' ≤ R →
        θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → τ' ∈ Set.Icc 0 S →
        |deriv (fun z'' => profFull α g z'' θ τ) z
          - deriv (fun z'' => profFull α g z'' θ τ') z'| ≤ N * (|z - z'| + |τ - τ'|) ^ α) := by
  -- the static part: bounds for `∂_z F_*` on `[0,R]`
  obtain ⟨M0, N0, hM0, hN0, hM0b, hN0b⟩ := fstarDzUniform h.hα h.hα13 hR
  -- the perturbation part: the jet of `∂_z g`
  obtain ⟨Npz, hNpz⟩ := h.hpz
  have hNpz0 : 0 ≤ Npz := hNpz.1
  -- conjunct 1: `deriv` is additive on the sum `F_* + g`
  have hpart1 : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun z' => profFull α g z' θ τ) z
        = deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z
          + Work.Spaces.pz (gSlice g τ) z θ := by
    intro z θ τ hz hθ hτ
    have hFd : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar (pExp α) z' θ) z :=
      fstarSlice_differentiableAt z θ (by linarith)
    have hGd : DifferentiableAt ℝ (fun z' => g z' θ τ) z :=
      gSlice_differentiableAt h θ hθ z τ hz hτ
    exact deriv_add hFd hGd
  refine ⟨hpart1, ?_, ?_⟩
  · -- conjunct 2: triangle inequality, `M = M0 + Npz`
    refine ⟨M0 + Npz, by linarith, ?_⟩
    intro z θ τ hz hzR hθ hτ
    rw [hpart1 z θ τ hz hθ hτ]
    have h1 := hM0b z θ hz hzR hθ
    have h2 := hNpz.abs_le hz hθ hτ
    calc |deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z
            + Work.Spaces.pz (gSlice g τ) z θ|
        ≤ |deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z|
          + |Work.Spaces.pz (gSlice g τ) z θ| := abs_add_le _ _
      _ ≤ M0 + Npz := add_le_add h1 h2
  · -- conjunct 3: triangle inequality; the static part is `α`-Hölder, the perturbation part is
    -- jointly `α`-Hölder by its jet (at `θ = θ'`), then `|z-z'|^α ≤ (|z-z'|+|τ-τ'|)^α`
    refine ⟨N0 + Npz, by linarith, ?_⟩
    intro z z' θ τ τ' hz hzR hz' hz'R hθ hτ hτ'
    rw [hpart1 z θ τ hz hθ hτ, hpart1 z' θ τ' hz' hθ hτ']
    have h1 := hN0b z z' θ hz hzR hz' hz'R hθ
    have h2 := hNpz.2.2 z z' θ θ τ τ' hz hz' hθ hθ hτ hτ'
    have h3 : |z - z'| ^ α ≤ (|z - z'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (le_add_of_nonneg_right (abs_nonneg _)) h.hα.le
    have h5 : (0 : ℝ) ≤ (|z - z'| + |τ - τ'|) ^ α := Real.rpow_nonneg (by positivity) _
    have h6 : (0 : ℝ) ≤ N0 := hN0
    calc |deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
            + Work.Spaces.pz (gSlice g τ) z θ
            - (deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z'
              + Work.Spaces.pz (gSlice g τ') z' θ)|
        = |(deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
              - deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z')
            + (Work.Spaces.pz (gSlice g τ) z θ - Work.Spaces.pz (gSlice g τ') z' θ)| := by
          ring_nf
      _ ≤ |deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
              - deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z'|
            + |Work.Spaces.pz (gSlice g τ) z θ - Work.Spaces.pz (gSlice g τ') z' θ| :=
          abs_add_le _ _
      _ ≤ N0 * |z - z'| ^ α + Npz * (|z - z'| + |θ - θ| + |τ - τ'|) ^ α :=
          add_le_add h1 h2
      _ ≤ (N0 + Npz) * (|z - z'| + |τ - τ'|) ^ α := by
          simp only [sub_self, abs_zero, add_zero] at *
          nlinarith [mul_le_mul_of_nonneg_left h3 h6, h5]

end Work.FTS.FireFix.Prime
end
end
-- ===== merged: Submission.Work.FTS.FireFix.Prime.dzProfFullZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Topology

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

theorem dzProfFullZero {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∃ L : ℝ, 0 < L ∧ ∀ z θ τ : ℝ, L < z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun z' => profFull α g z' θ τ) z = 0 := by
  obtain ⟨L, hLpos, hL⟩ := h.hsupp
  refine ⟨L, hLpos, fun z θ τ hz _ hτ => ?_⟩
  have hev : (fun z' => profFull α g z' θ τ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show z ∈ Set.Ioi L from hz)] with z' hz'
    exact hL τ hτ z' θ hz'.le
  rw [hev.deriv_eq]
  simp

end Work.FTS.FireFix.Prime
end
-- ===== merged: Submission.Work.FTS.FireFix.Prime.physVort_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-- The azimuthal vector field `e_θ` is a unit vector, and `0` on the axis (`radial x = 0`). -/
theorem norm_eTheta_le_one (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  by_cases h : Work.Cyl.radial x = 0
  · simp [Work.Cyl.eTheta, h]
  · rw [Work.Cyl.norm_eTheta x h]

/-- The polar angle `θ(x) = arctan(x₃/r)` satisfies `|θ(x)| ∈ [0,π/2]`. -/
theorem abs_theta_mem_Iθ (y : R3) : |Work.Cyl.theta y| ∈ Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc]
  have h := Real.arctan_mem_Ioo (Work.Cyl.axial y / Work.Cyl.radial y)
  rw [Work.Cyl.theta]
  exact ⟨abs_nonneg _, le_of_lt (abs_lt.mpr ⟨h.1, h.2⟩)⟩

/-- **Pointwise bound of the self-similar profile.**  For `z ≥ 0`, `|θ| ∈ Iθ` and `τ` in the
strip, `|F(z,θ,τ)| ≤ 20·(3α) + N`, where `N` bounds the perturbation `g`. -/
theorem abs_profile_le {α S N : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hN : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → |g z θ τ| ≤ N)
    {z θ τ : ℝ} (hz : 0 ≤ z) (hθ : |θ| ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    |Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ| ≤ 20 * pExp α + N := by
  have hp : 0 < pExp α := pExp_pos hα
  have hp1 : pExp α ≤ 1 := pExp_le_one hα13
  have key : ∀ θ' ∈ Work.Spaces.Iθ,
      |Work.Construction.Fstar (pExp α) z θ' + g z θ' τ| ≤ 20 * pExp α + N := by
    intro θ' hθ'
    have h1 := Work.ConstructionInstance.Fstar_abs_le hp hp1 hz hθ'
    have hp3 : 0 ≤ pExp α / 3 := (div_pos hp (by norm_num)).le
    have hG1 := Work.ConstructionInstance.Gamma_le_one (β := pExp α / 3) hp3 hθ'
    have hG0 := Work.ConstructionInstance.Gamma_nonneg (β := pExp α / 3) hθ'
    have h2 : 20 * pExp α * Work.ConstructionInstance.Gamma (pExp α / 3) θ'
        ≤ 20 * pExp α := by nlinarith
    have h3 := hN z θ' τ hz hθ' hτ
    calc |Work.Construction.Fstar (pExp α) z θ' + g z θ' τ|
        ≤ |Work.Construction.Fstar (pExp α) z θ'| + |g z θ' τ| := abs_add_le _ _
      _ ≤ 20 * pExp α + N := add_le_add (le_trans h1 h2) h3
  rw [Work.ConstructionInstance.profile]
  split_ifs with h
  · exact key θ (by simpa [abs_of_nonneg h] using hθ)
  · rw [abs_neg]
    exact key (-θ) (by simpa [abs_of_neg (not_le.mp h)] using hθ)

/-- **THE PHYSICAL VORTICITY IS UNIFORMLY BOUNDED ON THE STRIP.** -/
theorem physVort_bound {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ y : Work.FTS.Regularity.R3,
      ‖Work.FTS.Regularity.physVort α A B g y τ‖ ≤ M := by
  obtain ⟨a₀, a₁, ha₀, hA⟩ := h.hAb
  obtain ⟨N, hN⟩ := h.hg
  have hN0 : 0 ≤ N := hN.1
  have hpN : 0 ≤ 20 * pExp α + N := by
    have hp := pExp_pos h.hα
    linarith
  refine ⟨(1 / a₀) * (20 * pExp α + N), by positivity, fun τ hτ y => ?_⟩
  have hAτ : 0 < A τ := h.hA τ hτ
  have hBτ : 0 < B τ := h.hB τ hτ
  have hz0 : 0 ≤ Work.Cyl.rho y ^ pExp α / B τ :=
    div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg y) _) hBτ.le
  have hprof := abs_profile_le h.hα h.hα13
    (fun z θ σ hz hθ hσ => hN.abs_le hz hθ hσ) hz0 (abs_theta_mem_Iθ y) hτ
  have hAinv : |(A τ)⁻¹| ≤ 1 / a₀ := by
    rw [abs_of_pos (inv_pos.mpr hAτ), one_div]
    exact (inv_le_inv₀ hAτ ha₀).mpr (hA τ hτ).1
  have he : ‖Work.Cyl.eTheta y‖ ≤ 1 := norm_eTheta_le_one y
  have hinner : |Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
        (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y)| * ‖Work.Cyl.eTheta y‖
      ≤ 20 * pExp α + N := by
    calc |Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
          (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y)| * ‖Work.Cyl.eTheta y‖
        ≤ (20 * pExp α + N) * 1 :=
          mul_le_mul hprof he (norm_nonneg _) hpN
      _ = 20 * pExp α + N := mul_one _
  calc ‖Work.FTS.Regularity.physVort α A B g y τ‖
      = ‖(A τ)⁻¹ • (Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
            (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y) • Work.Cyl.eTheta y)‖ := by
        rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply]
    _ = |(A τ)⁻¹| * (|Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
            (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y)| * ‖Work.Cyl.eTheta y‖) := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (1 / a₀) * (20 * pExp α + N) :=
        mul_le_mul hAinv hinner (by positivity) (by positivity)

end Work.FTS.FireFix.Prime
end
end
-- ===== merged: Submission.Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology
open scoped Topology

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-- `|a + b| ≤ |a| + |b|` for reals. -/
private theorem abs_add_le_aux_prv {a b : ℝ} : |a + b| ≤ |a| + |b| := by
  simpa [Real.norm_eq_abs] using norm_add_le a b

/-- The polar angle satisfies `|θ(x)| ∈ [0,π/2]`. -/
private theorem abs_theta_mem_Iθ_aux (y : R3) : |Work.Cyl.theta y| ∈ Work.Spaces.Iθ := by
  refine ⟨abs_nonneg _, ?_⟩
  rw [abs_le]
  rw [Work.Cyl.theta]
  exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩

/-- The azimuthal frame vector is a unit vector (and `0` on the axis). -/
private theorem norm_eTheta_le_one_aux (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  by_cases h : Work.Cyl.radial x = 0
  · rw [Work.Cyl.eTheta, h, div_zero, zero_smul, norm_zero]
    norm_num
  · rw [Work.Cyl.norm_eTheta x h]

/-! ## Auxiliary objects for the physical vorticity's time derivative

The physical vorticity is `ω(x,τ) = A(τ)⁻¹ • (F(ρ(x)^{3α}/B(τ), θ(x), τ) • e_θ(x))`, where
`F = F_* + g = profFull` and the profile is extended oddly in `θ`.  We record (i) the odd
extension `profOdd` of `profFull` and its identification with `ConstructionInstance.profile`,
(ii) the resulting product form of `physVort`, (iii) the `z`-derivative box of `F_*`, and
(iv) the two chain rules (in `z` and along the curve `s ↦ (ρ^{3α}/B(s), s)`). -/

/-- The odd extension in `θ` of the full profile `F = F_* + g`. -/
def profOdd (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) : ℝ :=
  if 0 ≤ θ then profFull α g z θ τ else -profFull α g z (-θ) τ

/-- `ConstructionInstance.profile (pExp α) (gSlice g τ)` is the odd extension of `profFull`. -/
theorem profile_eq_profOdd (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ = profOdd α g z θ τ := by
  by_cases hθ : 0 ≤ θ
  · rw [Work.ConstructionInstance.profile_of_nonneg hθ, profOdd, if_pos hθ]
    rfl
  · rw [Work.ConstructionInstance.profile_of_neg hθ, profOdd, if_neg hθ]
    simp

/-- **Product form of the physical vorticity**: `ω(x,τ) = A(τ)⁻¹ • (F(z,θ,τ) • e_θ(x))` with
`z = ρ(x)^{3α}/B(τ)`, `θ = θ(x)` and the odd extension of the full profile. -/
theorem physVort_eq_smul (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) :
    physVort α A B g x τ
      = (A τ)⁻¹ • (profOdd α g (Work.Cyl.rho x ^ pExp α / B τ) (Work.Cyl.theta x) τ
          • Work.Cyl.eTheta x) := by
  rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply, profile_eq_profOdd]

/-- **The `z`-derivative box of `F_*`**: `|∂_zF_*(z,θ)| ≤ 20p` for `0 < p ≤ 1`, `z ≥ 0` and
`θ ∈ Iθ`.  (`∂_zF_* = p(Γ(θ)/c(p))·2(1-z)/(1+z)³`, `Γ/c ≤ 10` and the rational factor is `≤ 2`
in absolute value on `z ≥ 0`.) -/
theorem pzFstar_abs_le_aux {p z θ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pz (Work.Construction.Fstar p) z θ| ≤ 20 * p := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hG0 : 0 ≤ Work.Spaces.Gam p θ := (Work.Spaces.Gam_bounds p θ hp hθ).1
  have hDz : Work.Spaces.pz (Work.Construction.Fstar p) z θ
      = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (2 * (1 - z) / (1 + z) ^ 3) := by
    have hfun : (fun z' => Work.Construction.Fstar p z' θ)
        = fun z' => (p * (Work.Spaces.Gam p θ / Work.Spaces.c p)) * Work.FM.Fstar z' := by
      funext z'; rw [Work.Construction.Fstar]
    rw [Work.Spaces.pz, hfun, deriv_const_mul_field, Work.FM.deriv_Fstar z (by linarith)]
  have hgb0 : 0 ≤ Work.Spaces.Gam p θ / Work.Spaces.c p := div_nonneg hG0 hcpos.le
  have hgle : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
    rw [div_le_iff₀ hcpos]; nlinarith [(Work.Spaces.Gam_bounds p θ hp hθ).2]
  have hfrac : |2 * (1 - z) / (1 + z) ^ 3| ≤ 2 := by
    have h1z : (0 : ℝ) < (1 + z) ^ 3 := by positivity
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos h1z,
      div_le_iff₀ h1z]
    have h3 : |1 - z| ≤ (1 + z) ^ 3 := by
      have h4 : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
      have h5 : (1 : ℝ) ≤ 1 + z := by linarith
      nlinarith [sq_nonneg (1 + z), h5]
    linarith
  rw [hDz, abs_mul, abs_mul, abs_of_nonneg hp.le, abs_of_nonneg hgb0]
  calc p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * |2 * (1 - z) / (1 + z) ^ 3|
      ≤ p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * 2 :=
        mul_le_mul_of_nonneg_left hfrac (mul_nonneg hp.le hgb0)
    _ ≤ p * 10 * 2 := by
        have h : p * (Work.Spaces.Gam p θ / Work.Spaces.c p) ≤ p * 10 :=
          mul_le_mul_of_nonneg_left hgle hp.le
        linarith
    _ = 20 * p := by ring

/-! ### The two chain rules -/

/-- **Chain rule for the perturbation along a curve.**  If `G : ℝ × ℝ → ℝ` is `C¹` on the open
strip `Ioi(-1) ×ˢ Ioo(-1)(S+1)` and `zfun` has derivative `z'` at `τ`, then
`s ↦ g (zfun s) θ s` (= `G (zfun s, s)` with `G q = g q.1 θ q.2`) has derivative
`z'·∂_zg + ∂_τg` at `τ`. -/
theorem gComp_hasDerivAt_aux {g : ℝ → ℝ → ℝ → ℝ} {θ S τ z' : ℝ} (_hθ : θ ∈ Work.Spaces.Iθ)
    (hcont : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Ioo (-1) (S + 1)) {zfun : ℝ → ℝ} (hz : -1 < zfun τ)
    (hzfun : HasDerivAt zfun z' τ) :
    HasDerivAt (fun s => g (zfun s) θ s)
      (z' * Work.Spaces.pz (gSlice g τ) (zfun τ) θ
        + deriv (fun t => g (zfun τ) θ t) τ) τ := by
  set G : ℝ × ℝ → ℝ := fun q => g q.1 θ q.2 with hGdef
  have hopen : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1)) :=
    (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ))).prod
      (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) (S + 1)))
  have hmem : (zfun τ, τ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) := ⟨hz, hτ⟩
  have hnhds : (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) ∈ 𝓝 (zfun τ, τ) :=
    hopen.mem_nhds (x := (zfun τ, τ)) hmem
  have hdiff : DifferentiableAt ℝ G (zfun τ, τ) :=
    (hcont.contDiffAt hnhds).differentiableAt (by norm_num)
  have hF : HasFDerivAt G (fderiv ℝ G (zfun τ, τ)) (zfun τ, τ) := hdiff.hasFDerivAt
  set L : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ G (zfun τ, τ) with hLdef
  have hcurve : HasDerivAt (fun s : ℝ => (zfun s, s)) ((z', (1 : ℝ)) : ℝ × ℝ) τ :=
    hzfun.prodMk (hasDerivAt_id τ)
  have hcomp : HasDerivAt (G ∘ fun s : ℝ => (zfun s, s)) (L (z', 1)) τ :=
    hF.comp_hasDerivAt (f := fun s : ℝ => (zfun s, s)) τ hcurve
  have hcomp' : HasDerivAt (fun s => g (zfun s) θ s) (L (z', 1)) τ := by
    simpa [hGdef, Function.comp_def] using hcomp
  -- the two partial derivatives, identified with `L (1,0)` and `L (0,1)`
  have hL1 : L (1, 0) = Work.Spaces.pz (gSlice g τ) (zfun τ) θ := by
    have h := hF.comp_hasDerivAt (f := fun s : ℝ => (s, τ)) (zfun τ)
      (HasDerivAt.prodMk (hasDerivAt_id (zfun τ)) (hasDerivAt_const (zfun τ) τ))
    have hd : deriv (fun s => G (s, τ)) (zfun τ) = L (1, 0) := h.deriv
    have hev : deriv (fun s => G (s, τ)) (zfun τ)
        = Work.Spaces.pz (gSlice g τ) (zfun τ) θ := by
      simp [hGdef, Work.Spaces.pz]
    exact hd.symm.trans hev
  have hL2 : L (0, 1) = deriv (fun t => g (zfun τ) θ t) τ := by
    have h := hF.comp_hasDerivAt (f := fun s : ℝ => (zfun τ, s)) τ
      (HasDerivAt.prodMk (hasDerivAt_const τ (zfun τ)) (hasDerivAt_id τ))
    have hd : deriv ((fun q : ℝ × ℝ => g q.1 θ q.2) ∘ fun s : ℝ => (zfun τ, s)) τ
        = L (0, 1) := h.deriv
    simpa [hGdef, Function.comp_def] using hd.symm
  have hval : L (z', 1) = z' * Work.Spaces.pz (gSlice g τ) (zfun τ) θ
      + deriv (fun t => g (zfun τ) θ t) τ := by
    have hsplit : ((z', (1 : ℝ)) : ℝ × ℝ) = z' • ((1, 0) : ℝ × ℝ) + (1 : ℝ) • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, map_smul, hL1, hL2]
    simp
  rw [hval] at hcomp'
  exact hcomp'

/-- **The `z`-derivative of the full profile splits.**  If `(z',τ) ↦ g z' θ τ` is `C¹` on the
open strip, then `∂_z(F_* + g) = ∂_zF_* + ∂_zg` for `z > -1`. -/
theorem profFull_deriv_z_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {θ z τ : ℝ}
    (hcont : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hz : -1 < z) (hτ : τ ∈ Set.Ioo (-1) (S + 1)) :
    deriv (fun z' => profFull α g z' θ τ) z
      = Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ
        + Work.Spaces.pz (gSlice g τ) z θ := by
  set G : ℝ × ℝ → ℝ := fun q => g q.1 θ q.2 with hGdef
  have hopen : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1)) :=
    (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ))).prod
      (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) (S + 1)))
  have hmem : (z, τ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) := ⟨hz, hτ⟩
  have hnhds : (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) ∈ 𝓝 (z, τ) :=
    hopen.mem_nhds (x := (z, τ)) hmem
  have hdiff : DifferentiableAt ℝ G (z, τ) :=
    (hcont.contDiffAt hnhds).differentiableAt (by norm_num)
  have hGdiff : DifferentiableAt ℝ (fun z' => g z' θ τ) z := by
    have hp : DifferentiableAt ℝ (fun z' : ℝ => (z', τ)) z := by fun_prop
    simpa [hGdef, Function.comp_def] using hdiff.comp z hp
  have hF : HasDerivAt (fun z' => Work.Construction.Fstar (pExp α) z' θ)
      (Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ) z :=
    Work.ConstructionInstance.hasDerivAt_Fstar_z z θ hz
  have hG : HasDerivAt (fun z' => g z' θ τ) (deriv (fun z' => g z' θ τ) z) z :=
    hGdiff.hasDerivAt
  have hsum := hF.add hG
  have hfun : (fun z' => profFull α g z' θ τ)
      = fun z' => Work.Construction.Fstar (pExp α) z' θ + g z' θ τ := by
    funext z'; rw [profFull_apply]
  have hval : Work.Spaces.pz (gSlice g τ) z θ = deriv (fun z' => g z' θ τ) z := rfl
  rw [hfun, hval]
  exact hsum.deriv

/-! ### The bookkeeping functions of the derivative -/

/-- The slope of the self-similar variable `s ↦ ρ^{3α}/B(s)` at time `τ`. -/
def zSlope (α : ℝ) (B : ℝ → ℝ) (ρ τ : ℝ) : ℝ :=
  -(ρ ^ pExp α * deriv B τ / (B τ) ^ 2)

/-- The `z`-derivative of the full profile `F = F_* + g` at a `τ`-slice, written as the sum of
the two summands' `z`-derivatives. -/
def pzProf (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) : ℝ :=
  Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ + Work.Spaces.pz (gSlice g τ) z θ

/-- The `τ`-derivative of the odd extension of the profile along the curve
`s ↦ (ρ^{3α}/B(s), s)`, as a function of `(ρ, θ, τ)`. -/
def dProfOdd (α : ℝ) (B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (ρ θ τ : ℝ) : ℝ :=
  if 0 ≤ θ then zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ
      + deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ
  else -(zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) (-θ) τ
      + deriv (fun t => g (ρ ^ pExp α / B τ) (-θ) t) τ)

/-- The value of `∂_τω(x,τ)`. -/
def vortDt (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) : R3 :=
  (A τ)⁻¹ • (dProfOdd α B g (Work.Cyl.rho x) (Work.Cyl.theta x) τ • Work.Cyl.eTheta x)
    + (-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (Work.Cyl.rho x ^ pExp α / B τ)
        (Work.Cyl.theta x) τ • Work.Cyl.eTheta x)

/-! ### The bound on the profile and its two derivatives -/

/-- `|F(z,θ,τ)| ≤ 20·3α + Ng` on the domain. -/
private theorem profFull_abs_le_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {Ng : ℝ}
    (hp : 0 < pExp α) (hp1 : pExp α ≤ 1) (hNg : Jet α S Ng g) {z θ τ : ℝ} (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    |profFull α g z θ τ| ≤ 20 * pExp α + Ng := by
  have hα0 : 0 ≤ α := by
    have h : pExp α / 3 = α := by rw [pExp]; ring
    rw [← h]; positivity
  have hF : |Work.Construction.Fstar (pExp α) z θ| ≤ 20 * pExp α := by
    have h1 := Work.ConstructionInstance.Fstar_abs_le (p := pExp α) hp hp1 hz hθ
    have h2 : Work.FTS.Regularity.Gamma (pExp α / 3) θ ≤ 1 := by
      rw [show pExp α / 3 = α by rw [pExp]; ring]
      exact Work.ConstructionInstance.Gamma_le_one hα0 hθ
    calc |Work.Construction.Fstar (pExp α) z θ|
        ≤ 20 * pExp α * Work.FTS.Regularity.Gamma (pExp α / 3) θ := h1
      _ ≤ 20 * pExp α * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 20 * pExp α := by ring
  have hg : |g z θ τ| ≤ Ng := hNg.abs_le hz hθ hτ
  calc |profFull α g z θ τ| = |Work.Construction.Fstar (pExp α) z θ + g z θ τ| := by
        rw [profFull_apply]
    _ ≤ 20 * pExp α + Ng := abs_add_le_aux_prv.trans (add_le_add hF hg)

/-- `|F(z,θ,τ)| ≤ 20·3α + Ng` for the odd extension, `|θ| ∈ Iθ`. -/
private theorem profOdd_abs_le_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {Ng : ℝ}
    (hp : 0 < pExp α) (hp1 : pExp α ≤ 1) (hNg : Jet α S Ng g) {z θ τ : ℝ} (hz : 0 ≤ z)
    (hθ : |θ| ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    |profOdd α g z θ τ| ≤ 20 * pExp α + Ng := by
  rw [profOdd]
  split_ifs with hθ0
  · exact profFull_abs_le_aux hp hp1 hNg hz ⟨hθ0, le_trans (le_abs_self θ) hθ.2⟩ hτ
  · rw [abs_neg]
    have hθ₁ : -θ ∈ Work.Spaces.Iθ := by
      have h : -θ = |θ| := (abs_of_neg (not_le.mp hθ0)).symm
      rw [h]; exact hθ
    exact profFull_abs_le_aux hp hp1 hNg hz hθ₁ hτ

/-- **The z-derivative of the profile is bounded, jointly with the support**: on the support
region `z ≤ L` this is the two global boxes, and for `z > L` the profile vanishes identically in
`z`, so its `z`-derivative does too. -/
private theorem pzProf_mul_abs_le_aux {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {L Npz : ℝ}
    (hp : 0 < pExp α) (hp1 : pExp α ≤ 1) (hL0 : 0 < L)
    (hsupp : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z → profFull α g z θ τ = 0)
    (hcont : ∀ θ' ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ' q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hnpz : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (gSlice g τ) z θ| ≤ Npz)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |z * pzProf α g z θ τ| ≤ max L 1 * (20 * pExp α + Npz) := by
  have hNpz0 : 0 ≤ Npz :=
    le_trans (abs_nonneg _) (hnpz τ hτ 0 0 le_rfl ⟨le_rfl, by linarith [Real.pi_pos]⟩)
  rcases le_or_gt z L with hzL | hzL
  · have hstar := pzFstar_abs_le_aux hp hp1 hz hθ
    have hsum : |pzProf α g z θ τ| ≤ 20 * pExp α + Npz := by
      rw [pzProf]
      exact abs_add_le_aux_prv.trans (add_le_add hstar (hnpz τ hτ z θ hz hθ))
    calc |z * pzProf α g z θ τ| = z * |pzProf α g z θ τ| := by
          rw [abs_mul, abs_of_nonneg hz]
      _ ≤ L * (20 * pExp α + Npz) := mul_le_mul hzL hsum (abs_nonneg _) hL0.le
      _ ≤ max L 1 * (20 * pExp α + Npz) :=
          mul_le_mul_of_nonneg_right (le_max_left L 1) (by linarith)
  · have hzero : pzProf α g z θ τ = 0 := by
      have hz1 : -1 < z := by linarith
      have hτmem : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hsplit := profFull_deriv_z_aux (α := α) (S := S) (g := g) (θ := θ) (z := z) (τ := τ)
        (hcont θ hθ) hz1 hτmem
      have hev : (fun z' : ℝ => profFull α g z' θ τ) =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [(isOpen_Ioi : IsOpen (Set.Ioi L)).mem_nhds hzL] with z' hz'
        exact hsupp τ hτ z' θ hz'.le
      have h0 : deriv (fun z' : ℝ => profFull α g z' θ τ) z = 0 := by
        rw [Filter.EventuallyEq.deriv_eq hev]
        simp
      rw [pzProf, ← hsplit]
      exact h0
    rw [hzero, mul_zero, abs_zero]
    exact mul_nonneg (le_trans zero_le_one (le_max_right L 1)) (by linarith)

/-- **The bound on the `τ`-derivative of the profile along the curve.**  Only the combination
`z·∂_zF` (with `z = ρ^{3α}/B τ`) enters, so the compact support of the profile enters through
`hpzProf` and the rest is the two-sided clock box. -/
private theorem profFull_curve_deriv_bound_aux {α : ℝ} {B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {ρ θ τ b₀ b₂ Npz Nd L : ℝ} (hρ : 0 ≤ ρ) (hθ : θ ∈ Work.Spaces.Iθ)
    (hBpos : 0 < B τ) (hb₀pos : 0 < b₀) (hb₀ : b₀ ≤ B τ) (hb₂ : |deriv B τ| ≤ b₂)
    (hb₂0 : 0 ≤ b₂) (hNd0 : 0 ≤ Nd)
    (hpzProf : |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) θ τ|
      ≤ max L 1 * (20 * pExp α + Npz))
    (hnd : |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| ≤ Nd) :
    |zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ
        + deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ|
      ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := by
  have hBne : B τ ≠ 0 := ne_of_gt hBpos
  have hz0 : 0 ≤ ρ ^ pExp α / B τ := div_nonneg (Real.rpow_nonneg hρ _) hBpos.le
  have hsl : |zSlope α B ρ τ| = (ρ ^ pExp α / B τ) * (|deriv B τ| / B τ) := by
    rw [zSlope, abs_neg, abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hρ _),
      abs_of_pos (pow_pos hBpos 2)]
    field_simp
  have hcoef : |deriv B τ| / B τ ≤ b₂ / b₀ :=
    (div_le_div_of_nonneg_right hb₂ hBpos.le).trans
      (div_le_div_of_nonneg_left hb₂0 hb₀pos hb₀)
  calc |zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ
        + deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ|
      ≤ |zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ τ|
          + |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| := abs_add_le _ _
    _ = |zSlope α B ρ τ| * |pzProf α g (ρ ^ pExp α / B τ) θ τ|
          + |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| := by
          rw [abs_mul]
    _ = (|deriv B τ| / B τ)
          * |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) θ τ|
          + |deriv (fun t => g (ρ ^ pExp α / B τ) θ t) τ| := by
          rw [hsl, abs_mul, abs_of_nonneg hz0]
          ring
    _ ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := by
          refine add_le_add ?_ hnd
          exact mul_le_mul hcoef hpzProf (abs_nonneg _) (div_nonneg hb₂0 hb₀pos.le)

/-! ### The chain rule for the odd-extended profile along the curve -/

/-- **The `τ`-derivative of the profile along `s ↦ (ρ^{3α}/B(s), s)`**, with the explicit value
`dProfOdd`.  This is the chain rule in the two variables `(z, τ)` — the diagonal curve moves in
both at once, so the joint `C¹` data `hcont` (not separate partial differentiability) is what is
used. -/
private theorem profOdd_hasDerivAt_aux {α S : ℝ} {B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {ρ θ τ : ℝ}
    (hθabs : |θ| ≤ Real.pi / 2) (hρ : 0 ≤ ρ)
    (hcont : ∀ θ' ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ' q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Ioo (-1) (S + 1)) (hBpos : 0 < B τ) (hBd : HasDerivAt B (deriv B τ) τ) :
    HasDerivAt (fun s => profOdd α g (ρ ^ pExp α / B s) θ s) (dProfOdd α B g ρ θ τ) τ := by
  have hBne : B τ ≠ 0 := ne_of_gt hBpos
  have hz0 : 0 ≤ ρ ^ pExp α / B τ := div_nonneg (Real.rpow_nonneg hρ _) hBpos.le
  have hz1 : -1 < ρ ^ pExp α / B τ := by linarith
  have hz : HasDerivAt (fun s : ℝ => ρ ^ pExp α / B s) (zSlope α B ρ τ) τ := by
    have h := (hasDerivAt_const τ (ρ ^ pExp α)).div hBd hBne
    rw [zSlope]
    exact h.congr_deriv (by ring)
  -- the core: the derivative for a fixed angle in `Iθ`
  have hcore : ∀ θ₁ : ℝ, θ₁ ∈ Work.Spaces.Iθ →
      HasDerivAt (fun s => profFull α g (ρ ^ pExp α / B s) θ₁ s)
        (zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ₁ τ
          + deriv (fun t => g (ρ ^ pExp α / B τ) θ₁ t) τ) τ := by
    intro θ₁ hθ₁
    have hF : HasDerivAt (fun s => Work.Construction.Fstar (pExp α) (ρ ^ pExp α / B s) θ₁)
        (Work.Spaces.pz (Work.Construction.Fstar (pExp α)) (ρ ^ pExp α / B τ) θ₁
          * zSlope α B ρ τ) τ :=
      HasDerivAt.comp (h := fun s : ℝ => ρ ^ pExp α / B s) τ
        (Work.ConstructionInstance.hasDerivAt_Fstar_z (ρ ^ pExp α / B τ) θ₁ hz1) hz
    have hG := gComp_hasDerivAt_aux hθ₁ (hcont θ₁ hθ₁) hτ hz1 hz
    have hsum := hF.add hG
    have heq : (fun s : ℝ => profFull α g (ρ ^ pExp α / B s) θ₁ s)
        = fun s => Work.Construction.Fstar (pExp α) (ρ ^ pExp α / B s) θ₁
            + g (ρ ^ pExp α / B s) θ₁ s := by
      funext s; exact profFull_apply α g _ θ₁ s
    rw [heq]
    refine hsum.congr_deriv ?_
    rw [pzProf]
    ring
  rw [dProfOdd]
  by_cases hθ0 : 0 ≤ θ
  · rw [if_pos hθ0]
    have hθ₁ : θ ∈ Work.Spaces.Iθ := ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩
    have heq : (fun s : ℝ => profOdd α g (ρ ^ pExp α / B s) θ s)
        = fun s => profFull α g (ρ ^ pExp α / B s) θ s := by
      funext s; rw [profOdd, if_pos hθ0]
    rw [heq]
    exact hcore θ hθ₁
  · rw [if_neg hθ0]
    have hθ₁ : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith [not_le.mp hθ0], by linarith [neg_le_abs θ, hθabs]⟩
    have hneg := (hcore (-θ) hθ₁).neg
    have heq : (fun s : ℝ => profOdd α g (ρ ^ pExp α / B s) θ s)
        = fun s => -profFull α g (ρ ^ pExp α / B s) (-θ) s := by
      funext s; rw [profOdd, if_neg hθ0]
    rw [heq]
    exact hneg

/-! ### The main theorem -/

theorem physVort_hasDerivAt_and_bound {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    (∀ x : Work.FTS.Regularity.R3, ∀ τ ∈ Set.Icc 0 S,
        HasDerivAt (fun s => Work.FTS.Regularity.physVort α A B g x s)
          (FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x τ) τ) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ x : Work.FTS.Regularity.R3,
        ‖FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x τ‖ ≤ M) := by
  classical
  obtain ⟨a₀, a₁, ha₀pos, hAb⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀pos, hBb⟩ := h.hBb
  obtain ⟨a₂, hAd⟩ := h.hAd
  obtain ⟨b₂, hBd⟩ := h.hBd
  obtain ⟨Ng, hNg⟩ := h.hg
  obtain ⟨Npz, hNpz⟩ := h.hpz
  obtain ⟨Nd, hNd⟩ := h.hgdoth
  obtain ⟨L, hLpos, hLsupp⟩ := h.hsupp
  have hp : 0 < pExp α := h.pExp_pos
  have hp1 : pExp α ≤ 1 := h.pExp_le_one
  have hS0 : 0 ≤ S := h.hS.le
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) S := ⟨le_rfl, hS0⟩
  have hNg0 : 0 ≤ Ng := hNg.1
  have hNpz0 : 0 ≤ Npz := hNpz.1
  have hNd0 : 0 ≤ Nd := hNd.1
  have ha₂0 : 0 ≤ a₂ := le_trans (abs_nonneg _) (hAd 0 h0mem)
  have hb₂0 : 0 ≤ b₂ := le_trans (abs_nonneg _) (hBd 0 h0mem)
  set M : ℝ := a₀⁻¹ * (b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) + Nd)
      + (a₂ / a₀ ^ 2) * (20 * pExp α + Ng) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have h1 : (0 : ℝ) ≤ max L 1 := le_trans zero_le_one (le_max_right L 1)
    have h2 : (0 : ℝ) ≤ 20 * pExp α + Npz := by linarith
    have h3 : (0 : ℝ) ≤ 20 * pExp α + Ng := by linarith
    positivity
  -- the three constants of the derivative bound
  have hdu : ∀ τ ∈ Set.Icc 0 S, ∀ ρ θ : ℝ, 0 ≤ ρ → |θ| ∈ Work.Spaces.Iθ →
      |dProfOdd α B g ρ θ τ|
        ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := by
    intro τ hτ ρ θ hρ hθmem
    have hθabs : |θ| ≤ Real.pi / 2 := hθmem.2
    have hBτ : 0 < B τ := h.hB τ hτ
    have hBτ₀ : b₀ ≤ B τ := (hBb τ hτ).1
    have hz0 : 0 ≤ ρ ^ pExp α / B τ := div_nonneg (Real.rpow_nonneg hρ _) hBτ.le
    have hpzProf : ∀ θ₁ ∈ Work.Spaces.Iθ,
        |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) θ₁ τ|
          ≤ max L 1 * (20 * pExp α + Npz) := fun θ₁ hθ₁ =>
      pzProf_mul_abs_le_aux hp hp1 hLpos hLsupp h.hcont
        (fun τ' hτ' z θ' hz' hθ' => hNpz.abs_le hz' hθ' hτ') hτ hz0 hθ₁
    rw [dProfOdd]
    split_ifs with hθ0
    · exact profFull_curve_deriv_bound_aux hρ ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩ hBτ hb₀pos
        hBτ₀ (hBd τ hτ) hb₂0 hNd0
        (hpzProf θ ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩)
        (hNd.abs_le hz0 ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩ hτ)
    · rw [abs_neg]
      have hθ₁ : -θ ∈ Work.Spaces.Iθ :=
        ⟨by linarith [not_le.mp hθ0], by linarith [neg_le_abs θ, hθabs]⟩
      exact profFull_curve_deriv_bound_aux hρ hθ₁ hBτ hb₀pos hBτ₀ (hBd τ hτ) hb₂0 hNd0
        (hpzProf (-θ) hθ₁) (hNd.abs_le hz0 hθ₁ hτ)
  -- the derivative
  have hder : ∀ x : R3, ∀ τ ∈ Set.Icc 0 S,
      HasDerivAt (fun s => physVort α A B g x s) (vortDt α A B g x τ) τ := by
    intro x τ hτ
    have hmem : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2, h.hS]⟩
    have hscal := profOdd_hasDerivAt_aux (α := α) (S := S) (B := B) (g := g)
      (ρ := Work.Cyl.rho x) (θ := Work.Cyl.theta x) (τ := τ)
      (abs_theta_mem_Iθ_aux x).2 (Work.Cyl.rho_nonneg x) h.hcont hmem
      (h.hB τ hτ) (h.hBdiff τ hτ)
    have hvec := hscal.smul_const (Work.Cyl.eTheta x)
    have hAinv : HasDerivAt (fun s : ℝ => (A s)⁻¹) (-(deriv A τ) / (A τ) ^ 2) τ :=
      (h.hAdiff τ hτ).inv (ne_of_gt (h.hA τ hτ))
    have hprod := hAinv.smul hvec
    have heq : (fun s : ℝ => physVort α A B g x s)
        = fun s : ℝ => (A s)⁻¹ • (profOdd α g (Work.Cyl.rho x ^ pExp α / B s)
            (Work.Cyl.theta x) s • Work.Cyl.eTheta x) := by
      funext s; rw [physVort_eq_smul]
    rw [heq, vortDt]
    exact hprod
  have htimeDeriv : ∀ x : R3, ∀ τ ∈ Set.Icc 0 S,
      FiniteTimeSingularity.timeDeriv (physVort α A B g) x τ = vortDt α A B g x τ := by
    intro x τ hτ
    rw [physVort_timeDeriv]
    exact (hder x τ hτ).deriv
  refine ⟨?_, ⟨M, hM0, ?_⟩⟩
  · intro x τ hτ
    rw [htimeDeriv x τ hτ]
    exact hder x τ hτ
  · intro τ hτ x
    have hAτ : 0 < A τ := h.hA τ hτ
    rw [htimeDeriv x τ hτ, vortDt]
    set ρ := Work.Cyl.rho x with hρdef
    set θ := Work.Cyl.theta x with hθdef
    set e : R3 := Work.Cyl.eTheta x with hedef
    have hρ0 : 0 ≤ ρ := Work.Cyl.rho_nonneg x
    have hθmem : |θ| ∈ Work.Spaces.Iθ := by rw [hθdef]; exact abs_theta_mem_Iθ_aux x
    have he1 : ‖e‖ ≤ 1 := by rw [hedef]; exact norm_eTheta_le_one_aux x
    have hAinv_le : (A τ)⁻¹ ≤ a₀⁻¹ := (inv_le_inv₀ hAτ ha₀pos).mpr ((hAb τ hτ).1)
    have hA2_le : |deriv A τ| / (A τ) ^ 2 ≤ a₂ / a₀ ^ 2 := by
      refine (div_le_div_of_nonneg_right (hAd τ hτ) (pow_pos hAτ 2).le).trans ?_
      exact div_le_div_of_nonneg_left ha₂0 (pow_pos ha₀pos 2)
        (pow_le_pow_left₀ ha₀pos.le (hAb τ hτ).1 2)
    have hu : ‖profOdd α g (ρ ^ pExp α / B τ) θ τ • e‖ ≤ 20 * pExp α + Ng :=
      calc ‖profOdd α g (ρ ^ pExp α / B τ) θ τ • e‖
          = |profOdd α g (ρ ^ pExp α / B τ) θ τ| * ‖e‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |profOdd α g (ρ ^ pExp α / B τ) θ τ| * 1 :=
            mul_le_mul_of_nonneg_left he1 (abs_nonneg _)
        _ = |profOdd α g (ρ ^ pExp α / B τ) θ τ| := mul_one _
        _ ≤ 20 * pExp α + Ng :=
            profOdd_abs_le_aux hp hp1 hNg
              (div_nonneg (Real.rpow_nonneg hρ0 _) (h.hB τ hτ).le) hθmem hτ
    have hduE : ‖dProfOdd α B g ρ θ τ • e‖
        ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd :=
      calc ‖dProfOdd α B g ρ θ τ • e‖ = |dProfOdd α B g ρ θ τ| * ‖e‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |dProfOdd α B g ρ θ τ| * 1 := mul_le_mul_of_nonneg_left he1 (abs_nonneg _)
        _ = |dProfOdd α B g ρ θ τ| := mul_one _
        _ ≤ (b₂ / b₀) * (max L 1 * (20 * pExp α + Npz)) + Nd := hdu τ hτ ρ θ hρ0 hθmem
    have hcoef1 : 0 ≤ b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) + Nd := by
      have h : 0 ≤ b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) :=
        mul_nonneg (div_nonneg hb₂0 hb₀pos.le)
          (mul_nonneg (le_trans zero_le_one (le_max_right L 1)) (by linarith))
      linarith
    have hcoef2 : 0 ≤ 20 * pExp α + Ng := by linarith
    calc ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
          + (-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)‖
        ≤ ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)‖
            + ‖(-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)‖ :=
          norm_add_le _ _
      _ = (A τ)⁻¹ * ‖dProfOdd α B g ρ θ τ • e‖
            + |deriv A τ| / (A τ) ^ 2 * ‖profOdd α g (ρ ^ pExp α / B τ) θ τ • e‖ := by
          congr 1
          · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hAτ.le)]
          · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (pow_pos hAτ 2)]
      _ ≤ a₀⁻¹ * (b₂ / b₀ * (max L 1 * (20 * pExp α + Npz)) + Nd)
            + (a₂ / a₀ ^ 2) * (20 * pExp α + Ng) :=
          add_le_add (mul_le_mul hAinv_le hduE (norm_nonneg _) (inv_nonneg.mpr ha₀pos.le))
            (mul_le_mul hA2_le hu (norm_nonneg _) (div_nonneg ha₂0 (pow_pos ha₀pos 2).le))
      _ = M := by rw [hMdef]

end Work.FTS.FireFix.Prime
end
end
-- ===== merged: Submission.Work.FTS.FireFix.Prime.physVort_support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-! ## Compact support of the physical vorticity

The physical vorticity of the route is

  `physVort α A B g x τ = A(τ)⁻¹ · F(ρ(x)^{3α}/B(τ), θ(x), τ) · e_θ(x)`,

so it vanishes wherever the *profile* `F = F_* + g` does.  The interface `RegPkg'` supplies the
compact support of the full profile in the self-similar variable `z`, uniformly on the strip
(`hsupp`), and the two-sided bound `B τ ≤ b₁` (`hBb`).  Hence the physical vorticity is supported
in a ball whose radius is controlled by `L · b₁` and the profile exponent `3α`.

The only two ingredients are (i) the dictionary between the profile of a `τ`-slice
(`ConstructionInstance.profile`) and the full profile `profFull`, and (ii) the elementary
observation that `t ^ s ≤ c` with `t ≥ 0`, `s > 0`, `c ≥ 0` forces `t ≤ max 1 (c ^ s⁻¹)`. -/

/-- The profile of a `τ`-slice agrees with the full profile `profFull` on the physical half plane
`0 ≤ θ`. -/
private lemma profile_gSlice_eq_profFull (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ)
    (hθ : 0 ≤ θ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ = profFull α g z θ τ := by
  rw [Work.ConstructionInstance.profile_of_nonneg hθ]
  rfl

/-- Off the physical half plane `θ ≥ 0` the profile of a `τ`-slice is the odd extension of the
full profile. -/
private lemma profile_gSlice_eq_neg_profFull (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ)
    (hθ : ¬ 0 ≤ θ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ
      = - profFull α g z (-θ) τ := by
  rw [Work.ConstructionInstance.profile_of_neg hθ]
  rfl

/-- If `t ≥ 0` and `t ^ s ≤ c` with `s > 0` and `c ≥ 0`, then `t ≤ max 1 (c ^ s⁻¹)`. -/
private lemma le_max_one_rpow_inv {s c t : ℝ} (hs : 0 < s) (_hc : 0 ≤ c) (ht : 0 ≤ t)
    (h : t ^ s ≤ c) : t ≤ max 1 (c ^ (1 / s)) := by
  rcases le_or_gt t 1 with h1 | h1
  · exact le_trans h1 (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    calc t = (t ^ s) ^ (1 / s) := by
          rw [← Real.rpow_mul ht s (1 / s), mul_one_div_cancel (ne_of_gt hs), Real.rpow_one]
      _ ≤ c ^ (1 / s) := Real.rpow_le_rpow (Real.rpow_nonneg ht s) h (by positivity)

/-- **The physical vorticity of a `RegPkg'` profile is compactly supported, uniformly on the
strip `[0,S]`.**  The radius is `max 1 ((L · b₁) ^ (3α)⁻¹)`, where `L` bounds the support of the
full profile in `z` and `b₁` bounds the clock `B` above. -/
theorem physVort_support {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ Set.Icc 0 S, ∀ y : Work.FTS.Regularity.R3,
      Work.FTS.Regularity.physVort α A B g y τ ≠ 0 → y ∈ Metric.closedBall 0 R := by
  obtain ⟨L, hLpos, hL⟩ := h.hsupp
  obtain ⟨b₀, b₁, hb₀pos, hBb⟩ := h.hBb
  have h0 : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_rfl, h.hS.le⟩
  have hb₁pos : 0 < b₁ := lt_of_lt_of_le hb₀pos (le_trans (hBb 0 h0).1 (hBb 0 h0).2)
  refine ⟨max 1 ((L * b₁) ^ (1 / pExp α)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro τ hτ y hy
  simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  -- the profile at the rescaled self-similar variable must be non-zero
  have hpne : Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
      (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y) ≠ 0 := by
    intro hz
    refine hy ?_
    rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply, hz]
    simp
  -- hence the self-similar variable lies below the support radius `L`
  have hzL : Work.Cyl.rho y ^ pExp α / B τ ≤ L := by
    rcases le_or_gt 0 (Work.Cyl.theta y) with hθ | hθ
    · rw [profile_gSlice_eq_profFull α g τ _ _ hθ] at hpne
      by_contra hc
      exact hpne (hL τ hτ _ (Work.Cyl.theta y) (not_le.mp hc).le)
    · rw [profile_gSlice_eq_neg_profFull α g τ _ _ (not_le.mpr hθ), neg_ne_zero] at hpne
      by_contra hc
      exact hpne (hL τ hτ _ (-(Work.Cyl.theta y)) (not_le.mp hc).le)
  -- convert it into a bound on `ρ(y)`, using `B τ ≤ b₁`
  have hBτ : 0 < B τ := lt_of_lt_of_le hb₀pos (hBb τ hτ).1
  have hle : Work.Cyl.rho y ^ pExp α ≤ L * b₁ :=
    ((div_le_iff₀ hBτ).mp hzL).trans (mul_le_mul_of_nonneg_left (hBb τ hτ).2 hLpos.le)
  rw [← Work.Cyl.rho_eq_norm y]
  exact le_max_one_rpow_inv (pExp_pos h.hα) (mul_nonneg hLpos.le hb₁pos.le)
    (Work.Cyl.rho_nonneg y) hle

end Work.FTS.FireFix.Prime
end
end
-- ===== merged: Submission.Work.FTS.FireFix.Prime.profFullBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-- **The uniform bound of the full profile `F = F_* + g`.**  For every regularity package
`RegPkg' α S A B g` there is a constant `M ≥ 0` with `|F(z,θ,τ)| ≤ M` for all `τ ∈ [0,S]`,
`z ≥ 0` and `θ ∈ Iθ`.  Since `pExp α = 3α ≤ 1` and `Γ ≤ 1` on `Iθ`, the explicit choice
`M = 20·(3α) + Cv` works, where `Cv` is the `L^∞` bound of `g` extracted from the angular
vanishing datum. -/
theorem profFullBounds {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |profFull α g z θ τ| ≤ M := by
  obtain ⟨Cv, hCv0, hCv⟩ := h.abs_le_Cv
  have hp : 0 < pExp α := h.pExp_pos
  have hp1 : pExp α ≤ 1 := h.pExp_le_one
  refine ⟨20 * pExp α + Cv, by positivity, fun τ hτ z θ hz hθ => ?_⟩
  have hGam1 : Gamma (pExp α / 3) θ ≤ 1 :=
    Work.ConstructionInstance.Gamma_le_one (by positivity) hθ
  have hF := Work.ConstructionInstance.Fstar_abs_le hp hp1 hz hθ
  have hG := hCv τ hτ z θ hz hθ
  rw [profFull_apply]
  calc |Work.Construction.Fstar (pExp α) z θ + g z θ τ|
      ≤ |Work.Construction.Fstar (pExp α) z θ| + |g z θ τ| := abs_add_le _ _
    _ ≤ 20 * pExp α * Gamma (pExp α / 3) θ + Cv := add_le_add hF hG
    _ ≤ 20 * pExp α + Cv := by
        have h1 : 20 * pExp α * Gamma (pExp α / 3) θ ≤ 20 * pExp α := by
          simpa using mul_le_mul_of_nonneg_left hGam1 (show (0 : ℝ) ≤ 20 * pExp α by positivity)
        linarith

end Work.FTS.FireFix.Prime
end
-- ===== merged: Submission.Work.FTS.Open2.Bridge2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.Open2

open Work.FTS.Apriori
open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.OpenPkg
open Work.FTS.OpenPkg.AprioriOpen
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000



end Work.FTS.Open2
end
end
-- ===== merged: Submission.Work.FTS.Open2.Compat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Open2

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif)

set_option autoImplicit false
set_option linter.unusedVariables false




end Work.FTS.Open2
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FamLopAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- `famC k = (∏_{i<k} (3/2 + i)) / k!` for `k ≥ 0`, and `0` for `k < 0`. -/
noncomputable def famC (k : ℤ) : ℝ :=
  if 0 ≤ k then (∏ i ∈ Finset.range k.toNat, ((3 : ℝ) / 2 + i)) / ((Nat.factorial k.toNat : ℕ) : ℝ) else 0



/-- The trigonometric form of the `n`-th Gegenbauer polynomial:
`famTrig n ψ = Σ_{j ≤ n} famC j · famC (n - j) · cos ((2j - n) ψ)`. -/
noncomputable def famTrig (n : ℕ) (ψ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    famC (j : ℤ) * famC ((n : ℤ) - (j : ℤ)) * Real.cos (((2 : ℝ) * (j : ℝ) - (n : ℝ)) * ψ)

end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.PhiStar.Linv23Aux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- The regularised integrand `sin t · cos² t · h t / 2` of the primitive entering `Linv h`. -/
def LinvPhiInt (h : ℝ → ℝ) : ℝ → ℝ := fun t => Real.sin t * Real.cos t ^ 2 / 2 * h t

/-- The primitive `θ ↦ ∫_0^θ sin t cos² t h t / 2`; `Linv h` is its `σ`-normalisation
`-(sin² θ cos³ θ)⁻¹ · LinvPhi h θ` (`Linv_eq`). -/
def LinvPhi (h : ℝ → ℝ) : ℝ → ℝ := fun θ => ∫ t in (0 : ℝ)..θ, LinvPhiInt h t

/-- The quotient integrand of `Linv` equals the regular one **everywhere**:
`sin² t cos³ t / sin (2t) = sin t cos² t / 2` (both sides are `0` when `sin t · cos t = 0`). -/
theorem sin_sq_cos_cube_div_s2 (t : ℝ) :
    Real.sin t ^ 2 * Real.cos t ^ 3 / Work.Construction.s2 t
      = Real.sin t * Real.cos t ^ 2 / 2 := by
  rw [Work.Construction.s2_eq, Real.sin_two_mul]
  by_cases hs : Real.sin t = 0
  · simp [hs]
  by_cases hc : Real.cos t = 0
  · simp [hc]
  · field_simp

/-- The definitional content of `Linv`, in regularised form.
(Named `Linv_eq_phi` — **not** `Linv_eq` — because the pointwise zero-moment inverse identity
`Linv_eq` already exists in `Work.FTS.PhiStar` (`PhiStar/LinvI_solves.lean`, in the function
form `Linv h = fun θ => ...`); two declarations of the same name would make it impossible to
import `Linv23Aux` and `LinvI_solves` together.) -/
theorem Linv_eq_phi (h : ℝ → ℝ) (θ : ℝ) :
    Linv h θ = -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * LinvPhi h θ) := by
  have key : (∫ t in (0 : ℝ)..θ,
        Real.sin t ^ 2 * Real.cos t ^ 3 * h t / Work.Construction.s2 t)
      = ∫ t in (0 : ℝ)..θ, LinvPhiInt h t := by
    apply intervalIntegral.integral_congr
    intro t _
    change Real.sin t ^ 2 * Real.cos t ^ 3 * h t / Work.Construction.s2 t
      = Real.sin t * Real.cos t ^ 2 / 2 * h t
    rw [show Real.sin t ^ 2 * Real.cos t ^ 3 * h t / Work.Construction.s2 t
          = (Real.sin t ^ 2 * Real.cos t ^ 3 / Work.Construction.s2 t) * h t from by ring,
      sin_sq_cos_cube_div_s2 t]
  simp only [Linv, LinvPhi, LinvPhiInt, key]

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.LinvFlat.LinvBaseBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.PhiStar.LinvFlat

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The uniform bound `|Linv h| ≤ 4K` -/

lemma LI_lc_sinCos2_nonneg {t : ℝ} (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Work.Elliptic.sinCos2 t := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le
    (by linarith [ht.2, Real.pi_pos])) (sq_nonneg _)

lemma LI_lc_integrand_eq (h : ℝ → ℝ) (t : ℝ) :
    Real.sin t ^ 2 * Real.cos t ^ 3 * h t / Work.Construction.s2 t
      = (1 / 2) * (h t * Work.Elliptic.sinCos2 t) := by
  rw [Work.Elliptic.sinCos2, Work.Construction.s2_eq, Real.sin_two_mul]
  by_cases hs : Real.sin t = 0
  · simp [hs]
  · by_cases hc : Real.cos t = 0
    · simp [hc]
    · field_simp

lemma LI_lc_Linv_eq (h : ℝ → ℝ) (θ : ℝ) :
    Work.FTS.PhiStar.Linv h θ
      = -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ *
          ((1 / 2) * ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t)) := by
  have hint : (∫ θ' in (0 : ℝ)..θ,
        Real.sin θ' ^ 2 * Real.cos θ' ^ 3 * h θ' / Work.Construction.s2 θ')
      = (1 / 2) * ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t := by
    rw [intervalIntegral.integral_congr (fun t _ => LI_lc_integrand_eq h t),
        intervalIntegral.integral_const_mul]
  simp only [Work.FTS.PhiStar.Linv]
  rw [hint]

lemma LI_lc_intervalIntegrable_moment {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π / 2) (hab : a ≤ b) :
    IntervalIntegrable (fun t => h t * Work.Elliptic.sinCos2 t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine hint.mono_set ?_
  intro t ht
  exact ⟨le_trans ha ht.1.le, le_trans ht.2 hb⟩

lemma LI_lc_interval_bound {h : ℝ → ℝ} {K : ℝ}
    (hbd : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |h θ| ≤ K)
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π / 2) (hab : a ≤ b) :
    |∫ t in a..b, h t * Work.Elliptic.sinCos2 t|
      ≤ K * ∫ t in a..b, Work.Elliptic.sinCos2 t := by
  have hf : IntervalIntegrable (fun t => |h t * Work.Elliptic.sinCos2 t|) volume a b :=
    (LI_lc_intervalIntegrable_moment hint ha hb hab).abs
  have hg : IntervalIntegrable (fun t => K * Work.Elliptic.sinCos2 t) volume a b :=
    (continuous_const.mul (by unfold Work.Elliptic.sinCos2; fun_prop)).intervalIntegrable a b
  have hpoint : ∀ x ∈ Set.Ioo a b,
      |h x * Work.Elliptic.sinCos2 x| ≤ K * Work.Elliptic.sinCos2 x := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
    have hnn : 0 ≤ Work.Elliptic.sinCos2 x := LI_lc_sinCos2_nonneg hx'
    rw [abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right (hbd x hx') hnn
  calc |∫ t in a..b, h t * Work.Elliptic.sinCos2 t|
      ≤ ∫ t in a..b, |h t * Work.Elliptic.sinCos2 t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, K * Work.Elliptic.sinCos2 t :=
        intervalIntegral.integral_mono_on_of_le_Ioo hab hf hg hpoint
    _ = K * ∫ t in a..b, Work.Elliptic.sinCos2 t := intervalIntegral.integral_const_mul K _

lemma LI_lc_hasDerivAt_cos3 (y : ℝ) :
    HasDerivAt (fun x => -(Real.cos x ^ 3) / 3) (Real.sin y * Real.cos y ^ 2) y := by
  have h1 := (Real.hasDerivAt_cos y).pow 3
  have h2 := h1.const_mul (-(1 / 3) : ℝ)
  convert h2 using 1
  · funext x; simp only [Pi.pow_apply]; ring
  · ring_nf

lemma LI_lc_integral_sinCos2 (a b : ℝ) :
    ∫ t in a..b, Work.Elliptic.sinCos2 t = (Real.cos a ^ 3 - Real.cos b ^ 3) / 3 := by
  have hcont : IntervalIntegrable (fun t => Real.sin t * Real.cos t ^ 2) volume a b :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => -(Real.cos x ^ 3) / 3)
    (f' := fun x => Real.sin x * Real.cos x ^ 2)
    (fun x _ => LI_lc_hasDerivAt_cos3 x) hcont
  change ∫ t in a..b, Real.sin t * Real.cos t ^ 2 = _
  rw [h]
  ring

lemma LI_lc_moment_zero {h : ℝ → ℝ}
    (hmom : (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∫ t in (0 : ℝ)..(π / 2), h t * Work.Elliptic.sinCos2 t = 0 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)] at hmom
  exact hmom

/-- The uniform base bound: `|Linv h θ| ≤ 4 K`, with a constant independent of `h` and `K`. -/
lemma LI_lc_abs_le (h : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hbd : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |h θ| ≤ K)
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, h θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |Work.FTS.PhiStar.Linv h θ| ≤ 4 * K := by
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ2 : θ < π / 2 := hθ.2
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcospos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩
  have hden : 0 < Real.sin θ ^ 2 * Real.cos θ ^ 3 :=
    mul_pos (pow_pos hsinpos 2) (pow_pos hcospos 3)
  rw [LI_lc_Linv_eq h θ]
  set J : ℝ := ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t with hJdef
  have habs : |-( (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * ((1 / 2) * J))|
      = (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * |J| := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hden),
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  rw [habs]
  by_cases hcase : θ ≤ π / 4
  · -- small angles
    have hJ : |J| ≤ K * (1 - Real.cos θ ^ 3) / 3 := by
      have hb := LI_lc_interval_bound hbd hint (a := 0) (b := θ) le_rfl hθ2.le hθ0.le
      have hb2 : K * ∫ t in (0 : ℝ)..θ, Work.Elliptic.sinCos2 t
          = K * (1 - Real.cos θ ^ 3) / 3 := by
        rw [LI_lc_integral_sinCos2 0 θ, Real.cos_zero]
        ring
      rw [hb2] at hb
      rw [hJdef]
      exact hb
    have hres : |J| ≤ K * Real.sin θ ^ 2 := by
      have h1 : (1 - Real.cos θ ^ 3) / 3 ≤ Real.sin θ ^ 2 := by
        have hs2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq θ
        have hfac : 3 * Real.sin θ ^ 2 - (1 - Real.cos θ ^ 3)
            = (1 - Real.cos θ) * (2 + 2 * Real.cos θ - Real.cos θ ^ 2) := by
          rw [hs2]; ring
        have hn1 : (0 : ℝ) ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
        have hn2 : (0 : ℝ) ≤ 2 + 2 * Real.cos θ - Real.cos θ ^ 2 := by
          nlinarith [hcospos, Real.cos_le_one θ]
        have hnn := mul_nonneg hn1 hn2
        linarith
      calc |J| ≤ K * (1 - Real.cos θ ^ 3) / 3 := hJ
        _ = K * ((1 - Real.cos θ ^ 3) / 3) := by ring
        _ ≤ K * Real.sin θ ^ 2 := mul_le_mul_of_nonneg_left h1 hK
    have hc12 : (1 : ℝ) / 2 ≤ Real.cos θ := by
      have h1 : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos (x := θ)
      have hpi : Real.pi ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
      have h2 : θ ^ 2 / 2 ≤ (1 : ℝ) / 2 := by
        have h3 : θ ^ 2 ≤ (Real.pi / 4) ^ 2 := by nlinarith [hθ0.le, hcase]
        nlinarith [Real.pi_pos]
      linarith
    have hfin : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.sin θ ^ 2) ≤ 4 * K := by
      have hx : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.sin θ ^ 2)
          = K / (2 * Real.cos θ ^ 3) := by
        field_simp [hsinpos.ne', hcospos.ne']
      rw [hx]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.cos θ ^ 3)]
      have hc3 : (1 : ℝ) / 8 ≤ Real.cos θ ^ 3 := by
        have hpp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2) hc12 3
        norm_num at hpp
        exact hpp
      nlinarith [hK, hc3]
    have step : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * |J|
        ≤ (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.sin θ ^ 2) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    linarith [step, hfin]
  · -- large angles
    have hcase' : π / 4 < θ := not_le.mp hcase
    have hJ : |J| ≤ K * Real.cos θ ^ 3 / 3 := by
      have hmom0 : ∫ t in (0 : ℝ)..(π / 2), h t * Work.Elliptic.sinCos2 t = 0 :=
        LI_lc_moment_zero hmom
      have hI1 : IntervalIntegrable (fun t => h t * Work.Elliptic.sinCos2 t) volume 0 θ :=
        LI_lc_intervalIntegrable_moment hint le_rfl hθ2.le hθ0.le
      have hI2 : IntervalIntegrable (fun t => h t * Work.Elliptic.sinCos2 t) volume θ (π / 2) :=
        LI_lc_intervalIntegrable_moment hint hθ0.le le_rfl hθ2.le
      have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
      have hb := LI_lc_interval_bound hbd hint (a := θ) (b := π / 2) hθ0.le le_rfl hθ2.le
      have hb2 : K * ∫ t in θ..(π / 2), Work.Elliptic.sinCos2 t
          = K * Real.cos θ ^ 3 / 3 := by
        rw [LI_lc_integral_sinCos2 θ (π / 2), Real.cos_pi_div_two]
        ring
      rw [hb2] at hb
      rw [hJdef]
      have heq : ∫ t in (0 : ℝ)..θ, h t * Work.Elliptic.sinCos2 t
          = -(∫ t in θ..(π / 2), h t * Work.Elliptic.sinCos2 t) := by linarith
      rw [heq, abs_neg]
      exact hb
    have hsin12 : (1 : ℝ) / 2 ≤ Real.sin θ := by
      have h1 : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ0.le hθ2.le
      have h2 : (1 : ℝ) / 2 ≤ 2 / Real.pi * θ := by
        rw [show (2 : ℝ) / Real.pi * θ = 2 * θ / Real.pi from by ring,
            le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi)]
        nlinarith [hcase']
      linarith
    have hfin : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.cos θ ^ 3 / 3)
        ≤ 4 * K := by
      have hx : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.cos θ ^ 3 / 3)
          = K / (6 * Real.sin θ ^ 2) := by
        field_simp [hsinpos.ne', hcospos.ne']; ring
      rw [hx]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 6 * Real.sin θ ^ 2)]
      have hs2 : (1 : ℝ) / 4 ≤ Real.sin θ ^ 2 := by
        have hpp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2) hsin12 2
        norm_num at hpp
        exact hpp
      nlinarith [hK, hs2]
    have step : (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * |J|
        ≤ (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (1 / 2) * (K * Real.cos θ ^ 3 / 3) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    linarith [step, hfin]


end Work.FTS.PhiStar.LinvFlat
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.LinvFlat.LinvLopAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.PhiStar.LinvFlat

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The coefficient function `L₂` -/

/-- `L₂ θ = 5 cos 2θ − 1 = 2(2cos²θ − 3sin²θ)`. -/
def LI_L2fun (θ : ℝ) : ℝ := 5 * Real.cos (2 * θ) - 1

lemma LI_L2fun_eq (θ : ℝ) : LI_L2fun θ = 2 * (2 * Real.cos θ ^ 2 - 3 * Real.sin θ ^ 2) := by
  rw [show LI_L2fun θ = 5 * Real.cos (2 * θ) - 1 from rfl, Real.cos_two_mul, Real.sin_sq]
  ring

lemma contDiffOn_LI_L2fun (k : ℕ) {U : Set ℝ} :
    ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) LI_L2fun U := by
  show ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (fun θ : ℝ => 5 * Real.cos (2 * θ) - 1) U
  fun_prop

/-- The `Lop`-iterates of `L₂` are uniformly bounded up to order `7`. -/
lemma LI_L2fun_lop_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℕ, a ≤ 7 → ∀ θ : ℝ,
      |(Work.Spaces.Lop^[a]) LI_L2fun θ| ≤ M := by
  have hbase : LopTrig.TP (fun θ : ℝ => 5 * Real.cos (2 * θ) + (-1) *
      (Real.sin (2 * θ) * Real.sin (2 * θ) + Real.cos (2 * θ) * Real.cos (2 * θ))) :=
    LopTrig.TP.add (LopTrig.TP.smul 5 LopTrig.TP.cos2)
      (LopTrig.TP.smul (-1) (LopTrig.TP.add (LopTrig.TP.mul LopTrig.TP.sin2 LopTrig.TP.sin2)
        (LopTrig.TP.mul LopTrig.TP.cos2 LopTrig.TP.cos2)))
  have hTP : LopTrig.TP LI_L2fun := by
    have heq : (fun θ : ℝ => 5 * Real.cos (2 * θ) + (-1) *
        (Real.sin (2 * θ) * Real.sin (2 * θ)
          + Real.cos (2 * θ) * Real.cos (2 * θ))) = LI_L2fun := by
      funext θ
      rw [show LI_L2fun θ = 5 * Real.cos (2 * θ) - 1 from rfl]
      have hs : Real.sin (2 * θ) * Real.sin (2 * θ)
          + Real.cos (2 * θ) * Real.cos (2 * θ) = 1 := by
        have h1 := Real.sin_sq_add_cos_sq (2 * θ)
        rw [pow_two, pow_two] at h1
        exact h1
      rw [hs]
      ring
    rw [heq] at hbase
    exact hbase
  have hTPa : ∀ a : ℕ, LopTrig.TP ((Work.Spaces.Lop^[a]) LI_L2fun) := by
    intro a
    induction a with
    | zero => simpa [Function.iterate_zero_apply] using hTP
    | succ a ih => rw [Function.iterate_succ_apply']; exact LopTrig.TP_lop ih
  choose B hB using fun a => LopTrig.TP_bdd (hTPa a)
  refine ⟨∑ a ∈ Finset.range 8, B a, Finset.sum_nonneg (fun a _ => (hB a).1), ?_⟩
  intro a ha θ
  have hmem : a ∈ Finset.range 8 := Finset.mem_range.mpr (Nat.lt_succ_of_le ha)
  exact le_trans ((hB a).2 θ) (Finset.single_le_sum (fun i _ => (hB i).1) hmem)

/-! ## Smoothness bookkeeping for `Lop` -/

/-- `Lop` costs one order of smoothness on an open set. -/
lemma LI_contDiffOn_Lop {m : ℕ} {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) f U) :
    ContDiffOn ℝ (m : ℕ∞ω) (Work.Spaces.Lop f) U := by
  have hd : ContDiffOn ℝ (m : ℕ∞ω) (deriv f) U := hf.deriv_of_isOpen hU (le_refl _)
  have hs : ContDiffOn ℝ (m : ℕ∞ω) (fun θ : ℝ => Real.sin (2 * θ)) U := by fun_prop
  have h := hs.mul hd
  change ContDiffOn ℝ (m : ℕ∞ω) (fun θ : ℝ => Real.sin (2 * θ) * deriv f θ) U
  exact h

/-- `Lop^[a]` costs `a` orders of smoothness. -/
lemma LI_LI_contDiffOn_Lop_iter {N : ℕ} {u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ (N : ℕ∞ω) u U) :
    ∀ a ≤ N, ContDiffOn ℝ ((N - a : ℕ) : ℕ∞ω) (Work.Spaces.Lop^[a] u) U := by
  intro a
  induction a with
  | zero => intro _; simpa [Function.iterate_zero_apply, Nat.sub_zero] using hu
  | succ a ih =>
      intro ha
      have ha' : a ≤ N := Nat.le_of_succ_le ha
      have hih : ContDiffOn ℝ ((N - a : ℕ) : ℕ∞ω) (Work.Spaces.Lop^[a] u) U := ih ha'
      have hsub : N - (a + 1) + 1 = N - a := by omega
      have hstep := LI_contDiffOn_Lop (m := N - (a + 1)) hU
        (f := Work.Spaces.Lop^[a] u) (by rw [hsub]; exact hih)
      rw [Function.iterate_succ_apply']
      exact hstep

lemma LI_diffAt_of_contDiffOn_one {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h : ContDiffOn ℝ (1 : ℕ∞ω) f U) {θ : ℝ} (hθ : θ ∈ U) :
    DifferentiableAt ℝ f θ :=
  (h.differentiableOn_one).differentiableAt (hU.mem_nhds hθ)

/-- Any iterate `Lop^[a] u` with `a < N` is differentiable at interior points of the open set
where `u` is `C^N`. -/
lemma LI_diffAt_lop_iter {N : ℕ} {u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ (N : ℕ∞ω) u U) (a : ℕ) (ha : a < N) {θ : ℝ} (hθ : θ ∈ U) :
    DifferentiableAt ℝ (Work.Spaces.Lop^[a] u) θ := by
  have h := LI_LI_contDiffOn_Lop_iter hU hu a (le_of_lt ha)
  have h1 : ContDiffOn ℝ (1 : ℕ∞ω) (Work.Spaces.Lop^[a] u) U :=
    h.of_le (by exact_mod_cast (by omega : 1 ≤ N - a))
  exact LI_diffAt_of_contDiffOn_one hU h1 hθ

/-! ## Congruence and linearity of the iterates -/

lemma LI_Lop_congr_eqOn {A B : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h : Set.EqOn A B U) : Set.EqOn (Work.Spaces.Lop A) (Work.Spaces.Lop B) U := by
  intro θ hθ
  show Real.sin (2 * θ) * deriv A θ = Real.sin (2 * θ) * deriv B θ
  rw [Set.EqOn.deriv h hU hθ]

lemma LI_Lop_iter_congr_eqOn {U : Set ℝ} (hU : IsOpen U) :
    ∀ (k : ℕ) {A B : ℝ → ℝ}, Set.EqOn A B U →
      Set.EqOn (Work.Spaces.Lop^[k] A) (Work.Spaces.Lop^[k] B) U := by
  intro k
  induction k with
  | zero => intro A B h; simpa [Function.iterate_zero_apply] using h
  | succ k ih =>
      intro A B h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact LI_Lop_congr_eqOn hU (ih h)

lemma LI_Lop_iter_neg_eqOn {U : Set ℝ} (hU : IsOpen U) :
    ∀ (k : ℕ) {A : ℝ → ℝ}, ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) A U →
      Set.EqOn (Work.Spaces.Lop^[k] (fun θ => -A θ))
        (fun θ => -(Work.Spaces.Lop^[k] A θ)) U := by
  intro k
  induction k with
  | zero =>
      intro A hA θ hθ
      show -A θ = -(A θ)
      rfl
  | succ k ih =>
      intro A hA
      show Set.EqOn (Work.Spaces.Lop^[k] (Work.Spaces.Lop (fun θ => -A θ)))
        (fun θ => -(Work.Spaces.Lop^[k] (Work.Spaces.Lop A) θ)) U
      have hbase : Set.EqOn (Work.Spaces.Lop (fun θ => -A θ))
          (fun θ => -(Work.Spaces.Lop A θ)) U := by
        intro θ hθ
        show Real.sin (2 * θ) * deriv (fun θ' : ℝ => -A θ') θ
          = -(Real.sin (2 * θ) * deriv A θ)
        have hd : DifferentiableAt ℝ A θ :=
          (((hA.of_le (by exact_mod_cast (by omega : 1 ≤ k + 1)))).differentiableOn_one).differentiableAt
            (hU.mem_nhds hθ)
        have hdn : HasDerivAt (fun θ' : ℝ => -A θ') (-(deriv A θ)) θ :=
          hd.hasDerivAt.neg
        rw [hdn.deriv]
        ring
      have hLopA : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (Work.Spaces.Lop A) U :=
        LI_contDiffOn_Lop (m := k) hU hA
      exact (LI_Lop_iter_congr_eqOn hU k hbase).trans (ih hLopA)

lemma LI_Lop_iter_add_eqOn {U : Set ℝ} (hU : IsOpen U) :
    ∀ (k : ℕ) {A B : ℝ → ℝ}, ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) A U →
      ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) B U →
      Set.EqOn (Work.Spaces.Lop^[k] (A + B))
        (fun θ => Work.Spaces.Lop^[k] A θ + Work.Spaces.Lop^[k] B θ) U := by
  intro k
  induction k with
  | zero =>
      intro A B hA hB θ hθ
      rfl
  | succ k ih =>
      intro A B hA hB
      show Set.EqOn (Work.Spaces.Lop^[k] (Work.Spaces.Lop (A + B)))
        (fun θ => Work.Spaces.Lop^[k] (Work.Spaces.Lop A) θ
          + Work.Spaces.Lop^[k] (Work.Spaces.Lop B) θ) U
      have hbase : Set.EqOn (Work.Spaces.Lop (A + B))
          (fun θ => Work.Spaces.Lop A θ + Work.Spaces.Lop B θ) U := by
        intro θ hθ
        show Real.sin (2 * θ) * deriv (A + B) θ
          = Real.sin (2 * θ) * deriv A θ + Real.sin (2 * θ) * deriv B θ
        have hdA : DifferentiableAt ℝ A θ :=
          (((hA.of_le (by exact_mod_cast (by omega : 1 ≤ k + 1)))).differentiableOn_one).differentiableAt
            (hU.mem_nhds hθ)
        have hdB : DifferentiableAt ℝ B θ :=
          (((hB.of_le (by exact_mod_cast (by omega : 1 ≤ k + 1)))).differentiableOn_one).differentiableAt
            (hU.mem_nhds hθ)
        have h := hdA.hasDerivAt.add hdB.hasDerivAt
        rw [h.deriv]
        ring
      have hLopA : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (Work.Spaces.Lop A) U :=
        LI_contDiffOn_Lop (m := k) hU hA
      have hLopB : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (Work.Spaces.Lop B) U :=
        LI_contDiffOn_Lop (m := k) hU hB
      exact (LI_Lop_iter_congr_eqOn hU k hbase).trans (ih hLopA hLopB)

/-! ## The iterated Leibniz rule at fixed order `9` -/

lemma LI_Lop_iter_mul_eqOn_9 {u v : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 9 u U) (hv : ContDiffOn ℝ 9 v U) :
    ∀ j : ℕ, j ≤ 8 → Set.EqOn (Work.Spaces.Lop^[j] (u * v))
      (fun θ : ℝ => ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
        (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a] v θ)) U := by
  intro j
  induction j with
  | zero =>
      intro _ θ _
      simp [Function.iterate_zero_apply, Finset.sum_range_one]
  | succ j ih =>
      intro hj θ hθ
      show Work.Spaces.Lop^[j + 1] (u * v) θ
        = ∑ a ∈ Finset.range (j + 1 + 1), ((j + 1).choose a : ℝ) *
            (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j + 1 - a] v θ)
      have hj' : j ≤ 8 := by omega
      rw [Function.iterate_succ_apply']
      have hih := ih hj'
      have hderiv : deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = deriv (fun θ' : ℝ => ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
              (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ :=
        hih.deriv hU hθ
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' : ℝ => (j.choose a : ℝ) *
            (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        intro a ha
        have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        exact (((LI_diffAt_lop_iter (N := 9) hU hu a (by omega) hθ).mul
          (LI_diffAt_lop_iter (N := 9) hU hv (j - a) (by omega) hθ)).const_mul _)
      have hfun : (fun θ' : ℝ => ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
            (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ'))
          = ∑ a ∈ Finset.range (j + 1), (fun θ' : ℝ => (j.choose a : ℝ) *
            (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hkey : Work.Spaces.Lop (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ) * deriv
              (fun θ' : ℝ => (j.choose a : ℝ) *
                (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] (u * v)) θ = _
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      have hstep : (∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ) * deriv
              (fun θ' : ℝ => (j.choose a : ℝ) *
                (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ)
          = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
              (Work.Spaces.Lop^[a + 1] u θ * Work.Spaces.Lop^[j - a] v θ
                + Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a + 1] v θ) := by
        apply Finset.sum_congr rfl
        intro a ha
        have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        exact Work.Spaces.sin_deriv_term u v θ j a
          (LI_diffAt_lop_iter (N := 9) hU hu a (by omega) hθ)
          (LI_diffAt_lop_iter (N := 9) hU hv (j - a) (by omega) hθ)
      rw [hstep]
      exact Work.Spaces.leibniz_step j (fun i => Work.Spaces.Lop^[i] u θ)
        (fun i => Work.Spaces.Lop^[i] v θ)


end Work.FTS.PhiStar.LinvFlat
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.PhiAjFlatDecay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-! ## 1. The derivative numerator of `z ↦ P(z)/(1+z)^n` -/

/-- The numerator of the derivative of `P(z)/(1+z)^n`: `P'(X)·(1+X) − n·P(X)`. -/
noncomputable def numStep (n : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.derivative P * (1 + Polynomial.X) - Polynomial.C (n : ℝ) * P

/-- The `k`-fold iterate of `numStep` (the numerator of the `k`-th derivative of
`P(z)/(1+z)^n`). -/
noncomputable def numIter (n : ℕ) (P : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => P
  | (k + 1) => numStep (n + k) (numIter n P k)

lemma numIter_zero (n : ℕ) (P : Polynomial ℝ) : numIter n P 0 = P := rfl

lemma numIter_succ (n : ℕ) (P : Polynomial ℝ) (k : ℕ) :
    numIter n P (k + 1) = numStep (n + k) (numIter n P k) := rfl

lemma numStep_eval (n : ℕ) (P : Polynomial ℝ) (z : ℝ) :
    (numStep n P).eval z = P.derivative.eval z * (1 + z) - (n : ℝ) * P.eval z := by
  simp only [numStep, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C]

lemma natDegree_one_add_X_le : (1 + Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
  have h1 : (1 : Polynomial ℝ).natDegree = 0 := Polynomial.natDegree_one
  have h2 : (Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := Polynomial.natDegree_X_le
  have h3 := Polynomial.natDegree_add_le (1 : Polynomial ℝ) Polynomial.X
  omega

lemma numStep_natDegree_le {n d : ℕ} (hd : 1 ≤ d) {P : Polynomial ℝ} (hP : P.natDegree ≤ d) :
    (numStep n P).natDegree ≤ d := by
  have hder : (Polynomial.derivative P).natDegree ≤ d - 1 :=
    (Polynomial.natDegree_derivative_le P).trans (by omega)
  have hmul : (Polynomial.derivative P * (1 + Polynomial.X)).natDegree ≤ d := by
    have h := Polynomial.natDegree_mul_le (p := Polynomial.derivative P)
      (q := 1 + Polynomial.X)
    have hX := natDegree_one_add_X_le
    omega
  have hC : (Polynomial.C (n : ℝ) * P).natDegree ≤ d :=
    (Polynomial.natDegree_C_mul_le _ _).trans hP
  rw [numStep]
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le hmul hC)

/-- `numStep` never increases the degree (also when the degree is `0`). -/
lemma numStep_natDegree_le_self (m : ℕ) (Q : Polynomial ℝ) :
    (numStep m Q).natDegree ≤ Q.natDegree := by
  rcases Nat.eq_zero_or_pos Q.natDegree with h0 | hpos
  · rw [numStep, Polynomial.derivative_of_natDegree_zero h0, zero_mul, zero_sub,
      Polynomial.natDegree_neg]
    exact Polynomial.natDegree_C_mul_le _ _
  · exact numStep_natDegree_le hpos le_rfl

lemma numIter_natDegree_le (n : ℕ) (P : Polynomial ℝ) (k : ℕ) :
    (numIter n P k).natDegree ≤ P.natDegree := by
  induction k with
  | zero => rw [numIter_zero]
  | succ k ih => rw [numIter_succ]; exact (numStep_natDegree_le_self _ _).trans ih

/-- `z ↦ (1+z)^p` has the expected derivative. -/
lemma hasDerivAt_one_add_pow (p : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => (1 + w) ^ p) ((p : ℝ) * (1 + z) ^ (p - 1)) z := by
  have hpoly : (fun w : ℝ => (1 + w) ^ p)
      = fun w : ℝ => ((1 + Polynomial.X : Polynomial ℝ) ^ p).eval w := by
    funext w
    simp [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
  rw [hpoly]
  have hder := Polynomial.hasDerivAt ((1 + Polynomial.X : Polynomial ℝ) ^ p) z
  convert hder using 1
  rw [Polynomial.derivative_pow]
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.derivative_add,
    Polynomial.derivative_one, Polynomial.derivative_X]

/-- **The derivative of a rational function with a single pole at `-1`.** -/
lemma deriv_rat (P : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n) {z : ℝ} (hz : z ≠ -1) :
    deriv (fun w : ℝ => P.eval w / (1 + w) ^ n) z
      = (numStep n P).eval z / (1 + z) ^ (n + 1) := by
  have ha : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  have h1 : HasDerivAt (fun w : ℝ => P.eval w) (P.derivative.eval z) z :=
    Polynomial.hasDerivAt P z
  have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ n) ((n : ℝ) * (1 + z) ^ (n - 1)) z :=
    hasDerivAt_one_add_pow n z
  have hdiv : HasDerivAt (fun w : ℝ => P.eval w / (1 + w) ^ n)
      ((P.derivative.eval z * (1 + z) ^ n - P.eval z * ((n : ℝ) * (1 + z) ^ (n - 1)))
        / ((1 + z) ^ n) ^ 2) z := h1.div h2 (pow_ne_zero n ha)
  rw [hdiv.deriv, numStep_eval]
  rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero n ha)) (pow_ne_zero (n + 1) ha)]
  have e1 : (1 + z) ^ n * (1 + z) ^ (n + 1) = (1 + z) ^ (2 * n + 1) := by
    rw [← pow_add]; congr 1; omega
  have e2 : (1 + z) ^ (n - 1) * (1 + z) ^ (n + 1) = (1 + z) ^ (2 * n) := by
    rw [← pow_add]; congr 1; omega
  have e3 : (1 + z) * (1 + z) ^ (2 * n) = (1 + z) ^ (2 * n + 1) :=
    (pow_succ' (1 + z) (2 * n)).symm
  have e4 : ((1 + z) ^ n) ^ 2 = (1 + z) ^ (2 * n) := by
    rw [← pow_mul]; congr 1; ring
  calc (P.derivative.eval z * (1 + z) ^ n - P.eval z * ((n : ℝ) * (1 + z) ^ (n - 1)))
        * (1 + z) ^ (n + 1)
      = P.derivative.eval z * ((1 + z) ^ n * (1 + z) ^ (n + 1))
        - (n : ℝ) * P.eval z * ((1 + z) ^ (n - 1) * (1 + z) ^ (n + 1)) := by ring
    _ = P.derivative.eval z * (1 + z) ^ (2 * n + 1)
        - (n : ℝ) * P.eval z * (1 + z) ^ (2 * n) := by rw [e1, e2]
    _ = (P.derivative.eval z * (1 + z) - (n : ℝ) * P.eval z) * ((1 + z) ^ n) ^ 2 := by
        rw [e4, sub_mul, mul_assoc, mul_assoc, e3]

/-- `iteratedDeriv 2 f = deriv (deriv f)`. -/
lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_zero]

/-- **The iterated derivative of a rational function with a single pole at `-1`.** -/
lemma iteratedDeriv_rat (P : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    Set.EqOn (iteratedDeriv k (fun w : ℝ => P.eval w / (1 + w) ^ n))
      (fun w : ℝ => (numIter n P k).eval w / (1 + w) ^ (n + k)) (Set.Ioi (-1)) := by
  induction k with
  | zero =>
      intro z _
      simp [numIter]
  | succ k ih =>
      intro z hz
      have hz' : (-1 : ℝ) < z := hz
      have hzne : z ≠ -1 := ne_of_gt hz'
      have hev : iteratedDeriv k (fun w : ℝ => P.eval w / (1 + w) ^ n)
          =ᶠ[𝓝 z] fun w : ℝ => (numIter n P k).eval w / (1 + w) ^ (n + k) :=
        ih.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz)
      rw [iteratedDeriv_succ, hev.deriv_eq,
        deriv_rat (numIter n P k) (n + k) (by omega) hzne, numIter_succ]
      rw [Nat.add_assoc]

/-! ## 2. The polynomial bound and the master decay estimate -/

/-- On the nonnegative half-line a polynomial of degree `≤ d` is bounded by the sum of the
absolute values of its coefficients times `(1+t)^d`. -/
lemma poly_eval_bound (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d) {t : ℝ}
    (ht : 0 ≤ t) :
    |P.eval t| ≤ (∑ i ∈ Finset.range (d + 1), |P.coeff i|) * (1 + t) ^ d := by
  rw [Polynomial.eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i * t ^ i|
      = ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * t ^ i := by
        refine Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_pow, abs_of_nonneg ht]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * (1 + t) ^ d := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ P.natDegree := by
          have := Finset.mem_range.mp hi
          omega
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc t ^ i ≤ (1 + t) ^ i := pow_le_pow_left₀ ht (by linarith) i
          _ ≤ (1 + t) ^ d := pow_le_pow_right₀ (by linarith) (by omega)
    _ = (∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|) * (1 + t) ^ d := by
        rw [Finset.sum_mul]
    _ ≤ (∑ i ∈ Finset.range (d + 1), |P.coeff i|) * (1 + t) ^ d := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro i hi
          simp only [Finset.mem_range] at hi ⊢
          omega
        · intro i _ _; exact abs_nonneg _

/-- **The master estimate.**  For a polynomial `P` with `natDegree P ≤ d` and `1 ≤ s`, every
`k`-th derivative of `z ↦ P(z)/(1+z)^{d+s}` decays at least like `(1+t)^{-(s+k)}` on
`(0,∞)`, with the completely explicit constant given by the coefficients of the numerator
polynomial `numIter (d+s) P k`. -/
theorem rat_iteratedDeriv_bound (P : Polynomial ℝ) (d s k : ℕ) (hs : 1 ≤ s)
    (hPd : P.natDegree ≤ d) :
    ∀ t : ℝ, 0 < t →
      |iteratedDeriv k (fun z : ℝ => P.eval z / (1 + z) ^ (d + s)) t|
        ≤ (∑ i ∈ Finset.range (d + 1), |(numIter (d + s) P k).coeff i|)
            / (1 + t) ^ (s + k) := by
  intro t ht
  have hds : 1 ≤ d + s := by omega
  have ht1 : (-1 : ℝ) < t := by linarith
  have hiter : iteratedDeriv k (fun z : ℝ => P.eval z / (1 + z) ^ (d + s)) t
      = (numIter (d + s) P k).eval t / (1 + t) ^ (d + s + k) :=
    iteratedDeriv_rat P (d + s) hds k ht1
  have hdeg : (numIter (d + s) P k).natDegree ≤ d :=
    (numIter_natDegree_le (d + s) P k).trans hPd
  have hpb := poly_eval_bound (numIter (d + s) P k) hdeg ht.le
  have hden : (0 : ℝ) < (1 + t) ^ (d + s + k) := pow_pos (by linarith) _
  have habs : |(1 + t) ^ (d + s + k)| = (1 + t) ^ (d + s + k) := abs_of_pos hden
  rw [hiter, abs_div, habs]
  refine (div_le_div_of_nonneg_right hpb hden.le).trans ?_
  have heq : (∑ i ∈ Finset.range (d + 1), |(numIter (d + s) P k).coeff i|) * (1 + t) ^ d
        / (1 + t) ^ (d + s + k)
      = (∑ i ∈ Finset.range (d + 1), |(numIter (d + s) P k).coeff i|)
        / (1 + t) ^ (s + k) := by
    rw [show d + s + k = d + (s + k) from by omega, pow_add]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [heq]

/-- Equality on an open set passes to iterated derivatives. -/
lemma iteratedDeriv_congr_of_eqOn_isOpen {s : Set ℝ} (hs : IsOpen s) {f g : ℝ → ℝ}
    (h : Set.EqOn f g s) (k : ℕ) : Set.EqOn (iteratedDeriv k f) (iteratedDeriv k g) s := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      intro x hx
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact EventuallyEq.deriv_eq (ih.eventuallyEq_of_mem (hs.mem_nhds hx))

/-! ## 3. The numerator polynomial of `phiAj j α` -/

/-- `phiAjNum α j` is the numerator of `phiAj j α` over the common denominator
`(1+z)^(2j+2)`:  `phiAj j α z = (phiAjNum α j).eval z / (1+z)^(2j+2)`. -/
noncomputable def phiAjNum (α : ℝ) : ℕ → Polynomial ℝ
  | 0 => Polynomial.C 2 * Polynomial.X
  | (j + 1) =>
      Polynomial.C α * Polynomial.X ^ 2
          * numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j))
        + Polynomial.C (5 + α) * Polynomial.X * (1 + Polynomial.X)
          * numStep (2 * j + 2) (phiAjNum α j)

lemma phiAjNum_natDegree_le (α : ℝ) (j : ℕ) : (phiAjNum α j).natDegree ≤ 2 * j + 1 := by
  induction j with
  | zero =>
      have h := Polynomial.natDegree_C_mul_le (2 : ℝ) (Polynomial.X : Polynomial ℝ)
      have hX := Polynomial.natDegree_X_le (R := ℝ)
      simp only [phiAjNum]
      omega
  | succ j ih =>
      have hQ1 : (numStep (2 * j + 2) (phiAjNum α j)).natDegree ≤ 2 * j + 1 :=
        numStep_natDegree_le (by omega) ih
      have hQ2 : (numStep (2 * j + 3)
          (numStep (2 * j + 2) (phiAjNum α j))).natDegree ≤ 2 * j + 1 :=
        numStep_natDegree_le (by omega) hQ1
      have hX2 : (Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
        have h := Polynomial.natDegree_pow_le (p := (Polynomial.X : Polynomial ℝ)) (n := 2)
        have hX := Polynomial.natDegree_X_le (R := ℝ)
        omega
      have h1X := natDegree_one_add_X_le
      rw [phiAjNum]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · have hc : (Polynomial.C α * Polynomial.X ^ 2).natDegree ≤ 2 :=
          (Polynomial.natDegree_C_mul_le _ _).trans hX2
        have h := Polynomial.natDegree_mul_le (p := Polynomial.C α * Polynomial.X ^ 2)
          (q := numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j)))
        omega
      · have hc : (Polynomial.C (5 + α) * Polynomial.X
            * (1 + Polynomial.X)).natDegree ≤ 2 := by
          refine (Polynomial.natDegree_mul_le.trans ?_)
          have hcx : (Polynomial.C (5 + α) * Polynomial.X).natDegree ≤ 1 :=
            (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
          omega
        have h := Polynomial.natDegree_mul_le
          (p := Polynomial.C (5 + α) * Polynomial.X * (1 + Polynomial.X))
          (q := numStep (2 * j + 2) (phiAjNum α j))
        omega

lemma phiAjNum_dvd_X (α : ℝ) (j : ℕ) : Polynomial.X ∣ phiAjNum α j := by
  induction j with
  | zero => exact ⟨Polynomial.C 2, by rw [phiAjNum]; ring⟩
  | succ j _ =>
      refine ⟨Polynomial.C α * Polynomial.X
          * numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j))
        + Polynomial.C (5 + α) * (1 + Polynomial.X)
          * numStep (2 * j + 2) (phiAjNum α j), ?_⟩
      rw [phiAjNum]
      ring

lemma phiAjNum_coeff_zero (α : ℝ) (j : ℕ) : (phiAjNum α j).coeff 0 = 0 :=
  Polynomial.X_dvd_iff.mp (phiAjNum_dvd_X α j)

/-- The elementary algebra of one `𝒜`-step on the rational representation. -/
lemma rat_step_algebra (α z a₁ a₂ : ℝ) (e : ℕ) (ha : (1 : ℝ) + z ≠ 0) :
    α * z ^ 2 * (a₂ / (1 + z) ^ (e + 2)) + (5 + α) * z * (a₁ / (1 + z) ^ (e + 1))
      = (α * z ^ 2 * a₂ + (5 + α) * z * (1 + z) * a₁) / (1 + z) ^ (e + 2) := by
  have h0 : α * z ^ 2 * (a₂ / (1 + z) ^ (e + 2)) = α * z ^ 2 * a₂ / (1 + z) ^ (e + 2) :=
    (mul_div_assoc _ _ _).symm
  have h1 : (5 + α) * z * (a₁ / (1 + z) ^ (e + 1))
      = ((5 + α) * z * a₁ * (1 + z)) / (1 + z) ^ (e + 2) := by
    rw [← mul_div_assoc]
    rw [div_eq_div_iff (pow_ne_zero (e + 1) ha) (pow_ne_zero (e + 2) ha)]
    have hA : (1 + z) ^ (e + 2) = (1 + z) ^ (e + 1) * (1 + z) := by
      rw [show e + 2 = (e + 1) + 1 from by omega, pow_succ]
    have hB : (1 + z) ^ (e + 1) = (1 + z) ^ e * (1 + z) := pow_succ _ _
    rw [hA, hB]
    ring
  rw [h0, h1, ← add_div]
  ring

/-- **The rational representation of `phiAj j α`.** -/
theorem phiAj_eqOn_num (α : ℝ) (j : ℕ) :
    Set.EqOn (phiAj j α)
      (fun z : ℝ => (phiAjNum α j).eval z / (1 + z) ^ (2 * j + 2)) (Set.Ioi (-1)) := by
  induction j with
  | zero =>
      intro z _
      show Work.FTS.VocabO.phiR z = (phiAjNum α 0).eval z / (1 + z) ^ (2 * 0 + 2)
      rw [Work.FTS.VocabO.phiR]
      simp only [phiAjNum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  | succ j ih =>
      intro z hz
      have hz' : (-1 : ℝ) < z := hz
      have hzne : z ≠ -1 := ne_of_gt hz'
      have ha : (1 : ℝ) + z ≠ 0 := by intro h; exact hzne (by linarith)
      show phiAj (j + 1) α z
        = (phiAjNum α (j + 1)).eval z / (1 + z) ^ (2 * (j + 1) + 2)
      have hder1 : deriv (phiAj j α) z
          = (numStep (2 * j + 2) (phiAjNum α j)).eval z / (1 + z) ^ (2 * j + 3) := by
        rw [(ih.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz)).deriv_eq]
        have h := deriv_rat (phiAjNum α j) (2 * j + 2) (by omega) hzne
        rw [show (2 * j + 2 + 1 : ℕ) = 2 * j + 3 from by omega] at h
        exact h
      have hder2 : iteratedDeriv 2 (phiAj j α) z
          = (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j))).eval z
              / (1 + z) ^ (2 * j + 4) := by
        have hev' : deriv (phiAj j α) =ᶠ[𝓝 z]
            (fun w : ℝ => (numStep (2 * j + 2) (phiAjNum α j)).eval w
              / (1 + w) ^ (2 * j + 3)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
          have hy' : (-1 : ℝ) < y := hy
          rw [(ih.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy)).deriv_eq]
          have h := deriv_rat (phiAjNum α j) (2 * j + 2) (by omega) (ne_of_gt hy')
          rw [show (2 * j + 2 + 1 : ℕ) = 2 * j + 3 from by omega] at h
          exact h
        rw [iteratedDeriv_two_eq, hev'.deriv_eq]
        have h := deriv_rat (numStep (2 * j + 2) (phiAjNum α j)) (2 * j + 3) (by omega) hzne
        rw [show (2 * j + 3 + 1 : ℕ) = 2 * j + 4 from by omega] at h
        exact h
      have hphi : phiAj (j + 1) α z
          = α * z ^ 2 * iteratedDeriv 2 (phiAj j α) z
            + (5 + α) * z * deriv (phiAj j α) z := rfl
      have hnum : (phiAjNum α (j + 1)).eval z
          = α * z ^ 2 * (numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j))).eval z
            + (5 + α) * z * (1 + z)
              * (numStep (2 * j + 2) (phiAjNum α j)).eval z := by
        simp only [phiAjNum, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
      rw [hphi, hder1, hder2, hnum]
      rw [show (2 * j + 4 : ℕ) = (2 * j + 2) + 2 from by omega,
        show (2 * j + 3 : ℕ) = (2 * j + 2) + 1 from by omega,
        show (2 * (j + 1) + 2 : ℕ) = (2 * j + 2) + 2 from by omega]
      exact rat_step_algebra α z ((numStep (2 * j + 2) (phiAjNum α j)).eval z)
        ((numStep (2 * j + 3) (numStep (2 * j + 2) (phiAjNum α j))).eval z) (2 * j + 2) ha

/-! ## 4. The divided function `phiAj j α / z` -/

/-- The numerator of `phiAj j α / z` over the denominator `(1+z)^(2j+2)`:
`(phiAjNum α j).divX`. -/
noncomputable def phiAjNumDiv (α : ℝ) (j : ℕ) : Polynomial ℝ := (phiAjNum α j).divX

lemma phiAjNumDiv_natDegree_le (α : ℝ) (j : ℕ) : (phiAjNumDiv α j).natDegree ≤ 2 * j := by
  rw [phiAjNumDiv, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  have h := phiAjNum_natDegree_le α j
  omega

/-- `(phiAjNum α j).eval z = z · (phiAjNumDiv α j).eval z`. -/
lemma phiAjNum_eval_divX (α : ℝ) (j : ℕ) (z : ℝ) :
    (phiAjNum α j).eval z = z * (phiAjNumDiv α j).eval z := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval z)
    (Polynomial.divX_mul_X_add (phiAjNum α j))
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    at h
  rw [phiAjNum_coeff_zero α j, add_zero, mul_comm] at h
  exact h.symm

/-- **The rational representation of `phiAj j α / z`.** -/
theorem phiAj_div_eqOn_num (α : ℝ) (j : ℕ) :
    Set.EqOn (fun z : ℝ => phiAj j α z / z)
      (fun z : ℝ => (phiAjNumDiv α j).eval z / (1 + z) ^ (2 * j + 2)) (Set.Ioi 0) := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  have hz0 : z ≠ 0 := ne_of_gt hzpos
  have hz1 : (-1 : ℝ) < z := by linarith
  show phiAj j α z / z = (phiAjNumDiv α j).eval z / (1 + z) ^ (2 * j + 2)
  rw [phiAj_eqOn_num α j hz1]
  dsimp only
  have ha : (1 + z) ^ (2 * j + 2) ≠ 0 := pow_ne_zero _ (by linarith)
  rw [phiAjNum_eval_divX α j z]
  field_simp

/-! ## 5. Auxiliary inequalities for the assembly -/

lemma div_pow_le_shift (C t : ℝ) (m : ℕ) (hC : 0 ≤ C) (ht : 0 < t) :
    C / (1 + t) ^ m ≤ (2 * C) / (1 + t ^ m) := by
  have h2 : (0 : ℝ) < (1 + t) ^ m := pow_pos (by linarith) m
  have h3 : 1 + t ^ m ≤ 2 * (1 + t) ^ m := by
    have a : t ^ m ≤ (1 + t) ^ m := pow_le_pow_left₀ (le_of_lt ht) (by linarith) m
    have b : (1 : ℝ) ≤ (1 + t) ^ m := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ 1 + t) m
    linarith
  have hgoal : C * (1 + t ^ m) ≤ 2 * C * (1 + t) ^ m := by nlinarith [h3, hC]
  have htnn : (0 : ℝ) ≤ 1 + t ^ m := by positivity
  have hleft : C / (1 + t) ^ m = C * (1 + t ^ m) / ((1 + t ^ m) * (1 + t) ^ m) := by
    rw [div_eq_div_iff (ne_of_gt h2) (by positivity)]
    ring
  have hright : (2 * C) / (1 + t ^ m) = 2 * C * (1 + t) ^ m / ((1 + t ^ m) * (1 + t) ^ m) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hleft, hright]
  exact div_le_div_of_nonneg_right hgoal (by positivity)

lemma bound_of_le {X C A t : ℝ} (m : ℕ) (hC : 0 ≤ C) (hA : 2 * C ≤ A) (ht : 0 < t)
    (hX : X ≤ C / (1 + t) ^ m) : X ≤ A / (1 + t ^ m) :=
  hX.trans ((div_pow_le_shift C t m hC ht).trans
    (div_le_div_of_nonneg_right hA (by positivity)))

/-- The constant of the `k`-th derivative bound for the `j`-th `𝒜`-iterate. -/
noncomputable def slotC1 (α : ℝ) (j k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * j + 2), |(numIter (2 * j + 2) (phiAjNum α j) k).coeff i|

/-- The constant of the `k`-th derivative bound for the divided `j`-th `𝒜`-iterate. -/
noncomputable def slotC2 (α : ℝ) (j k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * j + 1), |(numIter (2 * j + 2) (phiAjNumDiv α j) k).coeff i|

lemma slotC1_nonneg (α : ℝ) (j k : ℕ) : 0 ≤ slotC1 α j k := by
  rw [slotC1]; exact Finset.sum_nonneg fun i _ => abs_nonneg _

lemma slotC2_nonneg (α : ℝ) (j k : ℕ) : 0 ≤ slotC2 α j k := by
  rw [slotC2]; exact Finset.sum_nonneg fun i _ => abs_nonneg _




/-! ## 6. The target -/


end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi23Smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

/-!
# Smoothness of the two telescoping iterates `ψ₂`, `ψ₃`

`ψ₂ = sin 2θ · LinvI ψ` and `ψ₃ = sin 2θ · LinvI ψ₂`, where

`Linv h θ = −(sin²θ cos³θ)⁻¹ · ∫₀^θ sin²t cos³t h t / sin 2t dt`,  `LinvI h θ = ∫₀^θ Linv h`.

The point of this file is that `LinvI h` is `C²` on `(0, b)` as soon as `h` is continuous and
bounded on `(0, b)`: the integrand of `LinvI` is `−(sin²θcos³θ)⁻¹ ∫₀^θ (sin t cos²t /2) h t dt`,
a quotient of a `C¹` primitive by a smooth non-vanishing weight.  No moment condition and no
endpoint behaviour of `h` is used: everything is local on a sub-interval `(0, b)`,
`b < π/2`, so the iterate can be fed back into itself.
-/



















end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Consumer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Metric
open scoped Topology

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false
theorem gCompHolderQuant' {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : ℝ → ℝ → ℝ}
    {Cv Lg Lθ K : ℝ} (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg) (hLθ : 0 ≤ Lθ) (hK : 0 ≤ K)
    (hvt : Work.Spaces.VanishTheta g)
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ Lg * |z - z'| ^ α)
    (hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ α)
    (hKquad : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ K * z ^ 2)
    (hKz : ∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ K * max z z' * |z - z'|)
    (hKth : ∀ z θ θ' : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ K * z ^ 2 * |θ - θ'| ^ α) :
    HolderWith (gCompConstNN' α Cv Lg Lθ K) (⟨α, hα.le⟩ : NNReal)
      (fun x : Work.FTS.Regularity.R3 =>
        g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)) := by
  have h3α : 0 < 3 * α := by linarith
  have h3α1 : 3 * α ≤ 1 := by linarith
  have hvan' : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ := hvan
  have hK0 : 0 ≤ K := hK
  have hslicez : ∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
        |g z θ - g z' θ| ≤ K * max z z' * |z - z'| := hKz
  -- the two global bounds of the composite
  have hsup : ∀ z : R3, |g (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)| ≤ Cv := by
    intro z
    have hθ := Work.ConstructionInstance.psi_mem_Iθ z
    have h1 := hvan' (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)
      (Real.rpow_nonneg (Work.Cyl.rho_nonneg z) _) hθ
    have h2 : Work.ConstructionInstance.Gamma α (Work.ConstructionInstance.psi z) ≤ 1 := Work.ConstructionInstance.Gamma_le_one hα.le hθ
    have h3 : 0 ≤ Work.ConstructionInstance.Gamma α (Work.ConstructionInstance.psi z) := Work.ConstructionInstance.Gamma_nonneg hθ
    nlinarith [hCv]
  have hquadbound : ∀ z : R3, Work.Cyl.rho z ≤ 2 →
      |g (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)| ≤ K * (Work.Cyl.rho z) ^ (6 * α) := by
    intro z hz
    have hρ0 := Work.Cyl.rho_nonneg z
    have hZ0 : 0 ≤ Work.Cyl.rho z ^ (3 * α) := Real.rpow_nonneg hρ0 _
    have hZ2 : Work.Cyl.rho z ^ (3 * α) ≤ 2 := by
      calc Work.Cyl.rho z ^ (3 * α) ≤ 2 ^ (3 * α) := Real.rpow_le_rpow hρ0 hz h3α.le
        _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
        _ = 2 := Real.rpow_one 2
    have h1 := hKquad _ _ hZ0 hZ2 (Work.ConstructionInstance.psi_mem_Iθ z)
    have h2 : (Work.Cyl.rho z ^ (3 * α)) ^ 2 = (Work.Cyl.rho z) ^ (6 * α) := by
      rw [← Real.rpow_natCast (Work.Cyl.rho z ^ (3 * α)) 2, ← Real.rpow_mul hρ0]
      congr 1
      ring
    calc |g (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)|
        ≤ K * (Work.Cyl.rho z ^ (3 * α)) ^ 2 := h1
      _ = K * (Work.Cyl.rho z) ^ (6 * α) := by rw [h2]
  -- the Hölder constant
  set C : ℝ := 2 * Cv + (2 * Cv * (3/2) ^ α
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α)))) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hC1 : 2 * Cv ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv * (3/2) ^ α
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α))) by positivity]
  have hC2 : 2 * Cv * (3/2) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α))) by positivity]
  have hC3 : 2 * K * 3 ^ (6 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv
      + (2 * Cv * (3/2) ^ α + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α))) by positivity]
  have hC4 : Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α))) by positivity]
  have hC5 : K * (3/2) * 3 ^ α * (3/2) ^ (2 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α))) by positivity]
  have hC6 : K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)))) by positivity]
  have hC56 : K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α
      + K * (3/2) * 3 ^ α * (3/2) ^ (2 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + (Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α))) by positivity]
  have hCco : C = gCompConst' α Cv Lg Lθ K := by
    simp only [gCompConst']
    rw [hCdef]
  have hCg : 0 ≤ gCompConst' α Cv Lg Lθ K := hCco ▸ hCnn
  have hCnne : gCompConstNN' α Cv Lg Lθ K = (⟨C, hCnn⟩ : NNReal) := by
    apply Subtype.ext
    simp only [gCompConstNN']
    rw [abs_of_nonneg hCg]
    exact hCco.symm
  rw [hCnne]
  refine Work.Stability.holderWith_of_dist_le (fun x y => ?_)
  rw [Real.dist_eq, Work.ConstructionInstance.g_psi_eq hquad0 hvt x, Work.ConstructionInstance.g_psi_eq hquad0 hvt y]
  show |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
      ≤ C * dist x y ^ α
  by_cases hxy : x = y
  · subst hxy
    simp only [dist_self, sub_self, abs_zero]
    positivity
  have hdpos : 0 < dist x y := dist_pos.mpr hxy
  have hdnn : 0 ≤ dist x y := dist_nonneg
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := Work.ConstructionInstance.abs_sub_le_abs_add
  rcases le_or_gt 1 (dist x y) with hd1 | hd1
  · -- far away (or exactly at distance one): the sup bound suffices
    have h1 : (1 : ℝ) ≤ dist x y ^ α := Real.one_le_rpow hd1 hα.le
    calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
        ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)|
          + |g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := htri _ _
      _ ≤ 2 * Cv := by linarith [hsup x, hsup y]
      _ ≤ C * dist x y ^ α := by
          calc 2 * Cv ≤ C := hC1
            _ = C * 1 := by ring
            _ ≤ C * dist x y ^ α := by
                simpa using mul_le_mul_of_nonneg_left h1 hCnn
  · rcases le_or_gt (min (Work.Cyl.rho x) (Work.Cyl.rho y)) (2 * dist x y) with hfar | hnear
    · -- the radii are not large compared with `d`: use the two pointwise bounds
      have hmax3 : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 3 * dist x y := by
        have := Work.ConstructionInstance.max_rho_le_min_rho_add_dist x y
        linarith
      by_cases hsmall : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 2
      · -- both radii at most two: the quadratic vanishing of `g` at `z = 0`
        have hρx2 : Work.Cyl.rho x ≤ 2 := le_trans (le_max_left _ _) hsmall
        have hρy2 : Work.Cyl.rho y ≤ 2 := le_trans (le_max_right _ _) hsmall
        have hρx3 : Work.Cyl.rho x ≤ 3 * dist x y := le_trans (le_max_left _ _) hmax3
        have hρy3 : Work.Cyl.rho y ≤ 3 * dist x y := le_trans (le_max_right _ _) hmax3
        have hpow : dist x y ^ (6 * α) ≤ dist x y ^ α :=
          Real.rpow_le_rpow_of_exponent_ge hdpos (le_of_lt hd1) (by linarith)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)|
              + |g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := htri _ _
          _ ≤ K * (Work.Cyl.rho x) ^ (6 * α) + K * (Work.Cyl.rho y) ^ (6 * α) :=
              add_le_add (hquadbound x hρx2) (hquadbound y hρy2)
          _ ≤ K * (3 * dist x y) ^ (6 * α) + K * (3 * dist x y) ^ (6 * α) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) hρx3 (by linarith)) hK0
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) hρy3 (by linarith)) hK0
          _ = 2 * K * 3 ^ (6 * α) * dist x y ^ (6 * α) := by
              rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hdnn]; ring
          _ ≤ 2 * K * 3 ^ (6 * α) * dist x y ^ α :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC3 (Real.rpow_nonneg hdnn α)
      · -- both radii large: then `d > 2/3` and the sup bound suffices
        have hd23 : 2 / 3 ≤ dist x y := by
          have := Work.ConstructionInstance.max_rho_le_min_rho_add_dist x y
          linarith [not_le.mp hsmall, hfar]
        have h1 : (1 : ℝ) ≤ (3 / 2) ^ α * dist x y ^ α := by
          have h2 : (3 / 2 : ℝ) ^ α * (2 / 3) ^ α = 1 := by
            rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3 / 2) (by norm_num : (0:ℝ) ≤ 2 / 3),
              show (3:ℝ)/2 * (2/3) = 1 by ring, Real.one_rpow]
          have h3 : (2 / 3 : ℝ) ^ α ≤ dist x y ^ α :=
            Real.rpow_le_rpow (by norm_num) hd23 hα.le
          have h4 : 0 ≤ (3 / 2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
          calc (1 : ℝ) = (3 / 2 : ℝ) ^ α * (2 / 3) ^ α := h2.symm
            _ ≤ (3 / 2 : ℝ) ^ α * dist x y ^ α := mul_le_mul_of_nonneg_left h3 h4
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)|
              + |g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := htri _ _
          _ ≤ 2 * Cv := by linarith [hsup x, hsup y]
          _ = 2 * Cv * 1 := by ring
          _ ≤ 2 * Cv * ((3 / 2) ^ α * dist x y ^ α) :=
              mul_le_mul_of_nonneg_left h1 (by linarith)
          _ = 2 * Cv * (3 / 2) ^ α * dist x y ^ α := by ring
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hdnn α)
    · -- close together and away from the origin
      have hρmin2d : 2 * dist x y < min (Work.Cyl.rho x) (Work.Cyl.rho y) := hnear
      have hρminpos : 0 < min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
        lt_of_lt_of_le (by linarith [dist_nonneg (x := x) (y := y)]) (le_of_lt hρmin2d)
      have hminx : min (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ Work.Cyl.rho x := min_le_left _ _
      have hminy : min (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ Work.Cyl.rho y := min_le_right _ _
      have hρxmax : Work.Cyl.rho x ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_left _ _
      have hρymax : Work.Cyl.rho y ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_right _ _
      have hmax32 : max (Work.Cyl.rho x) (Work.Cyl.rho y)
          ≤ 3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2 := by
        have := Work.ConstructionInstance.max_rho_le_min_rho_add_dist x y
        linarith
      have hpsi : |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y|
          ≤ 4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
        Work.ConstructionInstance.psi_sub_le x y hρminpos hminx hminy
      have hpsi_nn : 0 ≤ |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| := abs_nonneg _
      have hZx0 : 0 ≤ Work.Cyl.rho x ^ (3 * α) := Real.rpow_nonneg (Work.Cyl.rho_nonneg x) _
      have hZy0 : 0 ≤ Work.Cyl.rho y ^ (3 * α) := Real.rpow_nonneg (Work.Cyl.rho_nonneg y) _
      have hsplit : |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)
            - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
          ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            + |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
                - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := by
        have := abs_add_le
          (g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y))
          (g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y))
        rwa [show g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)
              - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
            + (g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y))
            = g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)
              - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y) from by ring] at this
      by_cases hB1 : 1 ≤ min (Work.Cyl.rho x) (Work.Cyl.rho y)
      · -- both points at radius at least one: `hzk`/`hzth` and the Lipschitz bound for `Work.ConstructionInstance.psi`
        have hρx1 : 1 ≤ Work.Cyl.rho x := le_trans hB1 hminx
        have hρy1 : 1 ≤ Work.Cyl.rho y := le_trans hB1 hminy
        have hZd : |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| ≤ 3 * α * dist x y := by
          calc |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
              ≤ 3 * α * |Work.Cyl.rho x - Work.Cyl.rho y| :=
                Work.ConstructionInstance.abs_rpow_sub_le_mul_of_one_le h3α h3α1 hρx1 hρy1
            _ ≤ 3 * α * dist x y :=
                mul_le_mul_of_nonneg_left (Work.ConstructionInstance.abs_rho_sub_rho_le_dist x y) h3α.le
        have hdψ : |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ≤ 4 * Real.pi * dist x y := by
          rw [le_div_iff₀ hρminpos] at hpsi
          have h1 : |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y|
              ≤ |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| * min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
            le_mul_of_one_le_right (abs_nonneg _) hB1
          linarith
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)|
              + |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
                  - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := hsplit
          _ ≤ Lθ * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α + Lg * |Work.Cyl.rho x ^ (3 * α)
                - Work.Cyl.rho y ^ (3 * α)| ^ α :=
              add_le_add (hzth _ _ _ hZx0 (Work.ConstructionInstance.psi_mem_Iθ x) (Work.ConstructionInstance.psi_mem_Iθ y))
                (hzk _ _ _ hZx0 hZy0 (Work.ConstructionInstance.psi_mem_Iθ y))
          _ ≤ Lθ * (4 * Real.pi * dist x y) ^ α + Lg * (3 * α * dist x y) ^ α := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow hpsi_nn hdψ hα.le) hLθ
              · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hZd hα.le) hLg
          _ = (Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α) * dist x y ^ α := by
              rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4 * Real.pi) hdnn,
                Real.mul_rpow (by linarith : (0:ℝ) ≤ 3 * α) hdnn]
              ring
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC4 (Real.rpow_nonneg hdnn α)
      · -- both points at radius below one: the slice bounds of the Taylor expansion
        have hρmin1 : min (Work.Cyl.rho x) (Work.Cyl.rho y) < 1 := lt_of_not_ge hB1
        have hmax2 : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 2 := by linarith
        have hρx32 : Work.Cyl.rho x ≤ 3 / 2 := by
          have := le_trans hρxmax hmax32
          linarith
        have hρy32 : Work.Cyl.rho y ≤ 3 / 2 := by
          have := le_trans hρymax hmax32
          linarith
        have hZx2 : Work.Cyl.rho x ^ (3 * α) ≤ 2 := by
          calc Work.Cyl.rho x ^ (3 * α) ≤ (2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax2) h3α.le
            _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 2 := Real.rpow_one 2
        have hZy2 : Work.Cyl.rho y ^ (3 * α) ≤ 2 := by
          calc Work.Cyl.rho y ^ (3 * α) ≤ (2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) (le_trans hρymax hmax2) h3α.le
            _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 2 := Real.rpow_one 2
        have hZx32 : Work.Cyl.rho x ^ (3 * α) ≤ 3 / 2 := by
          calc Work.Cyl.rho x ^ (3 * α) ≤ (3 / 2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) hρx32 h3α.le
            _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 3 / 2 := Real.rpow_one (3 / 2)
        have hZy32 : Work.Cyl.rho y ^ (3 * α) ≤ 3 / 2 := by
          calc Work.Cyl.rho y ^ (3 * α) ≤ (3 / 2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) hρy32 h3α.le
            _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 3 / 2 := Real.rpow_one (3 / 2)
        have hmaxZ : max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α)) ≤ 3 / 2 :=
          max_le hZx32 hZy32
        have hZxle : Work.Cyl.rho x ^ (3 * α)
            ≤ (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α) :=
          Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax32) h3α.le
        have hZd : |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
            ≤ 3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α :=
          Work.ConstructionInstance.A0_rho_pow_diff (β := α) hα (le_trans hα13 (by norm_num)) (Work.Cyl.rho_nonneg x)
            (Work.Cyl.rho_nonneg y) hρx32 hρy32 (Work.ConstructionInstance.abs_rho_sub_rho_le_dist x y)
        have hzslice := hslicez (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)
          hZx0 hZx2 hZy0 hZy2 (Work.ConstructionInstance.psi_mem_Iθ y)
        have hθslice : |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)
              - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ K * (Work.Cyl.rho x ^ (3 * α)) ^ 2
              * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α :=
          hKth _ _ _ hZx0 hZx2 (Work.ConstructionInstance.psi_mem_Iθ x)
            (Work.ConstructionInstance.psi_mem_Iθ y)
        -- the corrected first gradient step: `z²` instead of `z`, and the α-power on `|Δψ|`
        have hsqu : (Work.Cyl.rho x ^ (3 * α)) ^ 2 = (Work.Cyl.rho x) ^ (6 * α) := by
          rw [← Real.rpow_natCast (Work.Cyl.rho x ^ (3 * α)) 2,
            ← Real.rpow_mul (Work.Cyl.rho_nonneg x)]
          congr 1
          ring
        have hstep1 : K * (Work.Cyl.rho x ^ (3 * α)) ^ 2
              * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α
            ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (6 * α)
              * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ α) := by
          have h1 : (Work.Cyl.rho x ^ (3 * α)) ^ 2
              ≤ (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (6 * α) := by
            rw [hsqu]
            exact Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax32)
              (by linarith : (0 : ℝ) ≤ 6 * α)
          have h2 : |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α
              ≤ (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ α :=
            Real.rpow_le_rpow hpsi_nn hpsi hα.le
          calc K * (Work.Cyl.rho x ^ (3 * α)) ^ 2
                * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α
              = K * ((Work.Cyl.rho x ^ (3 * α)) ^ 2
                * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α) := by
                ring
            _ ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (6 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ α) := by
                apply mul_le_mul_of_nonneg_left _ hK0
                exact mul_le_mul h1 h2 (Real.rpow_nonneg hpsi_nn _)
                  (Real.rpow_nonneg (by positivity) _)
        have hstep2 : K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
              * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
            ≤ K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
          have h1 : K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
              ≤ K * (3 / 2) := mul_le_mul_of_nonneg_left hmaxZ hK0
          calc K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
                * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
              ≤ K * (3 / 2) * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ = K * ((3 / 2) * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|) := by ring
            _ ≤ K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ K)
                exact mul_le_mul_of_nonneg_left hZd (by positivity)
        have hstep1' : (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (6 * α)
              * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ α
            ≤ (3 / 2) ^ (6 * α) * (4 * Real.pi) ^ α * dist x y ^ α := by
          set m : ℝ := min (Work.Cyl.rho x) (Work.Cyl.rho y) with hm
          have hm0 : 0 < m := hρminpos
          have hm1 : m ≤ 1 := le_of_lt hρmin1
          have e1 : (3 * m / 2) ^ (6 * α) = (3 / 2) ^ (6 * α) * m ^ (6 * α) := by
            rw [show 3 * m / 2 = 3 / 2 * m by ring_nf,
              Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3 / 2) hm0.le]
          have e2 : (4 * Real.pi * dist x y / m) ^ α
              = (4 * Real.pi) ^ α * dist x y ^ α * m ^ (-α) := by
            rw [show 4 * Real.pi * dist x y / m = 4 * Real.pi * dist x y * m⁻¹ by rw [div_eq_mul_inv],
              Real.mul_rpow (by positivity : (0:ℝ) ≤ 4 * Real.pi * dist x y)
                (inv_nonneg.mpr hm0.le),
              Real.mul_rpow (by positivity : (0:ℝ) ≤ 4 * Real.pi) hdnn,
              Real.inv_rpow hm0.le]
            rw [Real.rpow_neg hm0.le]
          have e3 : m ^ (6 * α) * m ^ (-α) = m ^ (5 * α) := by
            rw [← Real.rpow_add hm0]
            congr 1
            ring
          have e4 : m ^ (5 * α) ≤ 1 := Real.rpow_le_one hm0.le hm1 (by linarith)
          rw [e1, e2]
          calc (3 / 2) ^ (6 * α) * m ^ (6 * α)
                * ((4 * Real.pi) ^ α * dist x y ^ α * m ^ (-α))
              = (3 / 2) ^ (6 * α) * ((4 * Real.pi) ^ α * dist x y ^ α
                  * (m ^ (6 * α) * m ^ (-α))) := by ring
            _ = (3 / 2) ^ (6 * α) * ((4 * Real.pi) ^ α * dist x y ^ α * m ^ (5 * α)) := by
                rw [e3]
            _ ≤ (3 / 2) ^ (6 * α) * ((4 * Real.pi) ^ α * dist x y ^ α * 1) := by
                apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3 / 2) _)
                exact mul_le_mul_of_nonneg_left e4 (by positivity)
            _ = (3 / 2) ^ (6 * α) * (4 * Real.pi) ^ α * dist x y ^ α := by ring
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)|
              + |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
                  - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := hsplit
          _ ≤ K * (Work.Cyl.rho x ^ (3 * α)) ^ 2
                * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α
              + K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
                * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| :=
              add_le_add hθslice hzslice
          _ ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (6 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ α)
              + K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) :=
              add_le_add hstep1 hstep2
          _ ≤ K * ((3 / 2) ^ (6 * α) * (4 * Real.pi) ^ α * dist x y ^ α)
              + K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hstep1' hK0
              · exact le_refl _
          _ = (K * (3 / 2) ^ (6 * α) * (4 * Real.pi) ^ α
                + K * (3 / 2) * 3 ^ α * (3 / 2) ^ (2 * α)) * dist x y ^ α := by ring_nf
          _ ≤ C * dist x y ^ α :=
              mul_le_mul_of_nonneg_right hC56 (Real.rpow_nonneg hdnn α)
end Work.FTS.RegPkgGal
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.L12densAngIntegralHolder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false
-- `hN : 0 ≤ N` is kept because the requested statement carries it, but the estimate is sign-free
-- and does not need it.
set_option linter.unusedVariables false

/-- `θ ↦ |K(θ)|` is continuous on `ℝ`, where `K(θ) = 3 sin θ cos²θ`. -/
theorem continuous_abs_K : Continuous (fun θ : ℝ => |Work.Spaces.K θ|) := continuous_K.abs

/-- `θ ↦ K(θ)·F z θ τ` is `L¹` on the angular interval `Iθ`, for `z ≥ 0` and `τ ∈ [0,S]`
(this is `integrableOn_K_mul_jet_slice` with the set written as `Work.Spaces.Iθ`). -/
theorem integrableOn_K_mul_jet_slice_Iθ {α S N : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hJ : Work.FTS.Regularity.Jet α S N F) {z τ : ℝ} (hz : 0 ≤ z)
    (hτ : τ ∈ Set.Icc 0 S) :
    IntegrableOn (fun θ => Work.Spaces.K θ * F z θ τ) Work.Spaces.Iθ := by
  have h : Set.Icc (0 : ℝ) (Real.pi / 2) = Work.Spaces.Iθ := rfl
  rw [← h]
  exact integrableOn_K_mul_jet_slice hα hJ hz hτ


/-- **The angular integral of `L₁₂` is `α`-Hölder in the radial variable.**  For a `Jet` profile
`F` (bounded by `N` on `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]` and jointly `α`-Hölder there with constant
`N`), the map `s ↦ ∫_{Iθ} K(θ)·F s θ τ` is `α`-Hölder on `(0,∞)` with the explicit constant
`N·∫_{Iθ}|K|`, uniformly in `τ ∈ [0,S]`. -/
theorem L12densAngIntegralHolder {α S N : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hN : 0 ≤ N) (hJ : Work.FTS.Regularity.Jet α S N F) :
    ∀ τ ∈ Set.Icc 0 S, ∀ s ∈ Set.Ioi (0 : ℝ), ∀ s' ∈ Set.Ioi (0 : ℝ),
      |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F s θ τ)
        - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F s' θ τ)|
      ≤ (N * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ|)) * |s - s'| ^ α := by
  intro τ hτ s hs s' hs'
  have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
  have hs'0 : (0 : ℝ) ≤ s' := le_of_lt hs'
  -- integrability of the two angular slices (`K·F z · τ` is continuous on the compact `Iθ`)
  have hIntS : IntegrableOn (fun θ => Work.Spaces.K θ * F s θ τ) Work.Spaces.Iθ :=
    integrableOn_K_mul_jet_slice_Iθ hα hJ hs0 hτ
  have hIntS' : IntegrableOn (fun θ => Work.Spaces.K θ * F s' θ τ) Work.Spaces.Iθ :=
    integrableOn_K_mul_jet_slice_Iθ hα hJ hs'0 hτ
  -- integrability of the dominating function `|K|·(N·|s-s'|^α)`
  have hIntD : Integrable (fun θ : ℝ => |Work.Spaces.K θ| * (N * |s - s'| ^ α))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h : Set.Icc (0 : ℝ) (Real.pi / 2) = Work.Spaces.Iθ := rfl
    rw [← h]
    exact (continuous_abs_K.continuousOn.mul continuousOn_const).integrableOn_Icc
  -- the pointwise bound of the difference of the integrands
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ|
        ≤ |Work.Spaces.K θ| * (N * |s - s'| ^ α) := by
    intro θ hθ
    have hdiff : |F s θ τ - F s' θ τ| ≤ N * |s - s'| ^ α := hJ.zmod hs0 hs'0 hθ hτ
    have hre : Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ
        = Work.Spaces.K θ * (F s θ τ - F s' θ τ) := by ring
    rw [hre, abs_mul]
    exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
  -- the difference of the two integrals is the integral of the difference
  have hsplit : |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F s θ τ)
        - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F s' θ τ)|
      = |∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ)| := by
    rw [MeasureTheory.integral_sub hIntS hIntS']
  -- the norm of the integral is bounded by the integral of the norm
  have h1 : |∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ)|
      ≤ ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ| := by
    have hb := MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun θ => Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ)
    simpa only [Real.norm_eq_abs] using hb
  -- the monotone integral bound, then the sharp weight integral
  have h2 : (∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.K θ * F s θ τ - Work.Spaces.K θ * F s' θ τ|)
      ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ| * (N * |s - s'| ^ α) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hIntD
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hpt θ hθ)
  have h3 : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ| * (N * |s - s'| ^ α))
      = (N * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ|)) * |s - s'| ^ α := by
    rw [MeasureTheory.integral_mul_const]
    ring
  rw [hsplit]
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R1b.C1Facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R1b

open Set Filter Topology MeasureTheory
open scoped Topology Real

set_option autoImplicit false

/-! ## The two branches are `C¹` on `z > 0` -/

section Branches

variable {g : ℝ → ℝ → ℝ → ℝ} {θ : ℝ}

/-- `tauDer` is `C¹` on `z > 0`. -/
theorem tauDer_contDiffOn
    (hd1 : ContDiffOn ℝ 1 (tauDerFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))) :
    ContDiffOn ℝ 1 (tauDer g θ) (Ioi 0) := by
  have hmap : MapsTo (fun z : ℝ => (z, (0:ℝ))) (Ioi 0) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    fun z hz => ⟨hz, by norm_num⟩
  have hι : ContDiffOn ℝ 1 (fun z : ℝ => (z, (0:ℝ))) (Ioi 0) :=
    contDiffOn_id.prodMk contDiffOn_const
  have h := hd1.comp hι hmap
  change ContDiffOn ℝ 1 (fun z : ℝ => deriv (fun s => g z θ s) 0) (Ioi 0)
  exact h

/-- `jetFn` is `C¹` on `z > 0`. -/
theorem jetFn_contDiffOn
    (hbase : ContDiffOn ℝ 1 (baseFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)))
    (hdd : ContDiffOn ℝ 1 (tauDerFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))) :
    ContDiffOn ℝ 1 (jetFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := by
  have hmap : MapsTo (fun q : ℝ × ℝ => (q.1, (0:ℝ))) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))
      (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := fun q hq => ⟨hq.1, by norm_num⟩
  have hι : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => (q.1, (0:ℝ))) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    contDiffOn_fst.prodMk contDiffOn_const
  have h1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => baseFn g θ (q.1, 0)) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    hbase.comp hι hmap
  have h2 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => q.2 * tauDerFn g θ q) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    contDiffOn_snd.mul hdd
  refine (h1.add h2).congr (fun q _ => ?_)
  obtain ⟨z, τ⟩ := q
  simp only [jetFn_apply, baseFn_apply, tauDerFn_apply, Pi.add_apply]

/-- A `C¹` function on an open set has a Fréchet derivative at each point of the set. -/
theorem hasFDerivAt_of_contDiffOn_one {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) {x : ℝ × ℝ} (hx : x ∈ s) :
    HasFDerivAt f (fderiv ℝ f x) x :=
  ((hf.contDiffAt (hs.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt

/-- The `τ`-partial derivative of the jet. -/
theorem deriv_jetFn_snd (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) (z τ : ℝ) :
    deriv (fun t => jetFn g θ (z, t)) τ = tauDer g θ z := by
  have hfun : (fun t : ℝ => jetFn g θ (z, t)) = fun t : ℝ => g z θ 0 + t * tauDer g θ z := by
    funext t; simp only [jetFn_apply]
  rw [hfun, deriv_const_add]
  have h2 : HasDerivAt (fun t : ℝ => t * tauDer g θ z) (tauDer g θ z) τ := by
    simpa using (hasDerivAt_id τ).mul_const (tauDer g θ z)
  rw [h2.deriv]

/-- The `z`-partial derivative of the jet. -/
theorem deriv_jetFn_fst (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ}
    (hb : DifferentiableAt ℝ (fun z' => g z' θ 0) z)
    (hd : DifferentiableAt ℝ (tauDer g θ) z) :
    deriv (fun z' => jetFn g θ (z', τ)) z
      = deriv (fun z' => g z' θ 0) z + τ * deriv (tauDer g θ) z := by
  have hfun : (fun z' : ℝ => jetFn g θ (z', τ))
      = (fun z' : ℝ => g z' θ 0) + fun z' : ℝ => τ * tauDer g θ z' := by
    funext z'; simp only [Pi.add_apply, jetFn_apply]
  rw [hfun, deriv_add hb (hd.const_mul τ), deriv_const_mul τ hd]

/-- At `τ = 0` the jet and the family have the same Fréchet derivative (the jet is the
first-order Taylor expansion of the family in `τ`). -/
theorem fderiv_jetFn_eq_fderiv_baseFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z : ℝ}
    (hdj : DifferentiableAt ℝ (jetFn g θ) (z, 0))
    (hdb : DifferentiableAt ℝ (baseFn g θ) (z, 0)) :
    fderiv ℝ (jetFn g θ) (z, 0) = fderiv ℝ (baseFn g θ) (z, 0) := by
  rw [fderiv_eq_partials hdj, fderiv_eq_partials hdb]
  have h1 : deriv (fun z' : ℝ => jetFn g θ (z', (0:ℝ))) z
      = deriv (fun z' : ℝ => baseFn g θ (z', (0:ℝ))) z := by
    have ha : (fun z' : ℝ => jetFn g θ (z', (0:ℝ))) = fun z' : ℝ => g z' θ 0 := by
      funext z'; simp only [jetFn_apply, zero_mul, add_zero]
    have hb : (fun z' : ℝ => baseFn g θ (z', (0:ℝ))) = fun z' : ℝ => g z' θ 0 := by
      funext z'; simp only [baseFn_apply]
    rw [ha, hb]
  have h2 : deriv (fun s : ℝ => jetFn g θ (z, s)) (0:ℝ)
      = deriv (fun s : ℝ => baseFn g θ (z, s)) 0 := by
    rw [deriv_jetFn_snd]
    simp only [baseFn_apply, tauDer]
  rw [h1, h2]

end Branches

/-- At `τ = 0` the two branches of the candidate derivative agree. -/
theorem jetBranch_eq_baseBranch_at_zero (g : ℝ → ℝ → ℝ → ℝ) (θ z : ℝ) :
    jetBranch g θ (z, 0) = baseBranch g θ (z, 0) := by
  have h1 : (fun z' : ℝ => jetFn g θ (z', (0:ℝ))) = fun z' : ℝ => baseFn g θ (z', (0:ℝ)) := by
    funext z'; simp only [jetFn_apply, baseFn_apply, zero_mul, add_zero]
  have h2 : deriv (fun t : ℝ => jetFn g θ (z, t)) (0:ℝ)
      = deriv (fun t : ℝ => baseFn g θ (z, t)) 0 := by
    rw [deriv_jetFn_snd]
    simp only [baseFn_apply, tauDer]
  simp only [jetBranch, baseBranch]
  rw [h1, h2]

theorem extDeriv_eq_fderiv_baseFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : 0 ≤ τ) (hd : DifferentiableAt ℝ (baseFn g θ) (z, τ)) :
    extDeriv g θ (z, τ) = fderiv ℝ (baseFn g θ) (z, τ) := by
  rw [extDeriv_of_pos_of_nonneg' g θ hz hτ]
  exact (fderiv_eq_partials hd).symm

/-- The candidate derivative at `τ < 0` is the Fréchet derivative of the jet. -/
theorem extDeriv_eq_fderiv_jetFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : τ < 0) (hd : DifferentiableAt ℝ (jetFn g θ) (z, τ)) :
    extDeriv g θ (z, τ) = fderiv ℝ (jetFn g θ) (z, τ) := by
  rw [extDeriv_of_pos_of_neg' g θ hz hτ]
  exact (fderiv_eq_partials hd).symm

/-- **The `τ = 0` gluing** (`z > 0`): the extension is differentiable at `(z,0)` with the
candidate derivative, because the two branches have the same Fréchet derivative there. -/
theorem hasFDerivAt_extFun_join {g : ℝ → ℝ → ℝ → ℝ} {θ z : ℝ} (hz : 0 < z)
    (hbaseV : ContDiffOn ℝ 1 (baseFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)))
    (hjetV : ContDiffOn ℝ 1 (jetFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))) :
    HasFDerivAt (extFun g θ) (extDeriv g θ (z, 0)) (z, 0) := by
  have hVopen : IsOpen (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have hxV : (z, (0:ℝ)) ∈ Ioi 0 ×ˢ Ioi (-1) := ⟨hz, by norm_num⟩
  have hdj : DifferentiableAt ℝ (jetFn g θ) (z, 0) :=
    (hasFDerivAt_of_contDiffOn_one hVopen hjetV hxV).differentiableAt
  have hdb : DifferentiableAt ℝ (baseFn g θ) (z, 0) :=
    (hasFDerivAt_of_contDiffOn_one hVopen hbaseV hxV).differentiableAt
  have hfdeq : fderiv ℝ (jetFn g θ) (z, 0) = fderiv ℝ (baseFn g θ) (z, 0) :=
    fderiv_jetFn_eq_fderiv_baseFn g θ hdj hdb
  rw [extDeriv_eq_fderiv_baseFn g θ hz le_rfl hdb]
  have hst : ({y : ℝ × ℝ | 0 < y.1 ∧ y.2 ≤ 0} ∪ {y : ℝ × ℝ | 0 < y.1 ∧ 0 ≤ y.2})
      ∈ 𝓝 ((z, 0) : ℝ × ℝ) := by
    have heq : ({y : ℝ × ℝ | 0 < y.1 ∧ y.2 ≤ 0}
        ∪ {y : ℝ × ℝ | 0 < y.1 ∧ 0 ≤ y.2}) = {y : ℝ × ℝ | 0 < y.1} := by
      ext y; constructor
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
      · intro h1
        by_cases h2 : y.2 ≤ 0
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, le_of_lt (lt_of_not_ge h2)⟩
    rw [heq]
    exact (isOpen_Ioi.preimage continuous_fst).mem_nhds hz
  refine hasFDerivAt_of_union (f := extFun g θ) (f₁ := jetFn g θ) (f₂ := baseFn g θ)
    (L := fderiv ℝ (baseFn g θ) (z, 0)) (x := ((z, 0) : ℝ × ℝ))
    (s := {y : ℝ × ℝ | 0 < y.1 ∧ y.2 ≤ 0}) (t := {y : ℝ × ℝ | 0 < y.1 ∧ 0 ≤ y.2})
    hst ⟨hz, le_rfl⟩ ⟨hz, le_rfl⟩ ?_ ?_ ?_ ?_
  · rintro ⟨y1, y2⟩ ⟨hy1, hy2⟩
    rcases lt_or_eq_of_le hy2 with h | h
    · exact extFun_of_pos_of_neg g θ hy1 h
    · subst h
      rw [extFun_of_pos_of_nonneg g θ hy1 le_rfl, jetFn_eq_baseFn_at_zero]
  · rintro ⟨y1, y2⟩ ⟨hy1, hy2⟩
    exact extFun_of_pos_of_nonneg g θ hy1 hy2
  · have h := hasFDerivAt_of_contDiffOn_one hVopen hjetV hxV
    rw [hfdeq] at h
    exact h
  · exact hasFDerivAt_of_contDiffOn_one hVopen hbaseV hxV

/-- Continuity on `z > 0` of the `τ < 0` branch of the candidate derivative. -/
theorem continuousOn_jetBranch {g : ℝ → ℝ → ℝ → ℝ} {θ : ℝ}
    (hjetV : ContDiffOn ℝ 1 (jetFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))) :
    ContinuousOn (jetBranch g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := by
  have hVopen : IsOpen (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have h1 : ContinuousOn (fun q : ℝ × ℝ => deriv (fun z => jetFn g θ (z, q.2)) q.1)
      (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := continuousOn_deriv_z_slice hVopen hjetV
  have h2 : ContinuousOn (fun q : ℝ × ℝ => deriv (fun t => jetFn g θ (q.1, t)) q.2)
      (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := continuousOn_deriv_t_slice hVopen hjetV
  exact (h1.smul continuousOn_const).add (h2.smul continuousOn_const)

/-- Continuity on `z > 0` of the `τ ≥ 0` branch of the candidate derivative. -/
theorem continuousOn_baseBranch {g : ℝ → ℝ → ℝ → ℝ} {θ : ℝ}
    (hbaseV : ContDiffOn ℝ 1 (baseFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))) :
    ContinuousOn (baseBranch g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := by
  have hVopen : IsOpen (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have h1 : ContinuousOn (fun q : ℝ × ℝ => deriv (fun z => baseFn g θ (z, q.2)) q.1)
      (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := continuousOn_deriv_z_slice hVopen hbaseV
  have h2 : ContinuousOn (fun q : ℝ × ℝ => deriv (fun t => baseFn g θ (q.1, t)) q.2)
      (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := continuousOn_deriv_t_slice hVopen hbaseV
  exact (h1.smul continuousOn_const).add (h2.smul continuousOn_const)

end Work.FTS.RegPkgGal.R1b
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R2.RepairFinal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The repaired Taylor packages, unconditional

The two unconditional versions of the repaired statement, obtained by discharging the analytic
inputs of `Repair.lean`:

* `tay_clauses_nbhd` — the shape adopted by the repaired interface (`R2b`): `hsm` is taken on a
  neighbourhood of the closed angular range, `z ∈ (-1, ∞)`, `θ ∈ (-1, π/2+1)`;
* `tay_clauses_of_continuous` — the version with the *minimal* extra hypothesis, namely
  continuity of the angular slices `θ ↦ g z θ τ` on `Iθ` (for `0 < z ≤ 2`).

Both are proved with no `PLACEHOLDER` and with no axiom beyond `propext`, `Classical.choice`, `Quot.sound`.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R2


/-- **The repaired Taylor clauses with the minimal extra hypothesis.**

The hypotheses of `tay_clauses` are kept verbatim (the joint `C¹` hypothesis is still taken on
the open quadrant) and one hypothesis is *added*: each angular slice `θ ↦ g z θ τ` is continuous
on `Iθ` (for `0 < z ≤ 2`).  This is precisely the information that the counterexample of
`Work.FTS.RegPkgGal.R2.tay_clauses_refuted` violates, and it is physically necessary (a jump of
the slice at `θ = 0` would be a discontinuity of the vorticity across the plane `x₃ = 0`). -/
theorem tay_clauses_of_continuous {α S Cθ K Q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hCθ : 0 ≤ Cθ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S, ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |g z θ τ| ≤ K * z ^ 2)
    (hlinz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Q * z)
    (hcontθ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 < z → z ≤ 2 →
      ContinuousOn (fun θ => g z θ τ) Work.Spaces.Iθ) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K' * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K' * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K' * z ^ 2 * |θ - θ'| ^ α) :=
  tay_clauses_of_continuous_aux hα hα1 hS hCθ hK hQ hsm hd hvt hquad hlinz hcontθ
    (angIntegral_le hα hα1)
    (fun τ hτ z hz => integrableOn_pth_slice (g := fun z θ => g z θ τ) hα hα1 hCθ hz
      (hsm τ hτ) (fun θ hθ => hd τ hτ z θ (le_of_lt hz) hθ))

end Work.FTS.RegPkgGal.R2
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.RVocab =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

/-! ## The `St1`-class data -/

/-- **THE `St1`-CLASS DATA** of the perturbation `g` on the strip `[0,S]`: the two class
conditions of the paper's construction that are *not* consequences of `ℋ⁴`-membership (see the
module docstring):

* `dthvan` — the angular derivative `D_θ g = sin(2θ)∂_θg` is dominated by `Γ`: this is the
  quantitative form of the `Γ`-vanishing of the class.  Integrating it (using `g(z,0) = 0`) gives
  `|g| ≤ Cv Γ` (R4) and the `α`-Hölder modulus of `g` in `θ` (R3).
* `quad` — the quadratic vanishing at `z = 0` (`|g| ≤ K z²` for `z ≤ 2`) and the linear bound on
  `∂_zg` there, i.e. the Taylor datum.  The clause `z ≤ 2` is the one consumed by
  `RegPkg'.htay`. -/
structure StData (α S : ℝ) (g : Fam) : Prop where
  /-- `|D_θ g| ≤ Cθ · z² · Γ(θ)`: the `Γ`-vanishing of the angular derivative, with the `z²`
  factor that makes the class stable under `×z²` (the true profile is `g ≈ c(τ)z²Γ(θ)`).  The
  `z²` is what turns this into the *corrected* `htay` angular clause `≤ K z²|Δθ|^α`, since
  `Γ/sin(2θ) ≈ θ^{α-1}` integrates to `θ^α`. -/
  dthvan : ∃ Cθ : ℝ, 0 ≤ Cθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
    |Work.Spaces.Dth (gSlice g τ) z θ| ≤ Cθ * z ^ 2 * Gamma α θ
  /-- the quadratic vanishing of `g` at `z = 0`, and the linear vanishing of `∂_zg` there -/
  quad : ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K * z ^ 2) ∧
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |Work.Spaces.pz (gSlice g τ) z θ| ≤ Q * z)



/-! ## The dynamic profile equation `(E)` -/

/-- The left-hand side of the **dynamic profile equation** `(E)` at a point, with the fake-time
derivative `Fτ` as a parameter: `Fτ + (1+μ)F + (1-μ)D_zF + UVR α F Φ`. -/
def dynEqLHS (α : ℝ) (μ : ℝ) (F Φ : ℝ → ℝ → ℝ) (Z Θ Fτ : ℝ) : ℝ :=
  Fτ + (1 + μ) * F Z Θ + (1 - μ) * Work.Spaces.Dz F Z Θ + Work.Construction.UVR α F Φ Z Θ

/-- **The dynamic profile equation `(E)`** (design §3): the paper's modulation equation for the
*full* profile `F = F_* + g` in fake time,

  `∂_τ F + (1+μ(τ))·F + (1-μ(τ))·D_z F + UVR α F Φ = 0`   on the open quadrant, `τ > 0`.

Its transport form is what R7 (support propagation along characteristics) is stated over.  This is
a copy of `Work.FTS.MeridianDyn.DynEqF` (sibling area `MeridianDyn`, which owns the passage from
`IsDynEqOn`). -/
def DynEqF (α : ℝ) (μ : ℝ → ℝ) (F Φ : Fam) : Prop :=
  ∀ z θ τ : ℝ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
    deriv (fun s => F z θ s) τ + (1 + μ τ) * F z θ τ
      + (1 - μ τ) * Work.Spaces.Dz (famSlice F τ) z θ
      + Work.Construction.UVR α (famSlice F τ) (famSlice Φ τ) z θ = 0

theorem DynEqF.eq {α : ℝ} {μ : ℝ → ℝ} {F Φ : Fam} (h : DynEqF α μ F Φ)
    {z θ τ : ℝ} (hz : (z, θ) ∈ Work.Construction.Qd) (hτ : 0 < τ) :
    deriv (fun s => F z θ s) τ + (1 + μ τ) * F z θ τ
      + (1 - μ τ) * Work.Spaces.Dz (famSlice F τ) z θ
      + Work.Construction.UVR α (famSlice F τ) (famSlice Φ τ) z θ = 0 :=
  h z θ τ hz hτ

theorem DynEqF.pointwise {α : ℝ} {μ : ℝ → ℝ} {F Φ : Fam} (h : DynEqF α μ F Φ)
    {Z Θ τ : ℝ} (hZ : (Z, Θ) ∈ Work.Construction.Qd) (hτ : 0 < τ) :
    dynEqLHS α (μ τ) (famSlice F τ) (famSlice Φ τ) Z Θ (deriv (fun s => F Z Θ s) τ) = 0 := by
  have h0 := h Z Θ τ hZ hτ
  rw [dynEqLHS]
  simpa only [famSlice, Work.FTS.Galerkin.slice_apply, Work.Spaces.Dz] using h0

/-! ## The clock of the modulation (design §2)

The vorticity amplitude `A_v` and the space scale `B` of the reconstruction are the exponentials of
the two modulation rates `1 ± m`, `m = muDyn` (design §2, item 8):
`A_v(τ) = exp(-∫_0^τ(1+m))`, `B(τ) = exp(-∫_0^τ(1-m))`; note `(1+m)(1+λ) = 1-m` for
`λ = -2m/(1+m)`, which is the paper's second modulation constant (`Galerkin.lamDyn`). -/

/-- `A_v(τ) = exp(-∫_0^τ (1+m(s)) ds)` of the design §2. -/
noncomputable def Avort (m : ℝ → ℝ) (τ : ℝ) : ℝ :=
  Real.exp (-∫ s in (0 : ℝ)..τ, (1 + m s))

/-- `B(τ) = exp(-∫_0^τ (1-m(s)) ds)` of the design §2. -/
noncomputable def Bdyn (m : ℝ → ℝ) (τ : ℝ) : ℝ :=
  Real.exp (-∫ s in (0 : ℝ)..τ, (1 - m s))

theorem Avort_zero (m : ℝ → ℝ) : Avort m 0 = 1 := by simp [Avort]

theorem Bdyn_zero (m : ℝ → ℝ) : Bdyn m 0 = 1 := by simp [Bdyn]

end Work.FTS.RegPkgGal
end
end
