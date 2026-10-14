import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.LWP.Main
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
import Submission.Work.StabilityFar.St4
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_ball_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric
open Work.StabilityFar.Decay (kf crossL)

/-- **The Biot–Savart field as an integral over the fixed ball `B(0,ρ)`.**

The Newtonian-potential Biot–Savart field is the full-space Bochner integral of the kernel
`bsK ω x a = ‖x-a‖⁻³ • (ω a × (x-a))`.  When `ω` is supported in `closedBall 0 R` and
`R + ‖x‖ ≤ ρ`, the support of the integrand misses `B(0,ρ)ᶜ` up to the sphere `sphere 0 ρ`,
which is `volume`-null; hence the full integral coincides with the integral over `B(0,ρ)`.

Since the restricted integrand is `crossL (ω a) (kf (x-a))` (`bsK_eq_crossL`), this identifies
`biotSavart ω x` with `(4π)⁻¹ • bsField ω ρ x` — the un-normalised field on which the
Calderón–Zygmund differentiation of the Biot–Savart operator is carried out. -/
theorem biotSavart_ball_integral {ω : Work.LWP.R3 → Work.LWP.R3} {R M ρ : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) {x : Work.LWP.R3}
    (hρ : R + ‖x‖ ≤ ρ) :
    Work.LWP.biotSavart ω x = (4 * Real.pi)⁻¹ • Work.CoreResiduals.BiotSavart.bsField ω ρ x := by
  -- `R + ‖x‖ ≤ ρ` gives in particular `R ≤ ρ`, so the support of `ω` lies in `closedBall 0 ρ`.
  have hRle : R ≤ ρ := by have := norm_nonneg x; linarith
  -- The kernel scalar `(4π)⁻¹` is common to both sides; the content is the identity of the
  -- underlying Bochner integrals.
  have hkey : ∫ y, Work.LWP.BiotSavart.bsK ω x y
      = ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a) (kf (x - a)) := by
    -- Replace the integrand by its indicator on `B(0,ρ)` (an a.e. equality) and then unfold the
    -- restricted integral into the integral of that indicator.
    rw [← MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
      (f := fun a => crossL (ω a) (kf (x - a))) measurableSet_ball]
    refine MeasureTheory.integral_congr_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    -- The two integrands can only differ on points of `sphere 0 ρ`, a null set.
    refine MeasureTheory.measure_mono_null ?_
      (MeasureTheory.Measure.addHaar_sphere MeasureTheory.volume (0 : Work.LWP.R3) ρ)
    intro a ha
    rw [Set.mem_ofPred_eq] at ha
    by_cases hmem : a ∈ Metric.ball (0 : Work.LWP.R3) ρ
    · -- Inside the ball the indicator is the integrand itself, so the two sides agree there.
      exact absurd (by rw [Set.indicator_of_mem hmem,
        Work.StabilityFar.Decay.bsK_eq_crossL]) ha
    · -- Outside the ball the indicator vanishes; a non-vanishing kernel forces `ω a ≠ 0`,
      -- hence `‖a‖ ≤ R ≤ ρ`, so `dist a 0 = ρ` and `a` lies on the null sphere.
      have hzero : (Metric.ball (0 : Work.LWP.R3) ρ).indicator
          (fun a => crossL (ω a) (kf (x - a))) a = 0 := Set.indicator_of_notMem hmem _
      have hb : Work.LWP.BiotSavart.bsK ω x a ≠ 0 := fun h0 => ha (by rw [hzero, h0])
      have hωa : ω a ≠ 0 := fun h0 => hb (Work.LWP.BiotSavart.bsK_eq_zero h0)
      have haR : dist a 0 ≤ R := Metric.mem_closedBall.mp (hs a hωa)
      have h5 : ρ ≤ dist a 0 := not_lt.mp hmem
      exact Metric.mem_sphere.mpr (le_antisymm (le_trans haR hRle) h5)
  rw [Work.LWP.BiotSavart.biotSavart_apply, hkey,
    Work.CoreResiduals.BiotSavart.bsField.eq_def]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_centred_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric

/-! ## Two elementary facts about the Biot–Savart kernel at a constant vorticity

The regularisation `ω ↦ ω - ω x` inside the Biot–Savart integral replaces the integrand
`bsK ω x` by its difference with the integrand of the *constant* vorticity `ω x`.  The latter
is not globally integrable (the constant vorticity is not supported in any ball), but it is
locally integrable, and the only integrability information the subtraction
`∫ (f - g) = ∫ f - ∫ g` needs is that of `g` on the ball `B(x,ρ)`.  We provide it here: the
kernel of a constant vorticity is dominated by `‖v‖·‖x-a‖⁻²`, which is integrable on any ball
of `ℝ³` (the borderline case `2 < 3 = dim`). -/




end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.farStrip_estimates_timeBlock =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open FiniteTimeSingularity

/-- **The far-field estimates for the time block `E(x,t) = BS (∂ₜω(·,t)) x` on the strip**
`Icc 0 S`.

The strip analogue of the three inputs for the `∂ₜu` block that `St4` consumes
(`Work.StabilityFar.velocity_decay_timeDeriv`, `Work.StabilityFar.Decay.timeDeriv_timeHolder`,
`Work.StabilityFar.timeDeriv_lipschitz_x`), with the window-indexed hypotheses replaced by the
strip bundle on `Icc 0 S`.  All three need the *support of `∂ₜω` on the strip*, which for a strip
bundle with `0 < S` holds (the short argument: at an interior time by
`Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall`, at the endpoint `t = 0` by
restricting the bundle's two-sided `HasDerivAt` to `Ioi 0` and using that the slice vanishes there
— this is the statement `Work.CoreResiduals.BiotSavart.slicesSupportedStrip_timeDeriv`, available
as `import Submission.Work.CoreResiduals.BiotSavart.slicesSupportedStrip_timeDeriv`).

* *bound*: `‖E(x,t)‖ ≤ (4/3)·M₁·R³/‖x‖²` for `2R ≤ ‖x‖` (`farField_decay_const` applied to the
  slice `∂ₜω(·,t)`, bounded by the bundle's uniform bound `M₁` and supported in `B(0,R)`);
* *`t`-Hölder*: `‖E(x,t) - E(x,τ)‖ ≤ Atu·|t-τ|^α` for `2R < ‖x‖`, `t,τ ∈ Icc 0 S`
  (`Decay.biotSavart_timeDeriv_sub_le`: the difference `∂ₜω(·,t) - ∂ₜω(·,τ)` is supported in
  `B(0,R)` and bounded by `N₁|t-τ|^α` by the bundle's `TimeDerivStripHolder`; note that fact is
  stated in the two-sided window form, so redo its short proof on `Icc 0 S`);
* *`x`-Lipschitz*: `‖E(x,t) - E(y,t)‖ ≤ A₁‖x-y‖` for `2R+5 < ‖x‖` and `‖x-y‖ ≤ 1`
  (`Work.LWP.BiotSavart.biotSavart_lipschitzOn_far`, as in
  `Work.StabilityFar.timeDeriv_lipschitz_x`). -/
theorem farStrip_estimates_timeBlock {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ} (hS : 0 < S)
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∃ M₁ Atu A₁ : ℝ, 0 ≤ M₁ ∧ 0 ≤ Atu ∧ 0 ≤ A₁ ∧
      (∀ t ∈ Set.Icc (0:ℝ) S, ∀ x : Work.LWP.R3, 2 * R ≤ ‖x‖ →
        ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y t) x‖
          ≤ (4 / 3) * M₁ * R ^ 3 / ‖x‖ ^ 2) ∧
      (∀ x : Work.LWP.R3, 2 * R < ‖x‖ → ∀ t ∈ Set.Icc (0:ℝ) S, ∀ τ ∈ Set.Icc (0:ℝ) S,
        ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y t) x
          - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y τ) x‖
          ≤ Atu * |t - τ| ^ (α : ℝ)) ∧
      (∀ t ∈ Set.Icc (0:ℝ) S, ∀ x y : Work.LWP.R3, 2 * R + 5 < ‖x‖ → ‖x - y‖ ≤ 1 →
        ‖Work.LWP.biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x
          - Work.LWP.biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y‖
          ≤ A₁ * ‖x - y‖) := by
  -- ## Unpack the strip bundle (keeping a copy for the support lemma)
  have hbunKeep : Work.CoreResiduals.BSAdmissibleStripFull α ω R S := hbun
  unfold Work.CoreResiduals.BSAdmissibleStripFull at hbun
  obtain ⟨hstrip, htd, hholder⟩ := hbun
  unfold Work.CoreResiduals.BSAdmissibleStrip at hstrip
  obtain ⟨hRpos, _hsuppω, _hbddω, _hholderω, _htimeω, _hmeasω⟩ := hstrip
  unfold Work.CoreResiduals.TimeDerivStrip at htd
  obtain ⟨_hHasDeriv, hbddDt₀, hmeasDt⟩ := htd
  unfold Work.CoreResiduals.TimeDerivStripHolder at hholder
  obtain ⟨N₀, hN₀⟩ := hholder
  -- ## The support of `∂ₜω` on the strip
  have hsuppDt : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : Work.LWP.R3,
      FiniteTimeSingularity.timeDeriv ω y t ≠ 0 → y ∈ Metric.closedBall 0 R :=
    slicesSupportedStrip_timeDeriv hS hbunKeep
  -- ## The constants
  obtain ⟨M₀, hM₀⟩ := hbddDt₀
  set M₁ : ℝ := max M₀ 0 with hM₁def
  have hM₁nonneg : 0 ≤ M₁ := by rw [hM₁def]; exact le_max_right _ _
  have hbddDt : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : Work.LWP.R3,
      ‖FiniteTimeSingularity.timeDeriv ω y t‖ ≤ M₁ := by
    intro t ht y
    rw [hM₁def]
    exact le_trans (hM₀ t ht y) (le_max_left _ _)
  set N₁ : ℝ := max N₀ 0 with hN₁def
  have hN₁nonneg : 0 ≤ N₁ := by rw [hN₁def]; exact le_max_right _ _
  have hholderN : ∀ y : Work.LWP.R3, ∀ t ∈ Set.Icc (0:ℝ) S, ∀ t' ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω y t - FiniteTimeSingularity.timeDeriv ω y t'‖
        ≤ N₁ * |t - t'| ^ (α : ℝ) := by
    intro y t ht t' ht'
    rw [hN₁def]
    exact le_trans (hN₀ y t ht t' ht')
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))
  set Atu : ℝ := N₁ * R / 3 with hAtudef
  set A₁ : ℝ := 2 ^ 17 * M₁ with hA₁def
  have hAtunonneg : 0 ≤ Atu := by
    rw [hAtudef]; exact div_nonneg (mul_nonneg hN₁nonneg hRpos.le) (by norm_num)
  have hA₁nonneg : 0 ≤ A₁ := by rw [hA₁def]; positivity
  refine ⟨M₁, Atu, A₁, hM₁nonneg, hAtunonneg, hA₁nonneg, ?_, ?_, ?_⟩
  · -- ## Clause 1: the far-field bound
    intro t ht x hx
    exact Work.LWP.BiotSavart.farField_decay_const hRpos.le hM₁nonneg
      (fun y => hbddDt t ht y) (fun y => hsuppDt t ht y) x hx
  · -- ## Clause 2: the `t`-Hölder bound
    intro x hx t ht τ hτ
    have hs : 0 ≤ |t - τ| ^ (α : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    -- linearity of Biot–Savart
    have hsub : Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y t) x
        - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y τ) x
        = Work.LWP.biotSavart
            ((fun y => FiniteTimeSingularity.timeDeriv ω y t)
              - (fun y => FiniteTimeSingularity.timeDeriv ω y τ)) x :=
      (Work.StabilityFar.Decay.biotSavart_sub hRpos.le hM₁nonneg
        (fun y => hbddDt t ht y) (fun y => hbddDt τ hτ y)
        (fun y => hsuppDt t ht y) (fun y => hsuppDt τ hτ y)
        (hmeasDt t ht) (hmeasDt τ hτ) x).symm
    rw [hsub]
    -- the difference field is supported in `B(0,R)` and bounded by `N₁|t-τ|^α`
    have hbddDiff : ∀ y : Work.LWP.R3,
        ‖((fun y => FiniteTimeSingularity.timeDeriv ω y t)
            - (fun y => FiniteTimeSingularity.timeDeriv ω y τ)) y‖
          ≤ N₁ * |t - τ| ^ (α : ℝ) := by
      intro y
      rw [Pi.sub_apply]
      by_cases hy : y ∈ Metric.closedBall 0 R
      · exact hholderN y t ht τ hτ
      · have ht0 : FiniteTimeSingularity.timeDeriv ω y t = 0 := by
          by_contra hne; exact hy (hsuppDt t ht y hne)
        have hτ0 : FiniteTimeSingularity.timeDeriv ω y τ = 0 := by
          by_contra hne; exact hy (hsuppDt τ hτ y hne)
        rw [ht0, hτ0, sub_zero, norm_zero]
        exact mul_nonneg hN₁nonneg hs
    have hsuppDiff : ∀ y : Work.LWP.R3,
        ((fun y => FiniteTimeSingularity.timeDeriv ω y t)
            - (fun y => FiniteTimeSingularity.timeDeriv ω y τ)) y ≠ 0 →
          y ∈ Metric.closedBall 0 R := by
      intro y hy
      by_contra hcon
      apply hy
      rw [Pi.sub_apply]
      have ht0 : FiniteTimeSingularity.timeDeriv ω y t = 0 := by
        by_contra hne; exact hcon (hsuppDt t ht y hne)
      have hτ0 : FiniteTimeSingularity.timeDeriv ω y τ = 0 := by
        by_contra hne; exact hcon (hsuppDt τ hτ y hne)
      rw [ht0, hτ0, sub_zero]
    have hfar := Work.LWP.BiotSavart.farField_decay_const hRpos.le
      (mul_nonneg hN₁nonneg hs) hbddDiff hsuppDiff x hx.le
    refine hfar.trans ?_
    -- `R³/‖x‖² ≤ R/4`
    have hkey : R ^ 3 / ‖x‖ ^ 2 ≤ R / 4 := by
      have hXpos : 0 < ‖x‖ ^ 2 := pow_pos (by linarith) 2
      rw [div_le_iff₀ hXpos, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      have h2 : (2 * R) ^ 2 ≤ ‖x‖ ^ 2 := by
        have h1 : 0 ≤ 2 * R := by linarith
        simpa using pow_le_pow_left₀ h1 hx.le 2
      nlinarith [h2]
    have hstep : (4 / 3) * (N₁ * |t - τ| ^ (α : ℝ)) * R ^ 3 / ‖x‖ ^ 2
        = (4 / 3) * (N₁ * |t - τ| ^ (α : ℝ)) * (R ^ 3 / ‖x‖ ^ 2) := by ring
    rw [hstep]
    calc (4 / 3) * (N₁ * |t - τ| ^ (α : ℝ)) * (R ^ 3 / ‖x‖ ^ 2)
        ≤ (4 / 3) * (N₁ * |t - τ| ^ (α : ℝ)) * (R / 4) :=
          mul_le_mul_of_nonneg_left hkey (by nlinarith [hN₁nonneg, hs])
      _ = (N₁ * R / 3) * |t - τ| ^ (α : ℝ) := by ring
      _ = Atu * |t - τ| ^ (α : ℝ) := by rw [hAtudef]
  · -- ## Clause 3: the `x`-Lipschitz bound
    intro t ht x y hx hxy
    have hxR : 2 * R ≤ ‖x‖ := by linarith
    have hxpos : 0 < ‖x‖ := by linarith
    have hxmem : x ∈ Metric.ball x (‖x‖ / 4) := by
      rw [Metric.mem_ball, dist_self]; linarith
    have hymem : y ∈ Metric.ball x (‖x‖ / 4) := by
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; linarith
    have hlipfar := Work.LWP.BiotSavart.biotSavart_lipschitzOn_far hRpos.le hM₁nonneg
      (fun z => hbddDt t ht z) (fun z => hsuppDt t ht z) (hmeasDt t ht) hxR
    rw [lipschitzOnWith_iff_norm_sub_le] at hlipfar
    have hb := hlipfar hxmem hymem
    have hK : (2 ^ 20 : ℝ) * M₁ * R ^ 3 / ‖x‖ ^ 3 ≤ A₁ := by
      rw [hA₁def]
      have hxx : (2 * R) ^ 3 ≤ ‖x‖ ^ 3 := pow_le_pow_left₀ (by linarith) hxR 3
      have h8 : (2 * R) ^ 3 = 8 * R ^ 3 := by ring
      rw [div_le_iff₀ (pow_pos hxpos 3)]
      have hstep : 2 ^ 17 * M₁ * (8 * R ^ 3) ≤ 2 ^ 17 * M₁ * ‖x‖ ^ 3 :=
        mul_le_mul_of_nonneg_left (by rw [← h8]; exact hxx) (by positivity)
      have hpow : (2 : ℝ) ^ 20 = 2 ^ 17 * 8 := by norm_num
      nlinarith [hstep, hpow]
    calc ‖Work.LWP.biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x
          - Work.LWP.biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y‖
        ≤ (((2 ^ 20 : ℝ) * M₁ * R ^ 3 / ‖x‖ ^ 3).toNNReal : ℝ) * ‖x - y‖ := hb
      _ = (2 ^ 20 * M₁ * R ^ 3 / ‖x‖ ^ 3) * ‖x - y‖ := by
          rw [Real.coe_toNNReal _ (by positivity)]
      _ ≤ A₁ * ‖x - y‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_general =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **The `∂ₜ`-slices of a bundled strip vorticity are Hölder in `x`.**  This is the statement of
the already-proved `Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_of_stripBundle`
(`Submission/Work/CoreResiduals/BiotSavart/timeDeriv_xHolderOn_of_stripBundle.lean`) with the
hypothesis `hα1 : (α : ℝ) < 1` deleted: that hypothesis is never used in the existing proof
(grep `hα1` in that file: only the signature line mentions it), so the same proof establishes the
statement below verbatim with `hα1` removed.  Do NOT re-derive the mathematics: copy the existing
proof body and drop the hypothesis (both reviewers confirmed this by compiling the copy). -/
theorem timeDeriv_xHolderOn_general {α : NNReal} (hα : 0 < (α : ℝ))
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ} (hS : 0 < S)
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Work.LWP.R3, ∀ t ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω a t - FiniteTimeSingularity.timeDeriv ω b t‖
        ≤ C * ‖a - b‖ ^ c := by
  obtain ⟨⟨_, _, ⟨_, _⟩, ⟨H, hH⟩, ⟨_, _⟩, _⟩,
    ⟨hdc, ⟨M₁, hM₁⟩, _⟩, ⟨N₁, hN₁⟩⟩ := hbun
  -- `A = α` as a real, `k = α/(1+α)`, and the Hölder exponent `c = α²/(1+α) = A * k`.
  set A : ℝ := (α : ℝ) with hAdef
  have hApos : 0 < A := by rw [hAdef]; exact hα
  set H₀ : ℝ := (H : ℝ) with hH₀def
  have hH₀nn : 0 ≤ H₀ := by rw [hH₀def]; positivity
  -- the positive parts of the two real bounds
  set N₀ : ℝ := max N₁ 0 with hN₀def
  have hN₀nn : 0 ≤ N₀ := by rw [hN₀def]; exact le_max_right _ _
  set M₀ : ℝ := max M₁ 0 with hM₀def
  have hM₀nn : 0 ≤ M₀ := by rw [hM₀def]; exact le_max_right _ _
  set k : ℝ := A / (1 + A) with hkdef
  have hkpos : 0 < k := by rw [hkdef]; exact div_pos hApos (by linarith)
  have h1A : k * (1 + A) = A := by rw [hkdef]; field_simp
  have hS2 : 0 < S / 2 := by linarith
  have hSpow : 0 < (S / 2) ^ A := Real.rpow_pos_of_pos hS2 A
  set C₀ : ℝ := max (2 * (N₀ + H₀)) (2 * M₀ / (S / 2) ^ A) with hC₀def
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀def]; exact le_trans (by linarith) (le_max_left _ _)
  refine ⟨A * k, mul_pos hApos hkpos, C₀, hC₀nn, ?_⟩
  intro a b t ht
  by_cases hab : a = b
  · subst hab
    have hcne : A * k ≠ 0 := (mul_pos hApos hkpos).ne'
    simp [Real.zero_rpow hcne]
  · -- the generic case: `a ≠ b`
    set ψ : ℝ → Work.LWP.R3 := fun s => ω a s - ω b s with hψdef
    set ψ' : ℝ → Work.LWP.R3 := fun s =>
      FiniteTimeSingularity.timeDeriv ω a s - FiniteTimeSingularity.timeDeriv ω b s with hψ'def
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hnormpos : 0 < ‖a - b‖ := norm_pos_iff.mpr hne
    -- the step size `hh = ‖a-b‖^k`
    set hh : ℝ := ‖a - b‖ ^ k with hhdef
    have hhpos : 0 < hh := by rw [hhdef]; exact Real.rpow_pos_of_pos hnormpos k
    have hhA : hh ^ A = ‖a - b‖ ^ (A * k) := by
      rw [hhdef, ← Real.rpow_mul hnormpos.le k A, mul_comm k A]
    have hh1A : hh ^ (1 + A) = ‖a - b‖ ^ A := by
      rw [hhdef, ← Real.rpow_mul hnormpos.le k (1 + A), h1A]
    -- the `x`-Hölder bound on the slices of `ψ`
    have hψ_bound : ∀ s ∈ Set.Icc (0:ℝ) S, ‖ψ s‖ ≤ H₀ * ‖a - b‖ ^ A := by
      intro s hs
      rw [hψdef]
      have h2 := (hH s hs).dist_le a b
      rw [dist_eq_norm, dist_eq_norm] at h2
      calc ‖ω a s - ω b s‖ ≤ (H:ℝ) * ‖a - b‖ ^ (α:ℝ) := h2
        _ = H₀ * ‖a - b‖ ^ A := by rw [hH₀def, hAdef]
    -- `ψ` is differentiable in `t` on the strip, with derivative `ψ'`
    have hψderiv : ∀ x ∈ Set.Icc (0:ℝ) S, HasDerivAt ψ (ψ' x) x := by
      intro x hx
      exact (hdc x hx a).sub (hdc x hx b)
    -- the `α`-Hölder bound on `∂ₜω` with the nonnegative constant `N₀`
    have key₁ : ∀ y : Work.LWP.R3, ∀ s ∈ Set.Icc (0:ℝ) S, ∀ s' ∈ Set.Icc (0:ℝ) S,
        ‖FiniteTimeSingularity.timeDeriv ω y s - FiniteTimeSingularity.timeDeriv ω y s'‖
          ≤ N₀ * |s - s'| ^ A := by
      intro y s hs s' hs'
      have h1 := hN₁ y s hs s' hs'
      rcases le_total 0 N₁ with h | h
      · rw [hN₀def, max_eq_left h, hAdef]
        exact h1
      · rw [hN₀def, max_eq_right h, hAdef, zero_mul]
        have hr : 0 ≤ |s - s'| ^ A := Real.rpow_nonneg (abs_nonneg _) _
        have h2 : N₁ * |s - s'| ^ A ≤ 0 := by nlinarith
        exact le_trans h1 h2
    have key₂ : ∀ s ∈ Set.Icc (0:ℝ) S, ∀ s' ∈ Set.Icc (0:ℝ) S,
        ‖ψ' s - ψ' s'‖ ≤ 2 * N₀ * |s - s'| ^ A := by
      intro s hs s' hs'
      have h1 := key₁ a s hs s' hs'
      have h2 := key₁ b s hs s' hs'
      rw [hψ'def]
      calc ‖(FiniteTimeSingularity.timeDeriv ω a s - FiniteTimeSingularity.timeDeriv ω b s)
              - (FiniteTimeSingularity.timeDeriv ω a s' - FiniteTimeSingularity.timeDeriv ω b s')‖
          ≤ ‖FiniteTimeSingularity.timeDeriv ω a s - FiniteTimeSingularity.timeDeriv ω a s'‖
            + ‖FiniteTimeSingularity.timeDeriv ω b s - FiniteTimeSingularity.timeDeriv ω b s'‖ := by
            rw [sub_sub_sub_comm]
            exact norm_sub_le _ _
        _ ≤ N₀ * |s - s'| ^ A + N₀ * |s - s'| ^ A := add_le_add h1 h2
        _ = 2 * N₀ * |s - s'| ^ A := by ring
    -- the mean value step on a small interval around `t` of length `hh`
    have core : ∀ u ∈ Set.Icc (0:ℝ) S, |u - t| = hh →
        (∀ x ∈ Set.uIcc t u, |x - t| ≤ hh) →
        hh * ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * hh ^ (1 + A) := by
      intro u hu hueq hwin
      set f : ℝ → Work.LWP.R3 := fun s => ψ s - (s - t) • ψ' t with hfdef
      have hseg : Set.uIcc t u ⊆ Set.Icc (0:ℝ) S := by
        intro x hx
        exact ⟨le_trans (le_min ht.1 hu.1) hx.1, le_trans hx.2 (max_le ht.2 hu.2)⟩
      have hfd : ∀ x ∈ Set.uIcc t u, HasDerivAt f (ψ' x - ψ' t) x := by
        intro x hx
        have hxS := hseg hx
        have h2 : HasDerivAt (fun s : ℝ => (s - t) • ψ' t) (ψ' t) x := by
          have hh2 := ((hasDerivAt_id x).sub_const t).smul_const (ψ' t)
          rw [one_smul] at hh2
          exact hh2
        exact (hψderiv x hxS).sub h2
      have hdiff : ∀ x ∈ Set.uIcc t u, DifferentiableAt ℝ f x :=
        fun x hx => (hfd x hx).differentiableAt
      have hbound : ∀ x ∈ Set.uIcc t u, ‖deriv f x‖ ≤ 2 * N₀ * hh ^ A := by
        intro x hx
        rw [(hfd x hx).deriv]
        have hxS := hseg hx
        have hk := key₂ x hxS t ht
        have hr : |x - t| ^ A ≤ hh ^ A :=
          Real.rpow_le_rpow (abs_nonneg _) (hwin x hx) hApos.le
        calc ‖ψ' x - ψ' t‖ ≤ 2 * N₀ * |x - t| ^ A := hk
          _ ≤ 2 * N₀ * hh ^ A := mul_le_mul_of_nonneg_left hr (by linarith)
      have hmvt : ‖f u - f t‖ ≤ 2 * N₀ * hh ^ A * ‖u - t‖ :=
        Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_uIcc t u)
          Set.left_mem_uIcc Set.right_mem_uIcc
      have hmvt' : ‖f u - f t‖ ≤ 2 * N₀ * (hh ^ A * hh) := by
        have hnorm : ‖u - t‖ = hh := by rw [Real.norm_eq_abs, hueq]
        calc ‖f u - f t‖ ≤ 2 * N₀ * hh ^ A * ‖u - t‖ := hmvt
          _ = 2 * N₀ * (hh ^ A * hh) := by rw [hnorm, mul_assoc]
      have hkey : (u - t) • ψ' t = (ψ u - ψ t) - (f u - f t) := by
        simp only [hfdef]
        rw [sub_self, zero_smul, sub_zero]
        abel
      have htri : ‖(u - t) • ψ' t‖ ≤ ‖ψ u - ψ t‖ + ‖f u - f t‖ := by
        rw [hkey]; exact norm_sub_le _ _
      have hLHS : ‖(u - t) • ψ' t‖ = hh * ‖ψ' t‖ := by
        rw [norm_smul, Real.norm_eq_abs, hueq]
      have h1 : ‖ψ u - ψ t‖ ≤ 2 * H₀ * ‖a - b‖ ^ A := by
        have hψu := hψ_bound u hu
        have hψt := hψ_bound t ht
        calc ‖ψ u - ψ t‖ ≤ ‖ψ u‖ + ‖ψ t‖ := norm_sub_le _ _
          _ ≤ H₀ * ‖a - b‖ ^ A + H₀ * ‖a - b‖ ^ A := add_le_add hψu hψt
          _ = 2 * H₀ * ‖a - b‖ ^ A := by ring
      calc hh * ‖ψ' t‖ = ‖(u - t) • ψ' t‖ := hLHS.symm
        _ ≤ ‖ψ u - ψ t‖ + ‖f u - f t‖ := htri
        _ ≤ 2 * H₀ * ‖a - b‖ ^ A + 2 * N₀ * (hh ^ A * hh) := add_le_add h1 hmvt'
        _ = 2 * (N₀ + H₀) * hh ^ (1 + A) := by
            have h3 : hh ^ A * hh = hh ^ (1 + A) := by
              rw [Real.rpow_add hhpos 1 A, Real.rpow_one]; ring
            rw [hh1A.symm, h3]; ring
    by_cases hle : hh ≤ S / 2
    · -- a full interval of length `hh` fits inside the strip around `t`
      have hmain : hh * ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * hh ^ (1 + A) := by
        rcases le_total hh t with hhle | hhle
        · -- the interval `[t-hh, t]`
          have hu : t - hh ∈ Set.Icc (0:ℝ) S := ⟨by linarith, by linarith [ht.2]⟩
          have hueq : |(t - hh) - t| = hh := by
            have h4 : (t - hh) - t = -hh := by ring
            rw [h4, abs_neg, abs_of_pos hhpos]
          have hwin : ∀ x ∈ Set.uIcc t (t - hh), |x - t| ≤ hh := by
            intro x hx
            rw [Set.uIcc_of_ge (by linarith : t - hh ≤ t)] at hx
            rw [abs_le]
            exact ⟨by linarith [hx.1], by linarith [hx.2, hhpos.le]⟩
          exact core (t - hh) hu hueq hwin
        · -- the interval `[t, t+hh]`
          have hu : t + hh ∈ Set.Icc (0:ℝ) S :=
            ⟨by linarith [ht.1], by linarith [hhle, hle]⟩
          have hueq : |(t + hh) - t| = hh := by
            have h4 : (t + hh) - t = hh := by ring
            rw [h4, abs_of_pos hhpos]
          have hwin : ∀ x ∈ Set.uIcc t (t + hh), |x - t| ≤ hh := by
            intro x hx
            rw [Set.uIcc_of_le (by linarith : t ≤ t + hh)] at hx
            rw [abs_le]
            exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
          exact core (t + hh) hu hueq hwin
      have hfinal : ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * ‖a - b‖ ^ (A * k) := by
        have h4 : 2 * (N₀ + H₀) * hh ^ (1 + A) = hh * (2 * (N₀ + H₀) * hh ^ A) := by
          rw [Real.rpow_add hhpos 1 A, Real.rpow_one]; ring
        have h5 := h4 ▸ hmain
        have h6 : ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * hh ^ A := le_of_mul_le_mul_left h5 hhpos
        rwa [hhA] at h6
      calc ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * ‖a - b‖ ^ (A * k) := hfinal
        _ ≤ C₀ * ‖a - b‖ ^ (A * k) :=
            mul_le_mul_of_nonneg_right (by rw [hC₀def]; exact le_max_left _ _)
              (Real.rpow_nonneg (norm_nonneg _) _)
    · -- the step size is large: crudely bound `‖ψ' t‖` by `2 M₀`
      have hcrude : ‖ψ' t‖ ≤ 2 * M₀ := by
        have h1 : ‖FiniteTimeSingularity.timeDeriv ω a t‖ ≤ M₀ := by
          rw [hM₀def]; exact le_trans (hM₁ t ht a) (le_max_left _ _)
        have h2 : ‖FiniteTimeSingularity.timeDeriv ω b t‖ ≤ M₀ := by
          rw [hM₀def]; exact le_trans (hM₁ t ht b) (le_max_left _ _)
        calc ‖ψ' t‖ = ‖FiniteTimeSingularity.timeDeriv ω a t
            - FiniteTimeSingularity.timeDeriv ω b t‖ := rfl
          _ ≤ ‖FiniteTimeSingularity.timeDeriv ω a t‖
              + ‖FiniteTimeSingularity.timeDeriv ω b t‖ := norm_sub_le _ _
          _ ≤ M₀ + M₀ := add_le_add h1 h2
          _ = 2 * M₀ := by ring
      have hb : (S / 2) ^ A ≤ ‖a - b‖ ^ (A * k) := by
        have hlt : S / 2 < hh := lt_of_not_ge hle
        have hrp : (S / 2) ^ A < hh ^ A := Real.rpow_lt_rpow hS2.le hlt hApos
        calc (S / 2) ^ A ≤ hh ^ A := le_of_lt hrp
          _ = ‖a - b‖ ^ (A * k) := hhA
      calc ‖ψ' t‖ ≤ 2 * M₀ := hcrude
        _ = 2 * M₀ / (S / 2) ^ A * (S / 2) ^ A := (div_mul_cancel₀ (2 * M₀) hSpow.ne').symm
        _ ≤ C₀ * ‖a - b‖ ^ (A * k) := by
            rw [hC₀def]
            exact mul_le_mul (le_max_right _ _) hb hSpow.le hC₀nn


end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.Model =====
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

/-! ## The inhabitant -/

/-- **The delivered inhabitant of `ProfileData α`**, with its defining data recorded. -/
structure Inhabitant (α : NNReal) where
  /-- the profile/modulation data -/
  P : Work.ConstructionInstance.ProfileData α
  /-- the perturbation is zero -/
  hg : P.g = (fun _ _ => (0 : ℝ))
  /-- the blow-up time is `2` -/
  hT : P.T = 2
  /-- the rate constant is `1/2` -/
  hK : P.K = 1 / 2
  /-- the cut-off parameter is `4^{1/p}+1` -/
  hL : P.L = (4 : ℝ) ^ (1 / Work.ConstructionInstance.profExp α) + 1
  /-- the vorticity box is `20p` -/
  hM : P.M = 20 * Work.ConstructionInstance.profExp α
  /-- the `∂ₜ` box is `10p` -/
  hM₁ : P.M₁ = 10 * Work.ConstructionInstance.profExp α
  /-- the modulation is the affine function `1 - t/2` -/
  hlam : ∀ t : ℝ, P.lam t = 1 - t / 2

theorem inhabitant_exists {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    Nonempty (Inhabitant α) := by
  obtain ⟨D, hg, hT, hM, hM₁, hK, _hCg, _hCg', hL, hlam⟩ :=
    Work.ConstructionInstance.profileData_inhabited hα hα13
  exact ⟨D, hg, hT, hK, hL, hM, hM₁, hlam⟩

/-- The model data is a `ProfileData` with the recorded data (this is `IsModelData`). -/
theorem inhabitant_isModelData {α : NNReal} (I : Inhabitant α) :
    IsModelData I.P :=
  ⟨I.hT, I.hg, funext I.hlam, I.hL, I.hM, I.hM₁⟩

/-! ## `T` is forced

The delivered interface's own modulation fields force `T = 2` (`ProfileData_T_eq_two`), so the
`T = 2` conjunct of `IsModelData` is *not* a choice: it is the only value a `ProfileData` admits.
The paper's normalisation `T* = 1` is therefore excluded by the interface (see `NOTES.md` §4(a')). -/



/-! ## The rate of the model modulation -/

/-- The model modulation is the affine function `1 - t/2` everywhere, so its derivative is the
constant `-(1/2)`: the *rate* `κ = -λ̄'` of the design is `1/2`. -/
theorem model_deriv_lam {α : NNReal} (I : Inhabitant α) :
    ∀ t : ℝ, deriv I.P.lam t = -(1 / 2) := by
  intro t
  rw [show I.P.lam = fun s : ℝ => 1 - s / 2 from funext I.hlam]
  have h : HasDerivAt (fun s : ℝ => 1 - s / 2) (-(1 / 2)) t := by
    simpa using ((hasDerivAt_id t).div_const 2).const_sub 1
  exact h.deriv

/-- The model modulation's derivative in the design's (paper dilated-time) normalisation:
`-λ̄' = 1/2` at `t = 1`.  **This is *not* the rate entering the physical profile equation** — that
one is `2·(-λ̄')` (see the module header and `model_rate_physical`), and it equals `κ* = 1`. -/
theorem model_rate {α : NNReal} (I : Inhabitant α) : -(deriv I.P.lam 1) = 1 / 2 := by
  rw [model_deriv_lam I 1]; norm_num

/-- The reference rate of the paper's normalisation (`μ = 0`): `κ* = 1`. -/
theorem kappaStar_zero : Work.Stability.kappaStar 0 = 1 := by
  rw [Work.Stability.kappaStar_eq]; norm_num


/-- The design's normalisation `κ = -λ̄'` differs from the reference rate `κ* = 1` at the inhabitant.

**This is a discrepancy of conventions, not of mathematics**: `-λ̄'` is the rate in the paper's
dilated time, while the *physical* rate entering the delivered residual R1's profile equation is
`2·(-λ̄') = κ*` (`model_rate_physical_eq_reference`).  It is recorded here only so that the
`1/2`-dilation trap of `Work.Stability.Defs` is visible where the reader meets the inhabitant. -/
theorem model_rate_ne_reference {α : NNReal} (I : Inhabitant α) :
    -(deriv I.P.lam 1) ≠ Work.Stability.kappaStar 0 := by
  rw [model_rate I, kappaStar_zero]; norm_num

/-! ## The constant-rate rescaled vorticity equation -/



/-! ## The rigidity of the model profile -/




/-! ## The audited rate of the inhabitant (the factor `2` of the time dilation) -/



end Work.CoreResiduals
end
end
-- ===== merged: Submission.Work.CoreResiduals.VorticityEquation =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals.VorticityEquation



end Work.CoreResiduals.VorticityEquation
end
end
-- ===== merged: Submission.Work.CoreResiduals.solVort_BSAdmissibleStrip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- The model data satisfies the strip admissibility bundle of `Work.CoreResiduals.BSAdmissibleStrip`, for every strip with S < T. Each conjunct is a claim about the explicit field solVort P: solVort_supp gives the support, solVort_bdd together with the lower bound on the modulation gives the uniform bound, the uniform x-Hölder regularity is the dilation computation of solVort_holder (the constant is the datum constant times a power of the modulation, bounded below on the strip), solVort_timeHolder gives the time-Hölder regularity on window S which contains Icc 0 S, and the measurability comes from solVort_integrable. -/
theorem solVort_BSAdmissibleStrip {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {S : ℝ} (hS : 0 < S) (hST : S < P.T) :
    Work.CoreResiduals.BSAdmissibleStrip α (Work.ConstructionInstance.solVort P) P.R S := by
  have hp : 0 < (P.T - S) / 2 := by linarith
  -- the strip is contained in the half-window where the modulation data lives
  have hsub : ∀ t ∈ Set.Icc (0 : ℝ) S, t ∈ Work.ConstructionInstance.preWindow P.T :=
    fun t ht => ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hST⟩
  -- spatial Hölder regularity with a uniform constant
  obtain ⟨H, hH⟩ := Work.CoreResiduals.solVort_holder_strip P hS hST
  -- time-Hölder regularity with a uniform constant
  obtain ⟨N, hN0, hN⟩ :=
    Work.ConstructionInstance.solVort_timeHolder_Icc P S ⟨hS, hST⟩
  refine ⟨?_, ?_, ?_, ⟨H, hH⟩, ⟨N, ?_⟩, ?_⟩
  · linarith [P.hL, P.hRbig]
  · intro t _ht y hy
    exact Work.ConstructionInstance.solVort_supp P t y hy
  · refine ⟨P.M / ((P.T - S) / 2), fun t ht y => ?_⟩
    have hδle : (P.T - S) / 2 ≤ P.lam t := by
      have h1 := P.hlam_low t ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
      linarith [ht.2]
    exact le_trans (Work.ConstructionInstance.solVort_norm_le P (hsub t ht) y)
      (div_le_div_of_nonneg_left P.hM hp hδle)
  · intro y t ht t' ht'
    by_cases hy : y ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) P.R
    · exact hN y hy t ht t' ht'
    · have h0 : Work.ConstructionInstance.solVort P y t = 0 := by
        by_contra hne
        exact hy (Work.ConstructionInstance.solVort_supp P t y hne)
      have h0' : Work.ConstructionInstance.solVort P y t' = 0 := by
        by_contra hne
        exact hy (Work.ConstructionInstance.solVort_supp P t' y hne)
      rw [h0, h0', sub_zero, norm_zero]
      exact mul_nonneg hN0 (Real.rpow_nonneg (abs_nonneg _) _)
  · intro t ht
    exact (Work.ConstructionInstance.solVort_integrable P t (hsub t ht)).aestronglyMeasurable

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.CoreResiduals.solVort_holder_of_lam_ge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- Uniform `α`-Hölder regularity of the slices wherever the modulation is bounded below: for every `δ > 0` a single constant `H` works for every `t : ℝ` with `δ ≤ P.lam t`. No time interval is mentioned (so this also covers times `t < 0` of the half-window, where the strip lemma `solVort_holder_strip` cannot be applied); it is its quantitative strengthening, obtained by taking `δ = (T-S)/2` there via `ProfileData.hlam_low`.

Template: `Submission/Work/CoreResiduals/solVort_holder_strip.lean` proves exactly this with `hδle : δ ≤ P.lam t` derived from `hlam_low` and `t ∈ Icc 0 S`; replace that derivation by the hypothesis. Everything else is verbatim: the dilation factor `b = (P.lam t)⁻¹ ^ (1 / profExp α)` with `b ^ profExp α = (P.lam t)⁻¹`; `b ≤ bmax` with `bmax = (δ⁻¹) ^ (1 / profExp α)` (`Real.rpow_le_rpow` + `inv_le_inv₀ hlt hδ`); the dilation identity `solVort P x t = (P.lam t)⁻¹ • (Work.Stability.cutFactor P.L x • Work.ConstructionInstance.omegaS (profExp α) P.g (b • x))` (`solVort_holder_rho_smul`, `_theta_smul`, `_eTheta_smul`, `omegaS_apply'`, `omegaSz_apply`); the global datum regularity `holder_omegaS_of_data`; the datum bound `omegaS_norm_le` with `MA = 20 * profExp α + P.Cg`; and the calculus lemmas `holderWith_comp_smul`, `holderWith_smul_of_bounded_lipschitz` (`Mc = 1`, `Kφ` from `cutFactor_lipschitz`) and `holderWith_le_const` of that module. The constant is `H := Hcut * ↑⟨δ⁻¹, _⟩` with `Hcut := 1 * (C₀ * Real.toNNReal (bmax ^ (α:ℝ))) + MA * max (Kφ:ℝ) 2`, where `C₀` is the constant from `holder_omegaS_of_data`; the last step is `HolderWith.smul (P.lam t)⁻¹` plus `‖(P.lam t)⁻¹‖₊ ≤ δ⁻¹` (`Real.nnnorm_of_nonneg`, `inv_le_inv₀ hlt hδ`). -/
theorem solVort_holder_of_lam_ge {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ H : NNReal, ∀ t : ℝ, δ ≤ P.lam t →
      HolderWith H α (fun x : Work.CoreResiduals.R3 => Work.ConstructionInstance.solVort P x t) := by
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos P.hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]; linarith [P.hα13]
  have hα1 : α ≤ 1 := by
    rw [← NNReal.coe_le_coe]; push_cast; linarith [P.hα13]
  -- a *fixed* Hölder constant for the self-similar datum
  obtain ⟨C₀, hC₀⟩ : Holder α
      (Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g) :=
    Work.ConstructionInstance.holder_omegaS_of_data P.hα P.hα13 P.hCv P.hLg P.hLθ
      P.hvt P.hquad0 P.hquad P.hvan P.hzk P.hzth
      (ContDiffOn.of_le P.hsmooth (by simp))
  -- the Lipschitz constant of the cut-off factor
  obtain ⟨Kφ, hKφ⟩ := Work.Stability.cutFactor_lipschitz P.hL
  -- the uniform dilation factor produced by the lower bound `δ ≤ λ̄(t)`
  let bmax : ℝ := (δ⁻¹) ^ (1 / Work.ConstructionInstance.profExp α)
  have hbmax0 : 0 ≤ bmax := Real.rpow_nonneg (inv_nonneg.mpr hδ.le) _
  let CAdil : NNReal := C₀ * Real.toNNReal (bmax ^ (α : ℝ))
  let MA : ℝ := 20 * Work.ConstructionInstance.profExp α + P.Cg
  have hMAdef : MA = 20 * Work.ConstructionInstance.profExp α + P.Cg := rfl
  have hMA0 : 0 ≤ MA := by rw [hMAdef]; linarith [hp.le, P.hCg]
  let Hcut : NNReal := ⟨1 * (CAdil : ℝ) + MA * max (Kφ : ℝ) (2 * 1),
    add_nonneg (by norm_num)
      (mul_nonneg hMA0 (le_trans (by linarith) (le_max_right _ _)))⟩
  let δinv : NNReal := ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩
  refine ⟨Hcut * δinv, fun t hδle => ?_⟩
  have hlt : 0 < P.lam t := lt_of_lt_of_le hδ hδle
  -- the dilation factor `b = λ̄(t)^{-1/p}`, uniformly bounded by `bmax`
  let b : ℝ := (P.lam t)⁻¹ ^ (1 / Work.ConstructionInstance.profExp α)
  have hb : 0 < b := Real.rpow_pos_of_pos (inv_pos.mpr hlt) _
  have hb_eq : b = (P.lam t)⁻¹ ^ (1 / Work.ConstructionInstance.profExp α) := rfl
  have hbmax_eq : bmax = (δ⁻¹) ^ (1 / Work.ConstructionInstance.profExp α) := rfl
  have hbp : b ^ Work.ConstructionInstance.profExp α = (P.lam t)⁻¹ := by
    rw [hb_eq, ← Real.rpow_mul (inv_nonneg.mpr hlt.le)
        (1 / Work.ConstructionInstance.profExp α) (Work.ConstructionInstance.profExp α),
      div_mul_cancel₀ 1 (ne_of_gt hp), Real.rpow_one]
  have hb_le_bmax : b ≤ bmax := by
    rw [hb_eq, hbmax_eq]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hlt.le)
      ((inv_le_inv₀ hlt hδ).mpr hδle) (by positivity)
  have hbα : b ^ (α : ℝ) ≤ bmax ^ (α : ℝ) :=
    Real.rpow_le_rpow hb.le hb_le_bmax α.coe_nonneg
  -- the dilation identity for the cylindrical coordinates
  have hz : ∀ x : Work.LWP.R3,
      Work.Cyl.rho (b • x) ^ Work.ConstructionInstance.profExp α
        = Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / P.lam t := by
    intro x
    rw [Work.ConstructionInstance.solVort_holder_rho_smul hb.le,
      Real.mul_rpow hb.le (Work.Cyl.rho_nonneg x), hbp, div_eq_mul_inv, mul_comm ((P.lam t)⁻¹)]
  have hω : ∀ x : Work.LWP.R3,
      Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)
        = Work.ConstructionInstance.omegaSz (Work.ConstructionInstance.profExp α) P.g
            (Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / P.lam t) x := by
    intro x
    rw [Work.ConstructionInstance.omegaS_apply', Work.ConstructionInstance.omegaSz_apply,
      Work.ConstructionInstance.solVort_holder_theta_smul hb x,
      Work.ConstructionInstance.solVort_holder_eTheta_smul hb x, hz x]
  have hid : ∀ x : Work.LWP.R3, Work.ConstructionInstance.solVort P x t
      = (P.lam t)⁻¹ • (Work.Stability.cutFactor P.L x •
          Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) := by
    intro x
    rw [Work.ConstructionInstance.solVort_apply, Work.Stability.cutFactor_apply, hω x]
  -- the dilated datum is `α`-Hölder with the uniform constant `CAdil`
  have hH : HolderWith CAdil α (fun x : Work.LWP.R3 =>
      Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) := by
    have h1 : HolderWith (C₀ * Real.toNNReal (b ^ (α : ℝ))) α
        (fun x : Work.LWP.R3 =>
          Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) :=
      holderWith_comp_smul hC₀ hb.le
    refine holderWith_le_const h1 ?_
    have hCAdil : CAdil = C₀ * Real.toNNReal (bmax ^ (α : ℝ)) := rfl
    rw [hCAdil]
    exact mul_le_mul_of_nonneg_left (Real.toNNReal_le_toNNReal hbα)
      (zero_le : (0 : NNReal) ≤ C₀)
  -- the dilated datum is uniformly bounded by `MA`
  have hbd : ∀ x : Work.LWP.R3,
      ‖Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)‖ ≤ MA := by
    intro x
    have hMθ : ∀ θ ∈ Work.Spaces.Iθ, 20 * Work.ConstructionInstance.profExp α
        * Work.ConstructionInstance.Gamma (Work.ConstructionInstance.profExp α / 3) θ + P.Cg
          ≤ MA := by
      intro θ hθ
      have hG : Work.ConstructionInstance.Gamma (Work.ConstructionInstance.profExp α / 3) θ ≤ 1 :=
        Work.ConstructionInstance.Gamma_le_one (by positivity) hθ
      have hMA : MA = 20 * Work.ConstructionInstance.profExp α + P.Cg := rfl
      rw [hMA]; nlinarith [hG, hp.le, P.hCg]
    exact Work.ConstructionInstance.omegaS_norm_le hp hp1 (Work.ConstructionInstance.bdd_g P)
      P.hCg hMθ (b • x)
  -- multiplying by the bounded Lipschitz cut-off keeps the constant uniform
  have hcut : HolderWith Hcut α (fun x : Work.LWP.R3 =>
      Work.Stability.cutFactor P.L x •
        Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) := by
    refine holderWith_smul_of_bounded_lipschitz hα1 (K := Kφ) (Mc := 1) (MA := MA)
      (C := CAdil) (by norm_num) ?_ hKφ hMA0 hbd hH
    intro x
    rw [Work.Stability.cutFactor_apply, abs_of_nonneg (Work.Stability.chi_nonneg _)]
    exact Work.Stability.chi_le_one _
  have hslice : HolderWith (Hcut * ‖(P.lam t)⁻¹‖₊) α
      ((P.lam t)⁻¹ • (fun x : Work.LWP.R3 => Work.Stability.cutFactor P.L x •
        Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x))) :=
    HolderWith.smul (P.lam t)⁻¹ hcut
  have hslice' : HolderWith (Hcut * ‖(P.lam t)⁻¹‖₊) α
      (fun x : Work.LWP.R3 => Work.ConstructionInstance.solVort P x t) := by
    rw [funext hid]
    exact hslice
  -- the scalar `λ̄(t)^{-1}` is uniformly bounded by `δ^{-1}`
  refine holderWith_le_const hslice' ?_
  refine mul_le_mul_of_nonneg_left ?_ (zero_le : (0 : NNReal) ≤ Hcut)
  rw [Real.nnnorm_of_nonneg (inv_nonneg.mpr hlt.le)]
  exact (inv_le_inv₀ hlt hδ).mpr hδle

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.CoreResiduals.solVort_timeDerivStrip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- The constructed vorticity satisfies the time-regularity bundle of the space-time Schauder
estimate on every strip: `Work.CoreResiduals.TimeDerivStrip (solVort P) S` for `0 < S < P.T`.

The three conjuncts are: `t`-differentiability of each slice on `Icc 0 S`
(`Work.ConstructionInstance.hasDerivAt_selfSimVort_slice`, applicable since
`Icc 0 S ⊆ preWindow P.T`), a uniform bound on `∂ₜω` there (`solVort_bddDt` together with the
lower bound `λ̄ ≥ (T-S)/2` from `hlam_low`), and the ae-strong-measurability of the derivative
slices (`Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice`, from the differentiability
in `t` and the measurability of the slices; the companion module
`Work.CoreResiduals.solVort_timeDeriv_aesm_preWindow` supplies it on `preWindow P.T`). -/
theorem solVort_timeDerivStrip {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {S : ℝ} (hS : 0 < S) (hST : S < P.T) :
    Work.CoreResiduals.TimeDerivStrip (Work.ConstructionInstance.solVort P) S := by
  have hδpos : 0 < (P.T - S) / 2 := by linarith
  have hδ2pos : 0 < ((P.T - S) / 2) ^ 2 := by positivity
  -- the strip `Icc 0 S` is contained in the half-window where the modulation data lives
  have hsub : ∀ t ∈ Set.Icc (0 : ℝ) S, t ∈ Work.ConstructionInstance.preWindow P.T :=
    fun t ht => ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hST⟩
  refine ⟨?_, ⟨P.M₁ / ((P.T - S) / 2) ^ 2, ?_⟩, ?_⟩
  · -- `t`-differentiability of each slice on the strip
    intro t ht y
    have hd := Work.ConstructionInstance.hasDerivAt_selfSimVort_slice
      (p := Work.ConstructionInstance.profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) P.hgdiff P.hlam P.hlamdif (hsub t ht) y
    simpa only [Work.ConstructionInstance.solVort] using hd
  · -- uniform bound on `∂ₜω` on the strip: `λ̄ ≥ (T-S)/2` there
    intro t ht y
    have htpre := hsub t ht
    have hδle : (P.T - S) / 2 ≤ P.lam t := by
      have h1 := P.hlam_low t ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
      linarith [ht.2]
    have hlt : 0 < P.lam t := P.hlam t htpre
    have hm2 : ((P.T - S) / 2) ^ 2 ≤ (P.lam t) ^ 2 := by
      have h := mul_le_mul hδle hδle hδpos.le hlt.le
      simpa only [pow_two] using h
    have h1 : ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t‖
        ≤ P.M₁ / (P.lam t) ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (P.lam t) ^ 2), mul_comm]
      exact Work.ConstructionInstance.solVort_bddDt P t htpre y
    have h2 : P.M₁ / (P.lam t) ^ 2 ≤ P.M₁ / ((P.T - S) / 2) ^ 2 :=
      div_le_div_of_nonneg_left P.hM₁ hδ2pos hm2
    linarith
  · -- ae-strong-measurability of the derivative slices
    intro t ht
    exact solVort_timeDeriv_aesm_preWindow P t (hsub t ht)

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.CoreResiduals.solVort_timeDeriv_lipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- The `∂ₜ`-slices of the constructed vorticity are locally Lipschitz in `t`, uniformly in `x`,
i.e. `Work.CoreResiduals.TimeDerivLocallyLipschitz (solVort P) P.T`.

Near a time `t₀` of the half-window one takes a small interval whose closure stays in `preWindow P.T`
and on which `λ̄` is bounded below by some `m > 0` (continuity of `λ̄`); the second-order slice
identity `Work.ConstructionInstance.timeDeriv_timeDeriv_selfSimVort` then gives, for every `y`, the
`t`-differentiability of `s ↦ ∂ₜω(y,s)` there together with the box
`‖∂ₜ²ω(y,t)‖ ≤ Λ(m)` (an explicit function of the second-order data `Cg''` of the profile and `K₂`
of the modulation), and the mean value argument turns the box into the asserted Lipschitz bound.
The hypotheses are the second-order profile/modulation data of
`Work.ConstructionInstance.selfSimTimeHolderDeriv_of_secondOrderData`. -/
theorem solVort_timeDeriv_lipschitz {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) {Cg'' K₂ : ℝ}
    (hgdiff2 : ∀ z θ : ℝ, 0 < z → HasDerivAt
      (fun z' : ℝ => Work.Spaces.pz (Work.ConstructionInstance.profile
        (Work.ConstructionInstance.profExp α) P.g) z' θ)
      (Work.Spaces.pz (Work.Spaces.pz (Work.ConstructionInstance.profile
        (Work.ConstructionInstance.profExp α) P.g)) z θ) z)
    (hg3 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (Work.ConstructionInstance.profile
        (Work.ConstructionInstance.profExp α) P.g)) z θ| ≤ Cg'')
    (hlamdif2 : ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      HasDerivAt (deriv P.lam) (deriv (deriv P.lam) t) t)
    (hlamd2 : ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      |deriv (deriv P.lam) t| ≤ K₂) :
    Work.CoreResiduals.TimeDerivLocallyLipschitz
      (Work.ConstructionInstance.solVort P) P.T := by
  intro t₀ ht₀
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos P.hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]; linarith [P.hα13]
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ P.Cg := P.hCg
  have hCg' : 0 ≤ P.Cg' := by simpa using P.hg2 0 0 le_rfl hI0
  have hCg'' : 0 ≤ Cg'' := by simpa using hg3 0 0 le_rfl hI0
  have hK₂ : 0 ≤ K₂ := le_trans (abs_nonneg _) (hlamd2 0 ⟨by norm_num, P.hT⟩)
  -- a small interval around `t₀` whose closure stays in the half-window, on which `λ̄ ≥ m > 0`
  obtain ⟨ε, hεpos, hsub, m, hmpos, hmle⟩ :=
    Work.CoreResiduals.exists_eps_min_lam (T := P.T) (lam := P.lam) P.hlam P.hlamdif ht₀
  -- the second-order box
  set Λ : ℝ := K₂ * (20 * Work.ConstructionInstance.profExp α + P.Cg + P.Cg') / m ^ 2
      + P.K ^ 2 * (2 * (5 * Work.ConstructionInstance.profExp α + P.Cg') + Cg'') / m ^ 3
      + 2 * P.K ^ 2 * (20 * Work.ConstructionInstance.profExp α + P.Cg + P.Cg') / m ^ 3
    with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    have h1 : 0 ≤ K₂ * (20 * Work.ConstructionInstance.profExp α + P.Cg + P.Cg') / m ^ 2 :=
      div_nonneg (mul_nonneg hK₂ (by linarith)) (by positivity)
    have h2 : 0 ≤ P.K ^ 2 * (2 * (5 * Work.ConstructionInstance.profExp α + P.Cg') + Cg'') / m ^ 3 :=
      div_nonneg (mul_nonneg (sq_nonneg P.K) (by linarith)) (by positivity)
    have h3 : 0 ≤ 2 * P.K ^ 2 * (20 * Work.ConstructionInstance.profExp α + P.Cg + P.Cg') / m ^ 3 :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
    linarith
  refine ⟨ε, hεpos, Λ, ?_⟩
  intro t ht t' ht' y
  -- the second-order slice identity with its box, on the closed interval
  have hmem : ∀ s ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y u)
        (FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv
          (Work.ConstructionInstance.solVort P)) y s) s
      ∧ ‖FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv
          (Work.ConstructionInstance.solVort P)) y s‖ ≤ Λ := by
    intro s hs
    have hspre : s ∈ Work.ConstructionInstance.preWindow P.T := hsub hs
    have h := Work.ConstructionInstance.timeDeriv_timeDeriv_selfSimVort
      (p := Work.ConstructionInstance.profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) (m := m) (Cg := P.Cg) (Cg' := P.Cg') (Cg'' := Cg'') (K := P.K) (K₂ := K₂)
      hp hp1 P.hvt.1 (Work.ConstructionInstance.bdd_g P) P.hg2 hg3 P.hgdiff hgdiff2 P.hlam
      P.hlamdif hlamdif2 P.hlamd hlamd2 P.hK hK₂ hspre hmpos (hmle s hs) y
    refine ⟨h.1, ?_⟩
    rw [hΛdef]
    exact h.2
  -- the mean value argument
  exact Work.CoreResiduals.norm_timeDeriv_sub_le_of_secondDeriv_bound
    (a := t₀ - ε) (b := t₀ + ε) (C := Λ)
    (fun y z hz => (hmem z hz).1) (fun y z hz => (hmem z hz).2)
    t ht t' ht' y

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow12 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-- `SmoothOpen` is stable under multiplication by a scalar (the `SmoothOpen`-analogue of
`ContDiffOn.const_smul`). -/
private theorem smoothOpen_const_mul_prv {F : ℝ → ℝ → ℝ} (c : ℝ)
    (h : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * F z θ) :=
  h.const_smul c


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow13 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row8 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row9 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Physical.RegPkg.fakeLower_of_Fstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.RegPkg

/-- **The self-similar half plane is covered by physical space.**  For `B > 0`, `z > 0` and
`0 ≤ θ < π/2`, the point `x = ρ·(cos θ, 0, sin θ)` with `ρ = (B z)^{1/p} > 0` satisfies
`radial x ≠ 0` (so that `e_θ(x)` is a unit vector), `θ(x) = θ` (the polar angle of `x` is exactly
`θ`), and `ρ(x)^p/B = z` (the self-similar variable `ρ(x)^p` rescaled by the clock is exactly
`z`). -/
theorem polarPoint_coords {p B z θ : ℝ} (hp : 0 < p) (hB : 0 < B) (hz : 0 < z)
    (hθ0 : 0 ≤ θ) (hθlt : θ < Real.pi / 2) :
    ∃ x : Work.Cyl.R3, Work.Cyl.radial x ≠ 0 ∧ Work.Cyl.theta x = θ ∧
      Work.Cyl.rho x ^ p / B = z := by
  have hBz : 0 < B * z := mul_pos hB hz
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθlt⟩
  have hρ : 0 < (B * z) ^ (1 / p) := Real.rpow_pos_of_pos hBz _
  have hρp : ((B * z) ^ (1 / p)) ^ p = B * z := by
    rw [← Real.rpow_mul hBz.le, one_div, inv_mul_cancel₀ (ne_of_gt hp), Real.rpow_one]
  let x : Work.Cyl.R3 := !₂[(B * z) ^ (1 / p) * Real.cos θ, 0, (B * z) ^ (1 / p) * Real.sin θ]
  have hx0 : x 0 = (B * z) ^ (1 / p) * Real.cos θ := by simp [x]
  have hx1 : x 1 = 0 := by simp [x]
  have hx2 : x 2 = (B * z) ^ (1 / p) * Real.sin θ := by simp [x]
  have hradSq : Work.Cyl.radSq x = ((B * z) ^ (1 / p) * Real.cos θ) ^ 2 := by
    simp [Work.Cyl.radSq, hx0, hx1]
  have haxial : Work.Cyl.axial x = (B * z) ^ (1 / p) * Real.sin θ := by
    simp [Work.Cyl.axial, hx2]
  have hradial : Work.Cyl.radial x = (B * z) ^ (1 / p) * Real.cos θ := by
    rw [Work.Cyl.radial, hradSq, Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hρ hcos)]
  refine ⟨x, ne_of_gt (by rw [hradial]; exact mul_pos hρ hcos), ?_, ?_⟩
  · rw [Work.Cyl.theta, hradial, haxial]
    have htan : (B * z) ^ (1 / p) * Real.sin θ / ((B * z) ^ (1 / p) * Real.cos θ)
        = Real.tan θ := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    rw [htan, Real.arctan_tan (by linarith [Real.pi_pos]) hθlt]
  · rw [Work.Cyl.rho, hradSq, haxial]
    have hsq : ((B * z) ^ (1 / p) * Real.cos θ) ^ 2
        + ((B * z) ^ (1 / p) * Real.sin θ) ^ 2 = ((B * z) ^ (1 / p)) ^ 2 := by
      rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hρ, hρp,
      mul_div_cancel_left₀ z (ne_of_gt hB)]

/-- **A pointwise lower bound for the physical vorticity, from a pointwise lower bound on the
profile `F = F_* + g`.**  If at every fake time `τ ≥ 0` the full profile is bounded below in
modulus by `3α/100` at some point `z > 0`, `θ ∈ Iθ`, `θ < π/2` of the self-similar half plane,
then the physical vorticity is bounded below in modulus by `(3α/100)/A(τ)` at a point depending
on `τ`. -/
theorem fakeLower_of_Fstar {α : ℝ} (hα : 0 < α) {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hApos : ∀ τ : ℝ, 0 ≤ τ → 0 < A τ) (hBpos : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ)
    (hF : ∀ τ : ℝ, 0 ≤ τ → ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, θ ∈ Work.Spaces.Iθ ∧ θ < Real.pi / 2 ∧
      3 * α / 100 ≤ |Work.Construction.Fstar (3 * α) z θ + g z θ τ|) :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ, 0 ≤ τ → ∃ x : Work.FTS.Regularity.R3,
      c / A τ ≤ ‖Work.FTS.Regularity.physVort α A B g x τ‖ := by
  refine ⟨3 * α / 100, by linarith, ?_⟩
  intro τ hτ
  obtain ⟨z, hz, θ, hθmem, hθlt, hbound⟩ := hF τ hτ
  have hθ0 : 0 ≤ θ := hθmem.1
  have hp : 0 < Work.FTS.Regularity.pExp α := by
    rw [Work.FTS.Regularity.pExp]; linarith
  obtain ⟨x, hrne, hth, hrz⟩ :=
    polarPoint_coords (p := Work.FTS.Regularity.pExp α) (B := B τ) hp (hBpos τ hτ) hz hθ0 hθlt
  refine ⟨x, ?_⟩
  have hA : 0 < A τ := hApos τ hτ
  have hprof : Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
      (Work.FTS.Regularity.gSlice g τ) (Work.Cyl.rho x ^ Work.FTS.Regularity.pExp α / B τ)
      (Work.Cyl.theta x) = Work.Construction.Fstar (3 * α) z θ + g z θ τ := by
    rw [hth, hrz, Work.ConstructionInstance.profile_of_nonneg hθ0]
    rfl
  have hnorm : ‖Work.FTS.Regularity.physVort α A B g x τ‖
      = (A τ)⁻¹ * |Work.Construction.Fstar (3 * α) z θ + g z θ τ| := by
    rw [Work.FTS.Regularity.physVort, Work.ConstructionInstance.omegaSz,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hA), hprof, Work.Cyl.norm_eTheta x hrne, mul_one]
  rw [hnorm, show (3 * α / 100) / A τ = (A τ)⁻¹ * (3 * α / 100) by ring]
  exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hA.le)

end Work.FTS.Physical.RegPkg
end
-- ===== merged: Submission.Work.FTS.Physical.RegPkg.profFull_ge_of_small =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `profFull_ge_of_small` — the full profile is large somewhere

For `0 < α`, `3α ≤ 1` and a perturbation `g` that is uniformly small,
`|g z θ τ| ≤ 3α/200` on `[0,∞) × [0,π/2]`, there is a point `(z,θ)` with `z > 0`,
`θ ∈ [0,π/2]`, `θ < π/2` at which `|F_*(3α) + g| ≥ 3α/100`.

The witness is again `(z,θ) = (1, π/4)`:

* `F_{*,rad}(1) = 2·1/(1+1)² = 1/2` is the maximum of `F_{*,rad}`;
* `Γ(π/4) = (sin(π/4)·cos²(π/4))^α = (√2/4)^α ≥ √2/4 ≥ 3/10` (the base `√2/4` lies in
  `(0,1]` and `α ≤ 1/3 ≤ 1`, so the exponent `α` is *smaller* than `1`);
  note the exponent here is `(3α)/3 = α`, since the profile `F_*(3α)` carries `Γ(3α)`;
* `c(3α) ≤ 10` (`Work.Spaces.c_bounds`), hence `Γ(π/4)/c(3α) ≥ (3/10)/10 = 3/100`.

Therefore `F_*(3α)(1,π/4) ≥ 3α · (3/100) · (1/2) = 9α/200`, so at this point
`F_*(3α)(1,π/4) + g(1,π/4,τ) ≥ 9α/200 - 3α/200 = 3α/100 > 0`, giving the claim.
-/

namespace Work.FTS.Physical.RegPkg

open scoped Real Topology

/-- `Γ(3α)(π/4) = (sin(π/4)·cos²(π/4))^α = (√2/4)^α ≥ √2/4 ≥ 3/10` (the exponent is
`(3α)/3 = α ≤ 1/3 ≤ 1`, and `√2/4 ∈ (0,1]`). -/
private lemma Gam_three_pi_div_four_ge {α : ℝ} (hα1 : 3 * α ≤ 1) :
    (3 : ℝ) / 10 ≤ Work.Spaces.Gam (3 * α) (Real.pi / 4) := by
  have hbase0 : (0 : ℝ) < √2 / 4 := by positivity
  have hbase1 : √2 / 4 ≤ 1 := by
    have h : √2 < 4 := by
      rw [Real.sqrt_lt' (show (0 : ℝ) < 4 by norm_num)]; norm_num
    linarith
  have hsqrt_ge : (3 : ℝ) / 10 ≤ √2 / 4 := by
    have h65 : (6 : ℝ) / 5 ≤ √2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    linarith
  have hsq : (√2 / 2) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hbase : Real.sin (Real.pi / 4) * Real.cos (Real.pi / 4) ^ 2 = √2 / 4 := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four, hsq]; ring
  have hGamEq : Work.Spaces.Gam (3 * α) (Real.pi / 4) = (√2 / 4) ^ α := by
    rw [Work.Spaces.Gam, hbase, show (3 * α) / 3 = α by ring]
  have hmono : (√2 / 4) ^ (1 : ℝ) ≤ (√2 / 4) ^ α :=
    Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1 (by linarith)
  rw [Real.rpow_one] at hmono
  rw [hGamEq]
  linarith

theorem profFull_ge_of_small {α : ℝ} (hα : 0 < α) (hα1 : 3 * α ≤ 1) {g : ℝ → ℝ → ℝ → ℝ}
    (hsmall : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |g z θ τ| ≤ 3 * α / 200) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, θ ∈ Work.Spaces.Iθ ∧ θ < Real.pi / 2 ∧
      3 * α / 100 ≤ |Work.Construction.Fstar (3 * α) z θ + g z θ τ| := by
  intro τ hτ
  have hα3pos : 0 < 3 * α := by linarith
  obtain ⟨_hc1, hc2⟩ := Work.Spaces.c_bounds (3 * α) hα3pos hα1
  have hcpos : 0 < Work.Spaces.c (3 * α) := by
    linarith [(Work.Spaces.c_bounds (3 * α) hα3pos hα1).1]
  have hΓ : (3 : ℝ) / 10 ≤ Work.Spaces.Gam (3 * α) (Real.pi / 4) :=
    Gam_three_pi_div_four_ge hα1
  -- `Γ(π/4)/c(3α) ≥ (3/10)/10 = 3/100`.
  have hratio : (3 : ℝ) / 100 ≤ Work.Spaces.Gam (3 * α) (Real.pi / 4) / Work.Spaces.c (3 * α) := by
    rw [le_div_iff₀ hcpos]
    nlinarith
  have hFhalf : Work.FM.Fstar (1 : ℝ) = 1 / 2 := by
    rw [Work.FM.Fstar]; norm_num
  -- `F_*(3α)(1, π/4) ≥ 3α · (3/100) · (1/2) = 9α/200`.
  have hF : 3 * α * ((3 : ℝ) / 200) ≤ Work.Construction.Fstar (3 * α) 1 (Real.pi / 4) := by
    rw [Work.Construction.Fstar, hFhalf]
    have h1 : (3 * α * ((3 : ℝ) / 100)) * (1 / 2)
        ≤ (3 * α * (Work.Spaces.Gam (3 * α) (Real.pi / 4) / Work.Spaces.c (3 * α))) * (1 / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hα3pos.le) (by norm_num)
    nlinarith [h1]
  have hgpt : -(3 * α / 200) ≤ g 1 (Real.pi / 4) τ := by
    have h := hsmall τ hτ 1 (by simp [Work.Spaces.Iz]) (Real.pi / 4)
      (by constructor <;> linarith [Real.pi_pos])
    rw [abs_le] at h
    linarith [h.1]
  refine ⟨1, one_pos, Real.pi / 4, ?_, ?_, ?_⟩
  · constructor <;> linarith [Real.pi_pos]
  · linarith [Real.pi_pos]
  · have hkey : 3 * α / 100
        ≤ Work.Construction.Fstar (3 * α) 1 (Real.pi / 4) + g 1 (Real.pi / 4) τ := by linarith
    exact le_trans hkey (le_abs_self _)

end Work.FTS.Physical.RegPkg
end
-- ===== merged: Submission.Work.FTS.PressureOn.VortWtAesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal ENNReal

namespace Work.FTS.PressureOn

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- **The perturbation slice is continuous on the closed quadrant.**  This is the Hölder estimate
of the `Jet` field of `RegPkg`, read as an `ε`-`δ` continuity statement. -/
theorem continuousOn_uncurry_gSlice {α S Ng : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hJet : Work.FTS.Regularity.Jet α S Ng g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 τ) (Set.Ici 0 ×ˢ Work.Spaces.Iθ) := by
  have hN0 : 0 ≤ Ng := hJet.1
  rw [Metric.continuousOn_iff]
  intro p hp ε hε
  by_cases hN : Ng = 0
  · refine ⟨1, one_pos, fun q hq _ => ?_⟩
    have hle := hJet.2.2 q.1 p.1 q.2 p.2 τ τ hq.1 hp.1 hq.2 hp.2 hτ hτ
    rw [hN, zero_mul] at hle
    have h0 : 0 ≤ g q.1 q.2 τ - g p.1 p.2 τ := by
      linarith [neg_abs_le (g q.1 q.2 τ - g p.1 p.2 τ), hle]
    rw [Real.dist_eq, abs_of_nonneg h0]
    linarith [le_abs_self (g q.1 q.2 τ - g p.1 p.2 τ), hle, hε]
  · have hNpos : 0 < Ng := lt_of_le_of_ne hN0 (Ne.symm hN)
    have h2α : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
    have hcoef : 0 < Ng * 2 ^ α := mul_pos hNpos h2α
    refine ⟨min 1 (((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2), lt_min one_pos
      (div_pos (Real.rpow_pos_of_pos (div_pos hε hcoef) _) (by norm_num)), fun q hq hpq => ?_⟩
    have hmax : max |q.1 - p.1| |q.2 - p.2| <
        min 1 (((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2) := by
      simpa only [Real.dist_eq, Prod.dist_eq] using hpq
    have hd1 : |q.1 - p.1| < min 1 (((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2) :=
      lt_of_le_of_lt (le_max_left _ _) hmax
    have hd2 : |q.2 - p.2| < min 1 (((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2) :=
      lt_of_le_of_lt (le_max_right _ _) hmax
    have hsum : |q.1 - p.1| + |q.2 - p.2| ≤ (ε / (Ng * 2 ^ α)) ^ (1 / α) := by
      have h1 : |q.1 - p.1| ≤ ((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2 :=
        le_of_lt (lt_of_lt_of_le hd1 (min_le_right _ _))
      have h2 : |q.2 - p.2| ≤ ((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2 :=
        le_of_lt (lt_of_lt_of_le hd2 (min_le_right _ _))
      linarith
    have hle := hJet.2.2 q.1 p.1 q.2 p.2 τ τ hq.1 hp.1 hq.2 hp.2 hτ hτ
    have hle0 : |g q.1 q.2 τ - g p.1 p.2 τ| ≤ Ng * (|q.1 - p.1| + |q.2 - p.2|) ^ α := by
      simpa using hle
    have hpow : (|q.1 - p.1| + |q.2 - p.2|) ^ α ≤ ε / (Ng * 2 ^ α) := by
      have h1 : ((ε / (Ng * 2 ^ α)) ^ (1 / α)) ^ α = ε / (Ng * 2 ^ α) := by
        rw [← Real.rpow_mul (le_of_lt (div_pos hε hcoef)), one_div, inv_mul_cancel₀,
          Real.rpow_one]
        positivity
      rw [← h1]
      exact Real.rpow_le_rpow (by positivity) hsum (le_of_lt hα)
    rw [Real.dist_eq]
    calc |g q.1 q.2 τ - g p.1 p.2 τ|
        ≤ Ng * (|q.1 - p.1| + |q.2 - p.2|) ^ α := hle0
      _ ≤ Ng * (ε / (Ng * 2 ^ α)) := by
          exact mul_le_mul_of_nonneg_left hpow hN0
      _ = ε / 2 ^ α := by field_simp
      _ < ε := by
          rw [div_lt_iff₀ h2α]
          have h2 : (1 : ℝ) < 2 ^ α := Real.one_lt_rpow one_lt_two hα
          nlinarith






end Work.FTS.PressureOn
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

/-- `Fam`, the type of families `(z,θ,τ) ↦ g z θ τ` (definitionally `Work.FTS.Galerkin.Fam`). -/
abbrev Fam := ℝ → ℝ → ℝ → ℝ

/-- The `τ`-slice of a family (definitionally `Work.FTS.Galerkin.slice`). -/
abbrev famSlice (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ := Work.FTS.Galerkin.slice g τ


/-! ## The extension `g̃` to negative fake time -/

/-- **THE EXTENSION `g̃` OF `g` TO NEGATIVE FAKE TIME** (design §4 preamble):

  `g̃ z θ τ = 0` if `z ≤ 0`; `g̃ z θ τ = g z θ 0 + τ·∂_τg(z,θ,0)` if `τ < 0`; `g̃ = g` otherwise.

The `z ≤ 0` test comes first, so `g̃` vanishes identically on the closed left half-plane
`{z ≤ 0}`; this is what makes the two axis clauses (`hquad0`, `hquad`) of `RegPkg'` true *by
definition* for `g̃`.  The `τ < 0` branch is the first-order Taylor jet of `g` at `τ = 0` (which is
the jet used in the `Jet α S Nd (∂_τ g)` field of the package), making `g̃` `C¹` across `τ = 0`
once `τ ↦ g z θ τ` is differentiable there. -/
noncomputable def extG (g : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ =>
    if z ≤ 0 then 0 else if τ < 0 then g z θ 0 + τ * deriv (fun s => g z θ s) 0 else g z θ τ

@[simp] theorem extG_of_nonpos {g : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ} (hz : z ≤ 0) :
    extG g z θ τ = 0 := by
  simp only [extG, if_pos hz]

@[simp] theorem extG_of_neg {g : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ} (hz : 0 < z) (hτ : τ < 0) :
    extG g z θ τ = g z θ 0 + τ * deriv (fun s => g z θ s) 0 := by
  simp only [extG, if_neg (not_le.mpr hz), if_pos hτ]

@[simp] theorem extG_of_pos {g : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ} (hz : 0 < z) (hτ : 0 ≤ τ) :
    extG g z θ τ = g z θ τ := by
  simp only [extG, if_neg (not_le.mpr hz), if_neg (not_lt.mpr hτ)]



/-! ## The corrected regularity package `RegPkg'` -/

/-- **THE CORRECTED REGULARITY PACKAGE `RegPkg'`**: `Work.FTS.Regularity.RegPkg` **verbatim**
except that the third clause of `htay` is the *Hölder* form of design correction 5,

  `|g z θ τ - g z θ' τ| ≤ K · z² · |θ - θ'|^α`,

instead of the false Lipschitz form `≤ K·z·|θ - θ'|`.  See the module docstring.

Every other field is the delivered one, field for field, so that all the downstream physical
transfer lemmas (`Work.FTS.Regularity.Slice`, `Time`, `Bundle`) can be re-run on `RegPkg'` by the
same arguments with `Basic.tay'`/`Basic.zmod'`/`Basic.thmod'` in place of `RegPkg.tay`/`zmod`/
`thmod`; only the composite Hölder transfer genuinely changes, and its re-proof is
`Consumer.gCompHolder'`. -/
structure RegPkg' (α : ℝ) (S : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop where
  /-- `0 < α` (the Hölder exponent of the challenge) -/
  hα : 0 < α
  /-- the paper's regime `α ≤ 1/3` -/
  hα13 : α ≤ 1 / 3
  /-- the fake-time strip is nonempty -/
  hS : 0 < S
  /-- the amplitude of the physical vorticity is positive on the strip -/
  hA : ∀ τ ∈ Set.Icc 0 S, 0 < A τ
  /-- the self-similar scaling is positive on the strip -/
  hB : ∀ τ ∈ Set.Icc 0 S, 0 < B τ
  /-- the amplitude is bounded above and below on the strip -/
  hAb : ∃ a₀ a₁ : ℝ, 0 < a₀ ∧ ∀ τ ∈ Set.Icc 0 S, a₀ ≤ A τ ∧ A τ ≤ a₁
  /-- the scaling is bounded above and below on the strip -/
  hBb : ∃ b₀ b₁ : ℝ, 0 < b₀ ∧ ∀ τ ∈ Set.Icc 0 S, b₀ ≤ B τ ∧ B τ ≤ b₁
  /-- the amplitude is differentiable on the strip, with its `deriv` as derivative -/
  hAdiff : ∀ τ ∈ Set.Icc 0 S, HasDerivAt A (deriv A τ) τ
  /-- the scaling is differentiable on the strip, with its `deriv` as derivative -/
  hBdiff : ∀ τ ∈ Set.Icc 0 S, HasDerivAt B (deriv B τ) τ
  /-- the derivative of the amplitude is bounded on the strip -/
  hAd : ∃ a₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv A τ| ≤ a₂
  /-- the derivative of the scaling is bounded on the strip -/
  hBd : ∃ b₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv B τ| ≤ b₂
  /-- the derivative of the amplitude is `α`-Hölder on the strip -/
  hAdh : ∃ a₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |deriv A τ - deriv A τ'| ≤ a₃ * |τ - τ'| ^ α
  /-- the derivative of the scaling is `α`-Hölder on the strip -/
  hBdh : ∃ b₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |deriv B τ - deriv B τ'| ≤ b₃ * |τ - τ'| ^ α
  /-- the perturbation vanishes on the two angular boundaries -/
  hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (gSlice g τ)
  /-- the perturbation vanishes at `z = 0` -/
  hquad0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, g 0 θ τ = 0
  /-- `∂_z g` vanishes at `z = 0` -/
  hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.pz (gSlice g τ) 0 θ = 0
  /-- the joint `α`-Hölder data of the perturbation -/
  hg : ∃ Ng : ℝ, Jet α S Ng g
  /-- the joint `α`-Hölder data of `∂_z g` -/
  hpz : ∃ Npz : ℝ, Jet α S Npz (fun z θ τ => Work.Spaces.pz (gSlice g τ) z θ)
  /-- the joint `α`-Hölder data of `∂_τ g` -/
  hgdoth : ∃ Nd : ℝ, Jet α S Nd (fun z θ τ => deriv (fun s => g z θ s) τ)
  /-- the uniform angular vanishing `|g| ≤ Cv·Γ(θ)` of the perturbation -/
  hvan : ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
    |g z θ τ| ≤ Cv * Gamma α θ
  /-- the quadratic vanishing of `g` at `z = 0`, with the near-origin `z`-Lipschitz bound and the
  **corrected (Hölder) angular bound** of design correction 5 -/
  htay : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K * z ^ 2) ∧
    (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
      |g z θ τ - g z' θ τ| ≤ K * max z z' * |z - z'|) ∧
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
      |g z θ τ - g z θ' τ| ≤ K * z ^ 2 * |θ - θ'| ^ α)
  /-- the full profile is compactly supported in the self-similar variable `z` -/
  hsupp : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z → profFull α g z θ τ = 0
  /-- the honest `ℋ⁴`-membership of every slice -/
  hH4 : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.HkMem (pExp α) 4 (gSlice g τ)
  /-- the joint `C¹` smoothness of `(z,τ) ↦ g z θ τ` at every fixed angle `θ ∈ Iθ` -/
  hcont : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1
    (fun q : ℝ × ℝ => g q.1 θ q.2) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1))

/-! ## The minimal Galerkin input `RegPkgMin` (design `FTS_STRONG_ROUTE.md` §1, §4)

The `Galerkin.RegPkg` interface asked for more than the strong-solution route can supply: a `C^∞`
(`smoothOrder`) field on `τ ∈ (-1,0)`, `ℋ⁵`-membership and an `ℋ³`-*membership* of `∂_τg` (which
does not support R5, since R5 needs a *uniform* bound).  `FTS_STRONG_ROUTE.md` §1 pinpoints which
fields are actually consumed by Open2 and by R1–R8 and proposes the following replacement, which
this area takes as its input (the lead's instruction of 2026-10-07). -/

/-- **THE MINIMAL INPUT `RegPkgMin`** of the Galerkin→regularity bridge
(`Submission/Work/FTS/FTS_STRONG_ROUTE.md` §1 and §4):

* `c1` — joint `C¹` on `z > 0, 0 < θ < π/2, τ > 0`;
* `c4` — `C⁴` on the open quadrant `Q0`, at every strip time `τ ≥ 0` (the field that replaces the
  `C^∞` field `Galerkin.RegPkg.smooth`, and which is what the `𝒲`-sup lemmas of R2–R4 consume);
* `cont` — continuity in `τ` on `Ici 0` at fixed `(z,θ) ∈ Qd`;
* `mem4` — honest `ℋ⁴`-membership at every `τ ≥ 0`;
* `dbd` — a **uniform** `ℋ³` bound on `∂_τg` for `τ > 0` (this is what R5 consumes; the delivered
  `Galerkin.RegPkg.deriv3` gives membership only, which is not a bound);
* `vanish` — vanishing on the two angular boundary lines. -/
structure RegPkgMin (α : ℝ) (g : Fam) : Prop where
  /-- joint `C¹` on the open slab `z > 0, 0 < θ < π/2, τ > 0` -/
  c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0)
  /-- `C⁴` on the open quadrant, at every strip time -/
  c4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
    Work.FTS.EllipticEst.Q0
  /-- continuity in `τ` on `[0,∞)` at every point of the open quadrant -/
  cont : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    ContinuousOn (fun τ => g z θ τ) (Set.Ici 0)
  /-- honest `ℋ⁴`-membership at every `τ ≥ 0` -/
  mem4 : ∀ τ, 0 ≤ τ → Work.Spaces.HkMem α 4 (Work.FTS.Galerkin.slice g τ)
  /-- a **uniform** `ℋ³` bound on `∂_τg` for `τ > 0` -/
  dbd : ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
    Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot g τ) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot g τ) ≤ Cd
  /-- vanishing on the two angular boundaries -/
  vanish : ∀ τ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0

/-! ## The corrected composite Hölder constant -/

/-- **The corrected Hölder constant of the composite profile** `x ↦ g (ρ(x)^{3α}) (|θ(x)|)`.

This is `Work.FTS.Regularity.gCompConst` with its last summand changed from the `z·|Δθ|`-term
`K·(3/2)·3^α·(3/2)^{2α}` to the term produced by the corrected Hölder clause
`|Δg| ≤ K·z²·|Δθ|^α`, namely `K·(3/2)^{6α}·(4π)^α` (the near-origin branch gives
`z²|Δψ|^α ≤ (3/2)^{6α}·(4π)^α·min(ρ)^{5α}·d^α ≤ (3/2)^{6α}(4π)^α d^α` since `min ρ ≤ 1` there).
The remaining six summands are literally those of `gCompConst`. -/
def gCompConst' (α Cv Lg Lθ K : ℝ) : ℝ :=
  2 * Cv + (2 * Cv * (3 / 2) ^ α
    + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3 / 2) * 3 ^ α * (3 / 2) ^ (2 * α)
        + K * (3 / 2) ^ (6 * α) * (4 * Real.pi) ^ α))))

/-- `gCompConst'` as a nonnegative real (the form in which `HolderWith` consumes it). -/
def gCompConstNN' (α Cv Lg Lθ K : ℝ) : ℝ≥0 :=
  ⟨|gCompConst' α Cv Lg Lθ K|, abs_nonneg _⟩



end Work.FTS.RegPkgGal
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.L12fBasic =====
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

/-- **Hölder implies continuous.**  A function on `ℝ` with the modulus `N·|Δθ|^α` on a set `s`
(`N ≥ 0`, `α > 0`) is continuous on `s`. -/
theorem continuousOn_of_holder {f : ℝ → ℝ} {s : Set ℝ} {N α : ℝ} (hN : 0 ≤ N) (hα : 0 < α)
    (h : ∀ θ ∈ s, ∀ θ' ∈ s, |f θ - f θ'| ≤ N * |θ - θ'| ^ α) : ContinuousOn f s := by
  have hM : (0 : ℝ) < N + 1 := by linarith
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have hpos : 0 < (ε / (N + 1)) ^ (1 / α) := Real.rpow_pos_of_pos (div_pos hε hM) _
  refine ⟨min 1 ((ε / (N + 1)) ^ (1 / α)), lt_min one_pos hpos, fun a ha hdist => ?_⟩
  have hab : |a - b| ≤ (ε / (N + 1)) ^ (1 / α) := by
    rw [Real.dist_eq] at hdist
    exact le_of_lt (lt_of_lt_of_le hdist (min_le_right _ _))
  have hpow : |a - b| ^ α ≤ ε / (N + 1) := by
    calc |a - b| ^ α ≤ ((ε / (N + 1)) ^ (1 / α)) ^ α :=
          Real.rpow_le_rpow (abs_nonneg _) hab hα.le
      _ = ε / (N + 1) := by
          rw [← Real.rpow_mul (le_of_lt (div_pos hε hM)),
            one_div_mul_cancel (ne_of_gt hα), Real.rpow_one]
  have key : |f a - f b| ≤ N * (ε / (N + 1)) :=
    le_trans (h a ha b hb) (mul_le_mul_of_nonneg_left hpow hN)
  have key2 : N * (ε / (N + 1)) < ε := by
    have hlt : N / (N + 1) < 1 := by
      rw [div_lt_one hM]; linarith
    calc N * (ε / (N + 1)) = (N / (N + 1)) * ε := by ring
      _ < 1 * ε := mul_lt_mul_of_pos_right hlt hε
      _ = ε := one_mul ε
  rw [Real.dist_eq]
  exact lt_of_le_of_lt key key2

/-- `K θ = 3 sin θ cos²θ ≥ 0` on `Iθ`. -/
theorem K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  simp only [Work.Spaces.K]
  positivity

/-- `K θ = 3 sin θ cos²θ ≤ 3` on `Iθ`. -/
theorem K_le_three_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hc0 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  simp only [Work.Spaces.K]
  nlinarith [mul_nonneg hs hc0]

/-- `|K θ| ≤ 3` on `Iθ`. -/
theorem abs_K_le_three {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : |Work.Spaces.K θ| ≤ 3 := by
  rw [abs_of_nonneg (K_nonneg_of_mem_Iθ hθ)]
  exact K_le_three_of_mem_Iθ hθ


/-- **The angular `L¹` bound.**  A pointwise bound on `Iθ` bounds the angular integral, the total
angular mass being `π/2`. -/
theorem setIntegral_abs_le_of_bound {f : ℝ → ℝ} {c : ℝ}
    (h : ∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ c) :
    ∫ θ in Work.Spaces.Iθ, |f θ| ≤ c * (Real.pi / 2) := by
  have hInt : MeasureTheory.IntegrableOn (fun _ : ℝ => c) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (ne_of_lt Work.Spaces.volume_Iθ_lt_top)
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (Filter.Eventually.of_forall fun θ => abs_nonneg _) hInt
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact h θ hθ)
  have hconst : (∫ θ in Work.Spaces.Iθ, (fun _ : ℝ => c) θ) = c * (Real.pi / 2) := by
    rw [MeasureTheory.setIntegral_const, Work.Spaces.volume_real_Iθ, smul_eq_mul]
    ring
  exact le_trans hmono (le_of_eq hconst)


end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.jet_L12_Fstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.jet_L12_Fstar`

The `L₁₂`-image of the **explicit** profile `F_* = Work.Construction.Fstar (pExp α)`, as a
`Jet` in the joint variables `(z,θ,τ)`: the function

  `(z,θ,τ) ↦ L₁₂(F_*)(z)`

is a *radial* function, so it is trivially constant in `θ` and `τ`; the content of the lemma is
the explicit evaluation

  `L₁₂(F_*)(z) = 2·pExp α/(1+z)`   (`Work.Construction.L12_Fstar_eq`, at `α' = pExp α`)

together with the two elementary facts about `z ↦ 2·pExp α/(1+z)` on `z ≥ 0`: it is bounded by
`2·pExp α` and `2·pExp α`-Lipschitz.  Those give the `Jet` with constant
`max (2 pExp α) (4 pExp α)` (the `4` comes from the large-distance regime, where the sup bound
replaces the Lipschitz estimate).

This is the leaf `Der.jet_L12_Fstar` of the `R5Slot` tree (NOTES_RegPkgGal §14), consumed by
`Der.jet_N0`.
-/

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter

theorem jet_L12_Fstar {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S) :
    ∃ N : ℝ, Work.FTS.Regularity.Jet α S N
      (fun z θ τ => Work.Coercivity.L12f (fun z θ => Work.Construction.Fstar
        (Work.FTS.Regularity.pExp α) z θ) z) := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp0 : (0 : ℝ) ≤ Work.FTS.Regularity.pExp α := hp.le
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hα1 : α ≤ 1 := by linarith
  -- the explicit value of the operator on the profile
  have hval : ∀ z : ℝ, 0 ≤ z → Work.Coercivity.L12f
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z
        = 2 * (Work.FTS.Regularity.pExp α) / (1 + z) := by
    intro z hz
    rw [show Work.Coercivity.L12f
          (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        = Work.Construction.L12 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) from rfl,
      Work.Construction.L12_Fstar_eq hp hp1 hz]
  -- it is `2 · pExp α`-Lipschitz on `[0,∞)`
  have hglip : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |Work.Coercivity.L12f (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z
        - Work.Coercivity.L12f
            (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z'|
        ≤ 2 * Work.FTS.Regularity.pExp α * |z - z'| := by
    intro z z' hz hz'
    rw [hval z hz, hval z' hz']
    have hden : (0 : ℝ) < (1 + z) * (1 + z') := by positivity
    rw [show 2 * Work.FTS.Regularity.pExp α / (1 + z) - 2 * Work.FTS.Regularity.pExp α / (1 + z')
        = 2 * Work.FTS.Regularity.pExp α * (z' - z) / ((1 + z) * (1 + z')) by
      field_simp
      ring]
    rw [abs_div, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hp0),
      abs_of_pos hden, abs_sub_comm]
    rw [div_le_iff₀ hden]
    have hd1 : (1 : ℝ) ≤ (1 + z) * (1 + z') := by nlinarith
    have hA : (0 : ℝ) ≤ 2 * Work.FTS.Regularity.pExp α * |z - z'| :=
      mul_nonneg (mul_nonneg (by norm_num) hp0) (abs_nonneg _)
    calc 2 * Work.FTS.Regularity.pExp α * |z - z'|
          = 2 * Work.FTS.Regularity.pExp α * |z - z'| * 1 := by ring
      _ ≤ 2 * Work.FTS.Regularity.pExp α * |z - z'| * ((1 + z) * (1 + z')) :=
          mul_le_mul_of_nonneg_left hd1 hA
  -- and bounded by `2 · pExp α`
  have hgbdd : ∀ z : ℝ, 0 ≤ z →
      |Work.Coercivity.L12f (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z|
        ≤ 2 * Work.FTS.Regularity.pExp α := by
    intro z hz
    rw [hval z hz,
      abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hp0) (by linarith))]
    exact div_le_self (mul_nonneg (by norm_num) hp0) (by linarith)
  refine ⟨max (2 * Work.FTS.Regularity.pExp α) (2 * (2 * Work.FTS.Regularity.pExp α)),
    le_trans (mul_nonneg (by norm_num) hp0) (le_max_left _ _), ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    change |Work.Coercivity.L12f
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z|
      ≤ max (2 * Work.FTS.Regularity.pExp α) (2 * (2 * Work.FTS.Regularity.pExp α))
    exact le_trans (hgbdd z hz) (le_max_left _ _)
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have hh := Work.FTS.RegPkgGal.Der.Lib.holder_of_lipschitz_of_bounded
      (f := fun z => Work.Coercivity.L12f
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z)
      hα hα1 (mul_nonneg (by norm_num) hp0) (mul_nonneg (by norm_num) hp0)
      hglip hgbdd z z' hz hz'
    have hzth : |z - z'| ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by linarith [abs_nonneg (θ - θ'), abs_nonneg (τ - τ')]) hα.le
    change |Work.Coercivity.L12f
          (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z
        - Work.Coercivity.L12f
            (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z'|
      ≤ max (2 * Work.FTS.Regularity.pExp α) (2 * (2 * Work.FTS.Regularity.pExp α))
        * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α
    exact le_trans hh (mul_le_mul_of_nonneg_left hzth
      (le_trans (mul_nonneg (by norm_num) hp0) (le_max_left _ _)))

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.rhs_jet_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.rhs_jet_aux` — the analytic and `Jet`-closure helpers of
`rhs_jet_of_parts`

This is the auxiliary module of `Submission/Work/FTS/RegPkgGal/Der/rhs_jet_of_parts.lean`.

It contains

* the elementary analytic facts about `θ ↦ Γ(θ)/c(3α) = (sin θ cos²θ)^α/c(3α)` and
  `z ↦ 2z²/(1+z)³` that give the bound and the `α`-Hölder modulus of the coercivity correction
  `AK α z θ = (Γ(θ)/c)·2z²/(1+z)³` (`rhsJet_ak_bounds`);
* the `Jet`-closure API used by the assembly: `rhsJet_add` (sum), `rhsJet_neg` (negation),
  `rhsJet_congr` (transport along a pointwise equality) and `rhsJet_mul` (multiplication by a
  bounded `α`-Hölder scalar depending on `τ` only).

All declarations are prefixed `rhsJet_` so as not to collide with the delegations
`Work.FTS.RegPkgGal.Der.{gam_div_c_holder,zsqCube_holder}` that prove the two `θ`- and
`z`-estimates independently.
-/

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false

/-! ## Elementary analytic helpers -/

/-- `|u^α - v^α| ≤ |u - v|^α` for `u, v ≥ 0` and `0 < α ≤ 1` (concavity of `t ↦ t^α`). -/
theorem rhsJet_rpow_abs_sub_le {α x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hα0 : 0 < α)
    (hα1 : α ≤ 1) : |x ^ α - y ^ α| ≤ |x - y| ^ α := by
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → |a ^ α - b ^ α| ≤ |a - b| ^ α := by
    intro a b ha hb
    wlog h : b ≤ a generalizing a b with H
    · rw [abs_sub_comm, abs_sub_comm a b]
      exact H b a hb ha (not_le.mp h).le
    · have h1 : a ^ α ≤ (a - b) ^ α + b ^ α := by
        have := Real.rpow_add_le_add_rpow (sub_nonneg.mpr h) hb hα0.le hα1
        rwa [sub_add_cancel] at this
      have h2 : b ^ α ≤ a ^ α := Real.rpow_le_rpow hb h hα0.le
      have h3 : 0 ≤ a - b := sub_nonneg.mpr h
      rw [abs_of_nonneg (sub_nonneg.mpr h2), abs_of_nonneg h3]
      linarith
  exact key x y hx hy

/-- `θ ↦ sin θ cos²θ` is `3`-Lipschitz on `ℝ` (product rule, with the `1`-Lipschitz continuity of
`sin` and `cos`). -/
theorem rhsJet_sin_cos_sq_lipschitz (θ θ' : ℝ) :
    |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ≤ 3 * |θ - θ'| := by
  have hs : |Real.sin θ - Real.sin θ'| ≤ |θ - θ'| := by
    have h := Real.lipschitzWith_sin.dist_le_mul θ θ'
    simpa [Real.dist_eq] using h
  have hc : |Real.cos θ - Real.cos θ'| ≤ |θ - θ'| := by
    have h := Real.lipschitzWith_cos.dist_le_mul θ θ'
    simpa [Real.dist_eq] using h
  have hc1 : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hc2 : |Real.cos θ'| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ', Real.cos_le_one θ'⟩
  have hcos2 : |Real.cos θ ^ 2 - Real.cos θ' ^ 2| ≤ 2 * |θ - θ'| := by
    have h : Real.cos θ ^ 2 - Real.cos θ' ^ 2
        = (Real.cos θ - Real.cos θ') * (Real.cos θ + Real.cos θ') := by ring
    rw [h, abs_mul]
    have h1 : |Real.cos θ + Real.cos θ'| ≤ 2 := by
      calc |Real.cos θ + Real.cos θ'| ≤ |Real.cos θ| + |Real.cos θ'| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add hc1 hc2
        _ = 2 := by norm_num
    calc |Real.cos θ - Real.cos θ'| * |Real.cos θ + Real.cos θ'| ≤ |θ - θ'| * 2 :=
          mul_le_mul hc h1 (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |θ - θ'| := by ring
  have hsq : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_sq]; nlinarith [abs_le.mp hc1]
  have hs1 : |Real.sin θ'| ≤ 1 := by
    rw [abs_le]; exact ⟨Real.neg_one_le_sin θ', Real.sin_le_one θ'⟩
  rw [show Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2
      = (Real.sin θ - Real.sin θ') * Real.cos θ ^ 2
        + Real.sin θ' * (Real.cos θ ^ 2 - Real.cos θ' ^ 2) by ring]
  calc |(Real.sin θ - Real.sin θ') * Real.cos θ ^ 2
        + Real.sin θ' * (Real.cos θ ^ 2 - Real.cos θ' ^ 2)|
      ≤ |(Real.sin θ - Real.sin θ') * Real.cos θ ^ 2|
        + |Real.sin θ' * (Real.cos θ ^ 2 - Real.cos θ' ^ 2)| := abs_add_le _ _
    _ = |Real.sin θ - Real.sin θ'| * |Real.cos θ ^ 2|
        + |Real.sin θ'| * |Real.cos θ ^ 2 - Real.cos θ' ^ 2| := by rw [abs_mul, abs_mul]
    _ ≤ |θ - θ'| * 1 + 1 * (2 * |θ - θ'|) :=
        add_le_add (mul_le_mul hs hsq (abs_nonneg _) (abs_nonneg _))
          (mul_le_mul hs1 hcos2 (abs_nonneg _) (by norm_num))
    _ = 3 * |θ - θ'| := by ring

/-- `θ ↦ Γ(θ)/c(3α)` is `40`-Hölder with exponent `α` on `Iθ`, for `0 < α ≤ 1/3`.  This is
`|u^α - v^α| ≤ |u - v|^α` for `u = sin θ cos²θ`, the `3`-Lipschitz bound on `u` and
`1/10 ≤ c(3α)`. -/
theorem rhsJet_gam_div_c_holder {α θ θ' : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ / Work.Spaces.c (Work.FTS.Regularity.pExp α)
      - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ' / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
    ≤ 40 * |θ - θ'| ^ α := by
  have hα1 : α ≤ 1 := by linarith
  have hP : 0 < Work.FTS.Regularity.pExp α := by rw [Work.FTS.Regularity.pExp]; linarith
  have hP1 : Work.FTS.Regularity.pExp α ≤ 1 := by rw [Work.FTS.Regularity.pExp]; linarith
  obtain ⟨hc1, hc10⟩ := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hP hP1
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith
  have hG : ∀ φ : ℝ, Work.Spaces.Gam (Work.FTS.Regularity.pExp α) φ
      = (Real.sin φ * Real.cos φ ^ 2) ^ α := by
    intro φ
    rw [Work.Spaces.Gam, Work.FTS.Regularity.pExp]
    norm_num
  have hs0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    exact mul_nonneg hs (by positivity)
  have hs0' : 0 ≤ Real.sin θ' * Real.cos θ' ^ 2 := by
    have hs : 0 ≤ Real.sin θ' := Real.sin_nonneg_of_mem_Icc ⟨hθ'.1, by linarith [hθ'.2, Real.pi_pos]⟩
    exact mul_nonneg hs (by positivity)
  have hbase : |(Real.sin θ * Real.cos θ ^ 2) ^ α - (Real.sin θ' * Real.cos θ' ^ 2) ^ α|
      ≤ |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ^ α :=
    rhsJet_rpow_abs_sub_le hs0 hs0' hα hα1
  have hlip : |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ^ α
      ≤ (3 * |θ - θ'|) ^ α :=
    Real.rpow_le_rpow (abs_nonneg _) (rhsJet_sin_cos_sq_lipschitz θ θ') hα.le
  have h3 : (3:ℝ) ^ α ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hα1
    rwa [Real.rpow_one] at h
  have hmain : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'| ≤ 3 * |θ - θ'| ^ α := by
    rw [hG θ, hG θ']
    calc |(Real.sin θ * Real.cos θ ^ 2) ^ α - (Real.sin θ' * Real.cos θ' ^ 2) ^ α|
        ≤ |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ^ α := hbase
      _ ≤ (3 * |θ - θ'|) ^ α := hlip
      _ = 3 ^ α * |θ - θ'| ^ α := Real.mul_rpow (by norm_num) (abs_nonneg _)
      _ ≤ 3 * |θ - θ'| ^ α := by
          have h0 : (0:ℝ) ≤ |θ - θ'| ^ α := Real.rpow_nonneg (abs_nonneg _) _
          nlinarith [h3, h0]
  have hrew : Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)
      - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ' / Work.Spaces.c (Work.FTS.Regularity.pExp α)
      = (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ')
        / Work.Spaces.c (Work.FTS.Regularity.pExp α) := by
    ring
  rw [hrew, abs_div, abs_of_pos hcpos]
  have h10 : 1 / Work.Spaces.c (Work.FTS.Regularity.pExp α) ≤ 10 := by
    rw [div_le_iff₀ hcpos]; linarith
  have hd0 : (0:ℝ) ≤ |θ - θ'| ^ α := Real.rpow_nonneg (abs_nonneg _) _
  calc |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'| / Work.Spaces.c (Work.FTS.Regularity.pExp α)
      ≤ (3 * |θ - θ'| ^ α) / Work.Spaces.c (Work.FTS.Regularity.pExp α) :=
        div_le_div_of_nonneg_right hmain hcpos.le
    _ = 3 * |θ - θ'| ^ α * (1 / Work.Spaces.c (Work.FTS.Regularity.pExp α)) := by ring
    _ ≤ 3 * |θ - θ'| ^ α * 10 := mul_le_mul_of_nonneg_left h10 (by positivity)
    _ ≤ 40 * |θ - θ'| ^ α := by linarith

/-- `|2z²/(1+z)³| ≤ 1` for `z ≥ 0`. -/
theorem rhsJet_zsqCube_bdd {z : ℝ} (hz : 0 ≤ z) : |2 * z ^ 2 / (1 + z) ^ 3| ≤ 1 := by
  have h1 : (0:ℝ) < (1 + z) ^ 3 := by positivity
  have h2 : (0:ℝ) ≤ 2 * z ^ 2 := by positivity
  rw [abs_div, abs_of_pos h1, div_le_iff₀ h1, abs_of_nonneg h2]
  nlinarith [hz, sq_nonneg z]

/-- The polynomial inequality behind the Lipschitz bound for `2z²/(1+z)³`: for `p, u ≥ 0`,
`|p + 3u - u²| ≤ (1 + p + u)³`. -/
theorem rhsJet_tri_abs_aux {p u : ℝ} (hp : 0 ≤ p) (hu : 0 ≤ u) :
    |p + 3 * u - u ^ 2| ≤ (1 + p + u) ^ 3 := by
  rw [abs_le]
  constructor
  · nlinarith [hp, hu, sq_nonneg p, sq_nonneg u, pow_nonneg hp 3, pow_nonneg hu 3,
      mul_nonneg hp hu, mul_nonneg (pow_nonneg hp 2) hu, mul_nonneg hp (pow_nonneg hu 2),
      mul_nonneg (sq_nonneg p) (sq_nonneg u)]
  · nlinarith [hp, hu, sq_nonneg p, sq_nonneg u, pow_nonneg hp 3, pow_nonneg hu 3,
      mul_nonneg hp hu]

/-- `z ↦ 2z²/(1+z)³` is `2`-Lipschitz on `[0,∞)` (the true constant is `≈ 0.36`). -/
theorem rhsJet_zsqCube_lip {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| ≤ 2 * |z - z'| := by
  have h1 : (0:ℝ) < (1 + z) ^ 3 := by positivity
  have h2 : (0:ℝ) < (1 + z') ^ 3 := by positivity
  have hp : (0:ℝ) ≤ z + z' := by linarith
  have hu : (0:ℝ) ≤ z * z' := by positivity
  have hq : |z + z' + 3 * z * z' - z ^ 2 * z' ^ 2| ≤ (1 + z) ^ 3 * (1 + z') ^ 3 := by
    have key := rhsJet_tri_abs_aux hp hu
    rwa [show (1 + (z + z') + z * z') ^ 3 = (1 + z) ^ 3 * (1 + z') ^ 3 by ring,
      show (z + z') + 3 * (z * z') - (z * z') ^ 2
        = z + z' + 3 * z * z' - z ^ 2 * z' ^ 2 by ring] at key
  have hfac : 2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3
      = 2 * (z - z') * (z + z' + 3 * z * z' - z ^ 2 * z' ^ 2)
        / ((1 + z) ^ 3 * (1 + z') ^ 3) := by
    field_simp
    ring
  have habs : |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3|
      = 2 * |z - z'| * |z + z' + 3 * z * z' - z ^ 2 * z' ^ 2|
        / ((1 + z) ^ 3 * (1 + z') ^ 3) := by
    rw [hfac, abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_pos (mul_pos h1 h2)]
  rw [habs, div_le_iff₀ (mul_pos h1 h2)]
  nlinarith [hq, abs_nonneg (z - z')]

/-- `z ↦ 2z²/(1+z)³` is `α`-Hölder with constant `2` on `[0,∞)`, for `0 < α ≤ 1`. -/
theorem rhsJet_zsqCube_holder {α z z' : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| ≤ 2 * |z - z'| ^ α := by
  rcases le_or_gt |z - z'| 1 with hd | hd
  · have h1 : |z - z'| ≤ |z - z'| ^ α := by
      rcases eq_or_lt_of_le (abs_nonneg (z - z')) with h | h
      · refine le_of_eq ?_
        rw [h.symm]
        exact (Real.zero_rpow hα.ne').symm
      · have := Real.rpow_le_rpow_of_exponent_ge h hd hα1
        rwa [Real.rpow_one] at this
    have := rhsJet_zsqCube_lip hz hz'
    linarith
  · have h1 : (1:ℝ) ≤ |z - z'| ^ α := Real.one_le_rpow hd.le hα.le
    have h2 := rhsJet_zsqCube_bdd hz
    have h3 := rhsJet_zsqCube_bdd hz'
    have h4 : |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| ≤ 2 := by
      calc |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3|
          = |2 * z ^ 2 / (1 + z) ^ 3 + -(2 * z' ^ 2 / (1 + z') ^ 3)| := by ring_nf
        _ ≤ |2 * z ^ 2 / (1 + z) ^ 3| + |-(2 * z' ^ 2 / (1 + z') ^ 3)| := abs_add_le _ _
        _ = |2 * z ^ 2 / (1 + z) ^ 3| + |2 * z' ^ 2 / (1 + z') ^ 3| := by rw [abs_neg]
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by norm_num
    have h0 : (0:ℝ) ≤ |z - z'| ^ α := Real.rpow_nonneg (abs_nonneg _) _
    nlinarith

/-- **Bound and Hölder modulus of `AK`.**  For `0 < α ≤ 1/3` the function
`AK (pExp α) z θ = (Γ(θ)/c(3α))·2z²/(1+z)³` satisfies `|AK| ≤ 10` on `[0,∞) × Iθ` and is
`α`-Hölder for the metric `|Δz| + |Δθ|` with constant `100`. -/
theorem rhsJet_ak_bounds {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    (∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ| ≤ 10) ∧
    (∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
      |Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ
        - Work.Construction.AK (Work.FTS.Regularity.pExp α) z' θ'|
      ≤ 100 * (|z - z'| + |θ - θ'|) ^ α) := by
  have hα1 : α ≤ 1 := by linarith
  have hP : 0 < Work.FTS.Regularity.pExp α := by rw [Work.FTS.Regularity.pExp]; linarith
  have hP1 : Work.FTS.Regularity.pExp α ≤ 1 := by rw [Work.FTS.Regularity.pExp]; linarith
  obtain ⟨hc1, hc10⟩ := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hP hP1
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith
  have hgc : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
        ≤ 10 := by
    intro θ hθ
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hP hθ
    have h1 : Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)
        ≤ 1 / Work.Spaces.c (Work.FTS.Regularity.pExp α) := by
      rw [div_le_iff₀ hcpos, div_mul_cancel₀ 1 hcpos.ne']
      exact hG1
    have h2 : 1 / Work.Spaces.c (Work.FTS.Regularity.pExp α) ≤ 10 := by
      rw [div_le_iff₀ hcpos]; linarith
    rw [abs_of_nonneg (div_nonneg hG0 hcpos.le)]
    linarith
  constructor
  · intro z hz θ hθ
    rw [Work.Construction.AK, abs_mul]
    calc |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)| * |2 * z ^ 2 / (1 + z) ^ 3|
        ≤ 10 * 1 := mul_le_mul (hgc θ hθ) (rhsJet_zsqCube_bdd hz) (abs_nonneg _) (by norm_num)
      _ = 10 := by norm_num
  · intro z z' hz hz' θ hθ θ' hθ'
    unfold Work.Construction.AK
    set d := |z - z'| + |θ - θ'| with hd
    have hd0 : 0 ≤ d := by rw [hd]; positivity
    have hzd : |z - z'| ^ α ≤ d ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (by rw [hd]; linarith [abs_nonneg (θ - θ')]) hα.le
    have hθd : |θ - θ'| ^ α ≤ d ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (by rw [hd]; linarith [abs_nonneg (z - z')]) hα.le
    have hg1 : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)
        - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ' / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
        ≤ 40 * |θ - θ'| ^ α := rhsJet_gam_div_c_holder hα hα13 hθ hθ'
    have hF1 : |2 * z ^ 2 / (1 + z) ^ 3| ≤ 1 := rhsJet_zsqCube_bdd hz
    have hF2 : |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| ≤ 2 * |z - z'| ^ α :=
      rhsJet_zsqCube_holder hα hα1 hz hz'
    have hg2 : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)| ≤ 10 := hgc θ' hθ'
    have h1 : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)
          - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
        * |2 * z ^ 2 / (1 + z) ^ 3| ≤ 40 * d ^ α := by
      have h₁ : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
          * |2 * z ^ 2 / (1 + z) ^ 3| ≤ (40 * |θ - θ'| ^ α) * 1 :=
        mul_le_mul hg1 hF1 (abs_nonneg _) (by positivity)
      nlinarith [h₁, hθd, Real.rpow_nonneg hd0 α]
    have h2 : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
        * |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| ≤ 20 * d ^ α := by
      have h₁ : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
          * |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3|
          ≤ 10 * (2 * |z - z'| ^ α) :=
        mul_le_mul hg2 hF2 (abs_nonneg _) (by norm_num)
      nlinarith [h₁, hzd, Real.rpow_nonneg hd0 α]
    have key : Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / Work.Spaces.c (Work.FTS.Regularity.pExp α) * (2 * z ^ 2 / (1 + z) ^ 3)
          - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / Work.Spaces.c (Work.FTS.Regularity.pExp α) * (2 * z' ^ 2 / (1 + z') ^ 3)
        = (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
            * (2 * z ^ 2 / (1 + z) ^ 3)
          + Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            * (2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3) := by ring
    rw [key]
    calc |(Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
            * (2 * z ^ 2 / (1 + z) ^ 3)
          + Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            * (2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3)|
        ≤ |(Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
            * (2 * z ^ 2 / (1 + z) ^ 3)|
          + |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            * (2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3)| := abs_add_le _ _
      _ = |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
          * |2 * z ^ 2 / (1 + z) ^ 3|
          + |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
            * |2 * z ^ 2 / (1 + z) ^ 3 - 2 * z' ^ 2 / (1 + z') ^ 3| := by
          rw [abs_mul, abs_mul]
      _ ≤ 40 * d ^ α + 20 * d ^ α := add_le_add h1 h2
      _ ≤ 100 * d ^ α := by
          have h0 : (0:ℝ) ≤ d ^ α := Real.rpow_nonneg hd0 α
          linarith

/-! ## The `Jet`-closure API -/

/-- The sum of two `Jet`s. -/
theorem rhsJet_add {α S N₁ N₂ : ℝ} {f g : ℝ → ℝ → ℝ → ℝ}
    (hf : Work.FTS.Regularity.Jet α S N₁ f) (hg : Work.FTS.Regularity.Jet α S N₂ g) :
    Work.FTS.Regularity.Jet α S (N₁ + N₂) (fun z θ τ => f z θ τ + g z θ τ) := by
  refine ⟨add_nonneg hf.1 hg.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    calc |f z θ τ + g z θ τ| ≤ |f z θ τ| + |g z θ τ| := abs_add_le _ _
      _ ≤ N₁ + N₂ := add_le_add (hf.abs_le hz hθ hτ) (hg.abs_le hz hθ hτ)
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h := hf.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h' := hg.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    simp only []
    rw [show f z θ τ + g z θ τ - (f z' θ' τ' + g z' θ' τ')
        = (f z θ τ - f z' θ' τ') + (g z θ τ - g z' θ' τ') by ring]
    calc |(f z θ τ - f z' θ' τ') + (g z θ τ - g z' θ' τ')|
        ≤ |f z θ τ - f z' θ' τ'| + |g z θ τ - g z' θ' τ'| := abs_add_le _ _
      _ ≤ N₁ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α
            + N₂ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := add_le_add h h'
      _ = (N₁ + N₂) * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by ring

/-- The negation of a `Jet`. -/
theorem rhsJet_neg {α S N : ℝ} {f : ℝ → ℝ → ℝ → ℝ}
    (hf : Work.FTS.Regularity.Jet α S N f) :
    Work.FTS.Regularity.Jet α S N (fun z θ τ => -f z θ τ) := by
  refine ⟨hf.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ; simpa using hf.abs_le hz hθ hτ
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    simp only []
    rw [show -f z θ τ - -f z' θ' τ' = -(f z θ τ - f z' θ' τ') by ring, abs_neg]
    exact hf.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'

/-- Transport of a `Jet` along a pointwise equality. -/
theorem rhsJet_congr {α S N : ℝ} {f g : ℝ → ℝ → ℝ → ℝ}
    (h : ∀ z θ τ, f z θ τ = g z θ τ) (H : Work.FTS.Regularity.Jet α S N f) :
    Work.FTS.Regularity.Jet α S N g := by
  refine ⟨H.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    simpa only [← h z θ τ] using H.2.1 z θ τ hz hθ hτ
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    simpa only [← h z θ τ, ← h z' θ' τ'] using H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'

/-- **Product of a `τ`-dependent bounded Hölder scalar with a bounded Hölder function of
`(z,θ)`.** -/
theorem rhsJet_mul {α S M K₁ K₂ : ℝ} {m : ℝ → ℝ} {A : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hm : ∀ τ ∈ Set.Icc 0 S, |m τ| ≤ M)
    (hmh : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |m τ - m τ'| ≤ M * |τ - τ'| ^ α)
    (hA : ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ, |A z θ| ≤ K₁)
    (hAh : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
      |A z θ - A z' θ'| ≤ K₂ * (|z - z'| + |θ - θ'|) ^ α) :
    Work.FTS.Regularity.Jet α S (M * K₁ + M * K₂) (fun z θ τ => m τ * A z θ) := by
  have hMK₁ : 0 ≤ M * K₁ := mul_nonneg hM hK₁
  have hMK₂ : 0 ≤ M * K₂ := mul_nonneg hM hK₂
  refine ⟨by linarith, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    calc |m τ * A z θ| = |m τ| * |A z θ| := abs_mul _ _
      _ ≤ M * K₁ := mul_le_mul (hm τ hτ) (hA z hz θ hθ) (abs_nonneg _) hM
      _ ≤ M * K₁ + M * K₂ := by linarith
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    set d := |z - z'| + |θ - θ'| + |τ - τ'| with hd
    have hd0 : 0 ≤ d := by rw [hd]; positivity
    have hτd : |τ - τ'| ^ α ≤ d ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by rw [hd]; linarith [abs_nonneg (z - z'), abs_nonneg (θ - θ')]) hα.le
    have hzd : (|z - z'| + |θ - θ'|) ^ α ≤ d ^ α :=
      Real.rpow_le_rpow (by positivity) (by rw [hd]; linarith [abs_nonneg (τ - τ')]) hα.le
    have h1 : |m τ - m τ'| * |A z θ| ≤ M * K₁ * d ^ α := by
      have h₁ : |m τ - m τ'| * |A z θ| ≤ (M * |τ - τ'| ^ α) * K₁ :=
        mul_le_mul (hmh τ hτ τ' hτ') (hA z hz θ hθ) (abs_nonneg _) (by positivity)
      have h₂ : M * K₁ * |τ - τ'| ^ α ≤ M * K₁ * d ^ α :=
        mul_le_mul_of_nonneg_left hτd hMK₁
      linarith
    have h2 : |m τ'| * |A z θ - A z' θ'| ≤ M * K₂ * d ^ α := by
      have h₁ : |m τ'| * |A z θ - A z' θ'| ≤ M * (K₂ * (|z - z'| + |θ - θ'|) ^ α) :=
        mul_le_mul (hm τ' hτ') (hAh z z' hz hz' θ hθ θ' hθ') (abs_nonneg _) hM
      have h₂ : M * (K₂ * (|z - z'| + |θ - θ'|) ^ α) ≤ M * (K₂ * d ^ α) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzd hK₂) hM
      have h₃ : M * (K₂ * d ^ α) = M * K₂ * d ^ α := by ring
      linarith
    simp only []
    rw [show m τ * A z θ - m τ' * A z' θ'
        = (m τ - m τ') * A z θ + m τ' * (A z θ - A z' θ') by ring]
    calc |(m τ - m τ') * A z θ + m τ' * (A z θ - A z' θ')|
        ≤ |(m τ - m τ') * A z θ| + |m τ' * (A z θ - A z' θ')| := abs_add_le _ _
      _ = |m τ - m τ'| * |A z θ| + |m τ'| * |A z θ - A z' θ'| := by rw [abs_mul, abs_mul]
      _ ≤ M * K₁ * d ^ α + M * K₂ * d ^ α := add_le_add h1 h2
      _ = (M * K₁ + M * K₂) * d ^ α := by ring

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.zderiv_Nstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.zderiv_Nstar`

The `z`-derivative bound for the modulation term `N_*` of the fake-time equation,

  `N_*(μ,λ,g) = -μ·g - (μ + λ + μλ)·D_z g`   (`Work.Construction.Nstar`),

evaluated on the clock functions `μ(τ)`, `λ(τ)` and on the perturbation family
`(z,θ,τ) ↦ g z θ τ`.

If the `z`-slices `z ↦ g z θ τ` and `z ↦ D_z g(·,θ,τ) z` are differentiable on `z > 0` with
derivatives bounded by `N` (uniformly in `τ ∈ [0,S]`, `θ ∈ Iθ`), and if `|μ|, |λ| ≤ Nmu` on
`[0,S]`, then `z ↦ N_*(μ τ, λ τ, g(·,·,τ)) z θ` is differentiable on `z > 0` with derivative
bounded by `Nmu·N + (2·Nmu + Nmu²)·N` (uniformly).

Note that `N_*` does not involve the *second* `z`-derivative of `g`: the factor
`D_z g = z·∂_zg` is differentiated as a whole, which is exactly what the hypothesis
`hdDg` provides.  The proof is the product/sum rule applied to the two summands, with the
coefficient `μ + λ + μλ` bounded by `|μ| + |λ| + |μ||λ| ≤ 2·Nmu + Nmu²`.

This is the `N_*`-input of `Work.FTS.RegPkgGal.Der.rhs_zderiv_of_parts`: it turns the two
`z`-jet hypotheses on `g` and `D_z g` and the boundedness of the clock functions into the
a-priori regularity of the `N_*` term of the right-hand side of the fake-time equation.
-/

namespace Work.FTS.RegPkgGal.Der

theorem zderiv_Nstar {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {mu lam : ℝ → ℝ} {N Nmu : ℝ}
    (hα : 0 < α) (hS : 0 < S)
    (hdg : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => g z' θ τ) d z ∧ |d| ≤ N)
    (hdDg : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Spaces.Dz (fun z θ => g z θ τ) z' θ) d z ∧ |d| ≤ N)
    (hmu : 0 ≤ Nmu ∧ ∀ τ ∈ Set.Icc 0 S, |mu τ| ≤ Nmu)
    (hlam : ∀ τ ∈ Set.Icc 0 S, |lam τ| ≤ Nmu) :
    ∃ Nc : ℝ, 0 ≤ Nc ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.Nstar (mu τ) (lam τ)
        (fun z θ => g z θ τ) z' θ) d z ∧ |d| ≤ Nc := by
  have hα0 : 0 ≤ α := hα.le
  -- `N ≥ 0` follows from the (non-vacuous) hypothesis `hdg`, evaluated at `τ = 0`, `θ = 0`,
  -- `z = 1`.
  have h0S : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_refl 0, hS.le⟩
  have h0θ : (0 : ℝ) ∈ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact ⟨le_refl 0, by linarith [Real.pi_pos]⟩
  have h1z : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hN0 : 0 ≤ N := by
    obtain ⟨d, _, hd⟩ := hdg 0 h0S 0 h0θ 1 h1z
    exact le_trans (abs_nonneg d) hd
  refine ⟨Nmu * N + (2 * Nmu + Nmu ^ 2) * N, ?_, ?_⟩
  · nlinarith [hmu.1, hN0, sq_nonneg Nmu]
  · intro τ hτ θ hθ z hz
    obtain ⟨dg, hdgd, hdgb⟩ := hdg τ hτ θ hθ z hz
    obtain ⟨dDg, hdDgd, hdDgb⟩ := hdDg τ hτ θ hθ z hz
    -- The bound on the coefficient `μ + λ + μλ`.
    have hc : |mu τ + lam τ + mu τ * lam τ| ≤ 2 * Nmu + Nmu ^ 2 := by
      have hu := hmu.2 τ hτ
      have hl := hlam τ hτ
      have h1 : |mu τ + lam τ| ≤ |mu τ| + |lam τ| := abs_add_le _ _
      have h2 : |mu τ * lam τ| ≤ Nmu * Nmu := by
        rw [abs_mul]
        exact mul_le_mul hu hl (abs_nonneg _) hmu.1
      have h3 : |mu τ + lam τ + mu τ * lam τ| ≤ |mu τ + lam τ| + |mu τ * lam τ| :=
        abs_add_le _ _
      nlinarith [sq_nonneg Nmu]
    have hC0 : 0 ≤ 2 * Nmu + Nmu ^ 2 := by nlinarith [hmu.1, sq_nonneg Nmu]
    refine ⟨(-(mu τ)) * dg + (-(mu τ + lam τ + mu τ * lam τ)) * dDg, ?_, ?_⟩
    · -- The derivative itself: sum rule on the two summands, each with a constant factor.
      have heq : (fun z' => Work.Construction.Nstar (mu τ) (lam τ) (fun z θ => g z θ τ) z' θ)
          = (fun z' => (-(mu τ)) * g z' θ τ)
            + (fun z' => (-(mu τ + lam τ + mu τ * lam τ))
                * Work.Spaces.Dz (fun z θ => g z θ τ) z' θ) := by
        funext z'
        simp only [Pi.add_apply, Work.Construction.Nstar, Work.Spaces.Dz, Work.Spaces.pz]
        ring
      rw [heq]
      exact (hdgd.const_mul (-(mu τ))).add
        (hdDgd.const_mul (-(mu τ + lam τ + mu τ * lam τ)))
    · -- The bound on the derivative.
      have hb1 : |(-(mu τ)) * dg| ≤ Nmu * N := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul (hmu.2 τ hτ) hdgb (abs_nonneg _) hmu.1
      have hb2 : |(-(mu τ + lam τ + mu τ * lam τ)) * dDg| ≤ (2 * Nmu + Nmu ^ 2) * N := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul hc hdDgb (abs_nonneg _) hC0
      calc |(-(mu τ)) * dg + (-(mu τ + lam τ + mu τ * lam τ)) * dDg|
          ≤ |(-(mu τ)) * dg| + |(-(mu τ + lam τ + mu τ * lam τ)) * dDg| := abs_add_le _ _
        _ ≤ Nmu * N + (2 * Nmu + Nmu ^ 2) * N := add_le_add hb1 hb2

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R4b.primBoundLeft =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R4b

theorem primBoundLeft {α : ℝ} (hα : 0 < α) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 < t → t ≤ Real.pi / 4 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ M * t ^ (α - 1) := by
  refine ⟨Real.pi / 2, by positivity, ?_⟩
  intro t ht htle
  -- basic sign and range facts on `(0, π/4]`
  have htpi : t < Real.pi := by linarith [Real.pi_pos]
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht htpi
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  -- the closed form of the density: `Γ(α,t)/sin(2t) = (1/2)·(sin t)^{α-1}·(cos t)^{2α-1}`
  have hc2 : (Real.cos t ^ 2) ^ α = Real.cos t ^ (2 * α) := by
    rw [← Real.rpow_natCast (Real.cos t) 2, ← Real.rpow_mul hc.le]
    norm_num
  have hnum : (Real.sin t * Real.cos t ^ 2) ^ α = Real.sin t ^ α * Real.cos t ^ (2 * α) := by
    rw [Real.mul_rpow hs.le (pow_nonneg hc.le 2), hc2]
  have hmain : (Real.sin t * Real.cos t ^ 2) ^ α / Real.sin (2 * t)
      = (1 / 2) * Real.sin t ^ (α - 1) * Real.cos t ^ (2 * α - 1) := by
    rw [Real.sin_two_mul, hnum, Real.rpow_sub hs, Real.rpow_sub hc, Real.rpow_one, Real.rpow_one]
    field_simp
  -- `sin t / t ∈ [2/π, 1]`, hence `(sin t / t)^{α-1} ≤ π/2`
  have hsdiv_pos : 0 < Real.sin t / t := div_pos hs ht
  have hsdiv_le1 : Real.sin t / t ≤ 1 := (div_le_one ht).2 (Real.sin_le ht.le)
  have hsdiv_ge : 2 / Real.pi ≤ Real.sin t / t := by
    rw [le_div_iff₀ ht]
    exact Real.mul_le_sin ht.le (by linarith)
  have hpow_le_one : (Real.sin t / t) ^ α ≤ 1 := Real.rpow_le_one hsdiv_pos.le hsdiv_le1 hα.le
  have hsig : (Real.sin t / t) ^ (α - 1) ≤ Real.pi / 2 := by
    rw [Real.rpow_sub hsdiv_pos, Real.rpow_one]
    calc (Real.sin t / t) ^ α / (Real.sin t / t) ≤ 1 / (Real.sin t / t) :=
          div_le_div_of_nonneg_right hpow_le_one hsdiv_pos.le
      _ ≤ Real.pi / 2 := by
          have h := one_div_le_one_div_of_le (a := 2 / Real.pi) (b := Real.sin t / t)
            (by positivity) hsdiv_ge
          have h2 : (1 : ℝ) / (2 / Real.pi) = Real.pi / 2 := by field_simp
          linarith [h, h2]
  -- peel off the `t^{α-1}`
  have hsin_bound : Real.sin t ^ (α - 1) ≤ Real.pi / 2 * t ^ (α - 1) := by
    have hdiv : Real.sin t ^ (α - 1) / t ^ (α - 1) ≤ Real.pi / 2 := by
      rw [← Real.div_rpow hs.le ht.le (α - 1)]
      exact hsig
    exact (div_le_iff₀ (Real.rpow_pos_of_pos ht (α - 1))).1 hdiv
  -- `cos t ∈ [√2/2, 1]`, hence `(cos t)^{2α-1} ≤ 2`
  have hcos_lb : √2 / 2 ≤ Real.cos t := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := t) (y := Real.pi / 4) ht.le
      (by linarith [Real.pi_pos]) htle
    rwa [Real.cos_pi_div_four] at h
  have hcos2a : Real.cos t ^ (2 * α) ≤ 1 :=
    Real.rpow_le_one hc.le (Real.cos_le_one t) (by linarith)
  have hcos_bound : Real.cos t ^ (2 * α - 1) ≤ 2 := by
    rw [Real.rpow_sub hc, Real.rpow_one]
    calc Real.cos t ^ (2 * α) / Real.cos t ≤ 1 / Real.cos t :=
          div_le_div_of_nonneg_right hcos2a hc.le
      _ ≤ 2 := by
          have hhalf : (1 : ℝ) / 2 ≤ Real.cos t := by
            have h2 : (1 : ℝ) ≤ √2 := by
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
            linarith
          have h := one_div_le_one_div_of_le (a := (1 : ℝ) / 2) (b := Real.cos t)
            (by norm_num) hhalf
          have h2 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
          linarith [h, h2]
  -- assembly
  have hB : 0 ≤ Real.cos t ^ (2 * α - 1) := Real.rpow_nonneg hc.le _
  have hC : 0 ≤ Real.pi / 2 * t ^ (α - 1) :=
    mul_nonneg (by linarith [Real.pi_pos]) (Real.rpow_nonneg ht.le _)
  have hprod : Real.sin t ^ (α - 1) * Real.cos t ^ (2 * α - 1)
      ≤ (Real.pi / 2 * t ^ (α - 1)) * 2 :=
    mul_le_mul hsin_bound hcos_bound hB hC
  rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma]
  calc (Real.sin t * Real.cos t ^ 2) ^ α / Real.sin (2 * t)
      = (1 / 2) * Real.sin t ^ (α - 1) * Real.cos t ^ (2 * α - 1) := hmain
    _ ≤ (1 / 2) * (Real.pi / 2 * t ^ (α - 1)) * 2 := by
        calc (1 / 2) * Real.sin t ^ (α - 1) * Real.cos t ^ (2 * α - 1)
            = (1 / 2) * (Real.sin t ^ (α - 1) * Real.cos t ^ (2 * α - 1)) := by ring
          _ ≤ (1 / 2) * ((Real.pi / 2 * t ^ (α - 1)) * 2) :=
              mul_le_mul_of_nonneg_left hprod (by norm_num)
          _ = (1 / 2) * (Real.pi / 2 * t ^ (α - 1)) * 2 := by ring
    _ = Real.pi / 2 * t ^ (α - 1) := by ring

end Work.FTS.RegPkgGal.R4b
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R4b.primBoundRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The right-endpoint bound for `Γ(θ)/sin(2θ)`

`Γ α θ = (sin θ · cos²θ)^α` vanishes like `θ^{2α}` as `θ → π/2⁻`, while `sin(2θ)` vanishes
linearly.  This file proves that on the right half interval `[π/4, π/2)` the quotient is
dominated by `(π/2 - θ)^{2α-1}`, i.e. the primitive `∫^θ Γ/sin(2·)` grows like `Γ` itself:

  `Γ α t / sin(2t) ≤ N · (π/2 - t)^{2α-1}`   for `π/4 ≤ t < π/2`.

## Mathematics

Write `δ = π/2 - t ∈ (0, π/4]`, `s = sin δ`, `c = cos δ`.  Then
`sin t = cos δ = c`, `cos t = sin δ = s`, `sin(2t) = 2sc`, so

  `Γ α t / sin(2t) = c^α s^{2α} / (2sc) = (1/2)·c^{α-1}·s^{2α-1}`.

Both factors are comparable with `δ`-powers: `c ∈ [√2/2, 1]` because `δ ∈ (0, π/4]`, and
`sin δ` is squeezed between `(2/π)δ ≤ sin δ ≤ δ` (Jordan's inequality and `sin ≤ id`).  Hence
`c^{α-1} ≤ max 1 ((√2/2)^{α-1})` and `s^{2α-1} ≤ max 1 ((2/π)^{2α-1})·δ^{2α-1}`, which gives the
statement with `N = (max 1 ((√2/2)^{α-1}))·(max 1 ((2/π)^{2α-1}))/2`.  (The bound in fact holds
for every real `α`; positivity of `α` is not used.)

## Formalisation note

The statement is fed to `Work.FTS.RegPkgGal.R4b.van_of_dthvan`, where one integrates the
`D_θ`-derivative of the class datum `|D_θ g| ≤ Cθ z²Γ` to obtain `|g| ≤ Cv Γ`.
-/

set_option linter.unusedVariables false

namespace Work.FTS.RegPkgGal.R4b

theorem primBoundRight {α : ℝ} (hα : 0 < α) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ t : ℝ, Real.pi / 4 ≤ t → t < Real.pi / 2 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ N * (Real.pi / 2 - t) ^ (2 * α - 1) := by
  refine ⟨max 1 ((Real.sqrt 2 / 2) ^ (α - 1))
      * max 1 ((2 / Real.pi) ^ (2 * α - 1)) / 2, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ max 1 ((Real.sqrt 2 / 2) ^ (α - 1)) :=
      le_trans zero_le_one (le_max_left _ _)
    have h2 : (0 : ℝ) ≤ max 1 ((2 / Real.pi) ^ (2 * α - 1)) :=
      le_trans zero_le_one (le_max_left _ _)
    exact div_nonneg (mul_nonneg h1 h2) (by norm_num)
  · intro t ht1 ht2
    -- put `δ = π/2 - t`
    set δ : ℝ := Real.pi / 2 - t with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hδle : δ ≤ Real.pi / 4 := by rw [hδ]; linarith
    have hs : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδpos (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos δ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hδle, Real.pi_pos]⟩
    -- the trigonometric identifications `sin t = cos δ`, `cos t = sin δ`
    have hsin_t : Real.sin t = Real.cos δ := by
      rw [hδ]; exact (Real.cos_pi_div_two_sub t).symm
    have hcos_t : Real.cos t = Real.sin δ := by
      rw [hδ]; exact (Real.sin_pi_div_two_sub t).symm
    -- the exact evaluation of the quotient
    have hkey : Work.FTS.Regularity.Gamma α t / Real.sin (2 * t)
        = (1 / 2) * Real.cos δ ^ (α - 1) * Real.sin δ ^ (2 * α - 1) := by
      have hG : Work.FTS.Regularity.Gamma α t = Real.cos δ ^ α * Real.sin δ ^ (2 * α) := by
        have h1 : Work.FTS.Regularity.Gamma α t = (Real.cos δ * Real.sin δ ^ (2 : ℕ)) ^ α := by
          simp only [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma]
          rw [hsin_t, hcos_t]
        rw [h1, Real.mul_rpow hc.le (by positivity)]
        congr 1
        rw [show Real.sin δ ^ (2 : ℕ) = Real.sin δ ^ (2 : ℝ) from
          by norm_num [Real.rpow_natCast]]
        rw [← Real.rpow_mul hs.le 2 α]
      have hsin2 : Real.sin (2 * t) = 2 * Real.cos δ * Real.sin δ := by
        rw [Real.sin_two_mul, hsin_t, hcos_t]
      rw [hG, hsin2]
      rw [Real.rpow_sub hc α 1, Real.rpow_sub hs (2 * α) 1, Real.rpow_one, Real.rpow_one]
      field_simp
    -- `√2/2 ≤ cos δ`, because `δ ≤ π/4`
    have hcge : Real.sqrt 2 / 2 ≤ Real.cos δ := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := δ) (y := Real.pi / 4)
        hδpos.le (by linarith [Real.pi_pos]) hδle
      rwa [Real.cos_pi_div_four] at h
    -- the `cos`-factor is bounded
    have hcb : Real.cos δ ^ (α - 1) ≤ max 1 ((Real.sqrt 2 / 2) ^ (α - 1)) := by
      rcases lt_or_ge α 1 with h | h
      · exact le_trans (Real.rpow_le_rpow_of_nonpos (by positivity) hcge (by linarith))
          (le_max_right _ _)
      · have h2 : Real.cos δ ^ (α - 1) ≤ (1 : ℝ) ^ (α - 1) :=
          Real.rpow_le_rpow hc.le (Real.cos_le_one δ) (by linarith)
        rw [Real.one_rpow] at h2
        exact le_trans h2 (le_max_left _ _)
    -- the `sin`-factor is bounded
    have hsb : Real.sin δ ^ (2 * α - 1)
        ≤ max 1 ((2 / Real.pi) ^ (2 * α - 1)) * δ ^ (2 * α - 1) := by
      rcases lt_or_ge (2 * α - 1) 0 with h | h
      · have hj : 2 / Real.pi * δ ≤ Real.sin δ :=
          Real.mul_le_sin hδpos.le (by linarith [hδle, Real.pi_pos])
        have h1 : Real.sin δ ^ (2 * α - 1) ≤ (2 / Real.pi * δ) ^ (2 * α - 1) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hj (le_of_lt h)
        have h2 : (2 / Real.pi * δ) ^ (2 * α - 1)
            = (2 / Real.pi) ^ (2 * α - 1) * δ ^ (2 * α - 1) :=
          Real.mul_rpow (by positivity) hδpos.le
        calc Real.sin δ ^ (2 * α - 1) ≤ (2 / Real.pi) ^ (2 * α - 1) * δ ^ (2 * α - 1) := by
              rw [← h2]; exact h1
          _ ≤ max 1 ((2 / Real.pi) ^ (2 * α - 1)) * δ ^ (2 * α - 1) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hδpos.le _)
      · have h1 : Real.sin δ ^ (2 * α - 1) ≤ δ ^ (2 * α - 1) :=
          Real.rpow_le_rpow hs.le (Real.sin_le hδpos.le) h
        calc Real.sin δ ^ (2 * α - 1) ≤ 1 * δ ^ (2 * α - 1) := by rw [one_mul]; exact h1
          _ ≤ max 1 ((2 / Real.pi) ^ (2 * α - 1)) * δ ^ (2 * α - 1) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hδpos.le _)
    have hMcnn : (0 : ℝ) ≤ max 1 ((Real.sqrt 2 / 2) ^ (α - 1)) :=
      le_trans zero_le_one (le_max_left _ _)
    calc Work.FTS.Regularity.Gamma α t / Real.sin (2 * t)
        = 1 / 2 * (Real.cos δ ^ (α - 1) * Real.sin δ ^ (2 * α - 1)) := by
          rw [hkey]; ring
      _ ≤ 1 / 2 * (max 1 ((Real.sqrt 2 / 2) ^ (α - 1))
            * (max 1 ((2 / Real.pi) ^ (2 * α - 1)) * δ ^ (2 * α - 1))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hcb hsb (Real.rpow_nonneg hs.le _) hMcnn
      _ = max 1 ((Real.sqrt 2 / 2) ^ (α - 1))
            * max 1 ((2 / Real.pi) ^ (2 * α - 1)) / 2 * δ ^ (2 * α - 1) := by ring
      _ = max 1 ((Real.sqrt 2 / 2) ^ (α - 1))
            * max 1 ((2 / Real.pi) ^ (2 * α - 1)) / 2 * (Real.pi / 2 - t) ^ (2 * α - 1) := by
          rw [hδ]

end Work.FTS.RegPkgGal.R4b
end
-- ===== merged: Submission.Work.FTS.Regularity.fstarDzUniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option autoImplicit false

namespace Work.FTS.Regularity

/-! ## The `z`-derivative of the static profile -/

/-- The `z`-derivative of the slice `z ↦ F_*(z,θ)` is the `z`-independent factor
`pExp α·(Γ(θ)/c)` times `deriv F_*`: the profile is a multiple of `Work.FM.Fstar`. -/
theorem deriv_fstar_z (α z θ : ℝ) :
    deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z
      = (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
          * deriv Work.FM.Fstar z := by
  have hfun : (fun z' => Work.Construction.Fstar (pExp α) z' θ)
      = fun z' => (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
          * Work.FM.Fstar z' := by
    funext z'
    simp only [Work.Construction.Fstar]
  rw [hfun, deriv_const_mul_field]

/-- **The angular coefficient is uniformly bounded on `Iθ`.**  For `0 < α ≤ 1/3` and
`θ ∈ Iθ = [0,π/2]`,

  `|3α·(Γ(θ)/c(3α))| ≤ 10·3α ≤ 30`,

because `Γ ∈ [0,1]` and `1/10 ≤ c(3α) ≤ 10`.  This is what makes the constant of the
`z`-derivative box independent of `θ` (and hence of the radius `R`). -/
theorem fstarCoef_abs_le {α θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α))| ≤ 10 * pExp α := by
  have hp0 : 0 < pExp α := pExp_pos hα
  have hp1 : pExp α ≤ 1 := pExp_le_one hα13
  obtain ⟨hc1, _hc2⟩ := Work.Spaces.c_bounds (pExp α) hp0 hp1
  have hcpos : 0 < Work.Spaces.c (pExp α) := by linarith
  obtain ⟨hg0, hg1⟩ := Work.Spaces.Gam_bounds (pExp α) θ hp0 hθ
  have hgab : |Work.Spaces.Gam (pExp α) θ| ≤ 1 := by
    rw [abs_of_nonneg hg0]; exact hg1
  rw [abs_mul, abs_of_pos hp0]
  have h2 : |Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)| ≤ 10 := by
    rw [abs_div, abs_of_pos hcpos]
    have h3 : |Work.Spaces.Gam (pExp α) θ| / Work.Spaces.c (pExp α)
        ≤ 1 / Work.Spaces.c (pExp α) := div_le_div_of_nonneg_right hgab hcpos.le
    have h4 : 1 / Work.Spaces.c (pExp α) ≤ 10 := by
      rw [div_le_iff₀ hcpos]; linarith
    linarith
  calc pExp α * |Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)|
      ≤ pExp α * 10 := mul_le_mul_of_nonneg_left h2 hp0.le
    _ = 10 * pExp α := by ring

/-- **`|deriv F_*| ≤ 2` on the physical half-line `z ≥ 0`**: with `deriv F_*(z) = 2(1-z)/(1+z)³`,
the estimate is `2|1-z| ≤ 2(1+z) ≤ 2(1+z)³`. -/
theorem deriv_FM_Fstar_abs_le {z : ℝ} (hz : 0 ≤ z) : |deriv Work.FM.Fstar z| ≤ 2 := by
  rw [Work.FM.deriv_Fstar z (by linarith)]
  have hpos : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have h1 : |1 - z| ≤ 1 + z := by
    rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [h1, hz, sq_nonneg z]

/-! ## The two uniform constants -/

/-- The pointwise bound of the static `z`-derivative, in the multiplicative form used by the
two conjuncts of `fstarDzUniform`. -/
theorem fstarDz_abs_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
        * deriv Work.FM.Fstar z| ≤ 20 * pExp α := by
  have hp0 : 0 < pExp α := pExp_pos hα
  have h1 := fstarCoef_abs_le hα hα13 hθ
  have h2 := deriv_FM_Fstar_abs_le hz
  calc |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
          * deriv Work.FM.Fstar z|
      = |pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α))|
        * |deriv Work.FM.Fstar z| := abs_mul _ _
    _ ≤ (10 * pExp α) * 2 := mul_le_mul h1 h2 (abs_nonneg _) (by nlinarith [hp0])
    _ = 20 * pExp α := by ring

/-- **The `α`-Hölder estimate of the static `z`-derivative.**  Its coefficient in `z` is
`8`-Lipschitz (`Moduli.fstarDerivLip`) and bounded by `10·3α`; on a pair with `|z - z'| ≤ 1`
the Lipschitz modulus upgrades to the `α`-modulus (`t ≤ t^α` for `t ≤ 1`), and for
`|z - z'| ≥ 1` the two pointwise bounds `20·3α` suffice because `1 ≤ |z-z'|^α`. -/
theorem fstarDz_holder {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hα1 : α ≤ 1)
    {z z' θ : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (hθ : θ ∈ Work.Spaces.Iθ) :
    |deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
        - deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z'|
      ≤ 80 * pExp α * |z - z'| ^ α := by
  have hp0 : 0 < pExp α := pExp_pos hα
  have hpnn : 0 ≤ 80 * pExp α := by linarith
  rw [deriv_fstar_z, deriv_fstar_z, ← mul_sub, abs_mul]
  by_cases hle : |z - z'| ≤ 1
  · have hcoef := fstarCoef_abs_le hα hα13 hθ
    have hlip := Moduli.fstarDerivLip hz hz'
    have hkey : |pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α))|
          * |deriv Work.FM.Fstar z - deriv Work.FM.Fstar z'|
        ≤ (10 * pExp α) * (8 * |z - z'|) :=
      mul_le_mul hcoef hlip (abs_nonneg _) (by nlinarith [hp0])
    have hrpow : |z - z'| ≤ |z - z'| ^ α :=
      Real.self_le_rpow_of_le_one (abs_nonneg _) hle hα1
    calc |pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α))|
          * |deriv Work.FM.Fstar z - deriv Work.FM.Fstar z'|
        ≤ (10 * pExp α) * (8 * |z - z'|) := hkey
      _ = 80 * pExp α * |z - z'| := by ring
      _ ≤ 80 * pExp α * |z - z'| ^ α := mul_le_mul_of_nonneg_left hrpow hpnn
  · push_neg at hle
    have h1 := fstarDz_abs_le hα hα13 hz hθ
    have h2 := fstarDz_abs_le hα hα13 hz' hθ
    have hrpow : (1 : ℝ) ≤ |z - z'| ^ α := Real.one_le_rpow hle.le hα.le
    have hsplit : |pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α))|
          * |deriv Work.FM.Fstar z - deriv Work.FM.Fstar z'|
        = |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z
          - (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z'| := by
      rw [← abs_mul, ← mul_sub]
    have htri : |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z
          - (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z'|
        ≤ |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z|
          + |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z'| := by
      have h := abs_sub_le
        ((pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z) 0
        ((pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z')
      simpa using h
    rw [hsplit]
    calc |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z
          - (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z'|
        ≤ |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z|
          + |(pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * deriv Work.FM.Fstar z'| := htri
      _ ≤ 20 * pExp α + 20 * pExp α := add_le_add h1 h2
      _ = 40 * pExp α := by ring
      _ ≤ 80 * pExp α * |z - z'| ^ α := by nlinarith [hrpow, hp0]

/-! ## The theorem -/

theorem fstarDzUniform {α R : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hR : 0 ≤ R) :
    ∃ M0 N0 : ℝ, 0 ≤ M0 ∧ 0 ≤ N0 ∧
      (∀ z θ : ℝ, 0 ≤ z → z ≤ R → θ ∈ Work.Spaces.Iθ →
        |deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z| ≤ M0) ∧
      (∀ z z' θ : ℝ, 0 ≤ z → z ≤ R → 0 ≤ z' → z' ≤ R → θ ∈ Work.Spaces.Iθ →
        |deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
          - deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z'|
          ≤ N0 * |z - z'| ^ α) := by
  have hp0 : 0 < pExp α := pExp_pos hα
  have hα1 : α ≤ 1 := by linarith
  refine ⟨20 * pExp α, 80 * pExp α, by linarith, by linarith, ?_, ?_⟩
  · intro z θ hz _hzR hθ
    rw [deriv_fstar_z]
    exact fstarDz_abs_le hα hα13 hz hθ
  · intro z z' θ hz _hzR hz' _hz'R hθ
    exact fstarDz_holder hα hα13 hα1 hz hz' hθ

end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.Regularity.fstarModuli =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Work.FTS.Regularity

open FiniteTimeSingularity Set Filter Topology MeasureTheory

/-! ## The reduction of `Fstar (3α)` to a constant times the fundamental-model profile -/

/-- `Γ` at the profile exponent: `Spaces.Gam (3α) = Gamma α`, since `(sinθcos²θ)^((3α)/3)` and
`(sinθcos²θ)^α` agree. -/
theorem gam_three (α θ : ℝ) : Work.Spaces.Gam (3 * α) θ = Gamma α θ := by
  rw [← Work.ConstructionInstance.Gamma_div_three (3 * α) θ]
  norm_num

/-- The coefficient `(3α)·(Γ(3α)/c(3α))` of `F_*` in the profile `Fstar (3α)` is bounded by
`10` on the angular domain: `0 < 3α ≤ 1`, `0 ≤ Γ ≤ 1` and `c(3α) ≥ 1/10`. -/
theorem fstarCoeff_abs_le {α θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |(3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))| ≤ 10 := by
  have h3a : 0 < 3 * α := by linarith
  have h3a1 : 3 * α ≤ 1 := by linarith
  have hc := Work.Spaces.c_bounds (3 * α) h3a h3a1
  have hcpos : 0 < Work.Spaces.c (3 * α) := by linarith [hc.1]
  have hG : |Work.Spaces.Gam (3 * α) θ| ≤ 1 := by
    rw [gam_three α θ, abs_of_nonneg (Work.ConstructionInstance.Gamma_nonneg (β := α) hθ)]
    exact Work.ConstructionInstance.Gamma_le_one hα.le hθ
  rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 * α), abs_div, abs_of_pos hcpos]
  have hdiv : |Work.Spaces.Gam (3 * α) θ| / Work.Spaces.c (3 * α) ≤ 10 := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hc.2, hG]
  calc (3 * α) * (|Work.Spaces.Gam (3 * α) θ| / Work.Spaces.c (3 * α))
      ≤ 1 * 10 := mul_le_mul h3a1 hdiv (by positivity) (by norm_num)
    _ = 10 := by ring

/-- The profile is a constant (in `z`) times `F_* z`. -/
theorem fstar_three_eq (α z θ : ℝ) :
    Work.Construction.Fstar (3 * α) z θ
      = ((3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))) * Work.FM.Fstar z := by
  rw [Work.Construction.Fstar]


/-! ## The three moduli -/

variable {α : ℝ}

/-- **The angular modulus**: `Γ = (sin θ cos²θ)^α` is `α`-Hölder on `Iθ` with constant `3^α`,
from the `3`-Lipschitz modulus of the base `sinθcos²θ` and the `α`-Hölder modulus of
`x ↦ x^α` on `[0,∞)`. -/
theorem gammaModulus (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∀ θ θ' : ℝ, θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |Gamma α θ - Gamma α θ'| ≤ 3 ^ α * |θ - θ'| ^ α := by
  intro θ θ' hθ hθ'
  have hb0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    positivity
  have hb0' : 0 ≤ Real.sin θ' * Real.cos θ' ^ 2 := by
    have h1 : 0 ≤ Real.sin θ' :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos])
    positivity
  have hlip := Work.FTS.Regularity.Moduli.sinCosSqLip θ θ'
  calc |Gamma α θ - Gamma α θ'|
      = |(Real.sin θ * Real.cos θ ^ 2) ^ α - (Real.sin θ' * Real.cos θ' ^ 2) ^ α| := rfl
    _ ≤ |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ^ α :=
        Work.FTS.Regularity.Moduli.rpow_abs_sub_le hb0 hb0' hα (by linarith)
    _ ≤ (3 * |θ - θ'|) ^ α := Real.rpow_le_rpow (abs_nonneg _) hlip hα.le
    _ = 3 ^ α * |θ - θ'| ^ α := by
        rw [Real.mul_rpow (by norm_num) (abs_nonneg _)]

/-- **The radial modulus of the profile**: `Fstar (3α)` is Lipschitz in `z` with constant `20`,
uniformly on `Iθ`. -/
theorem fstarModulus (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ|
        ≤ 20 * |z - z'| := by
  intro z z' θ hz hz' hθ
  have hC := fstarCoeff_abs_le hα hα13 hθ
  have hkey : Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ
      = ((3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)))
        * (Work.FM.Fstar z - Work.FM.Fstar z') := by
    simp only [fstar_three_eq]
    ring
  rw [hkey, abs_mul]
  calc |(3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))|
        * |Work.FM.Fstar z - Work.FM.Fstar z'|
      ≤ 10 * (2 * |z - z'|) :=
        mul_le_mul hC (Work.FTS.Regularity.Moduli.fstarLip hz hz') (abs_nonneg _) (by norm_num)
    _ = 20 * |z - z'| := by ring


/-! ## The target -/


end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.Regularity.gComp_abs_le_quant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity

noncomputable section

open Set Filter
open scoped Topology

/-! ## The quantitative bound `|ĝ x| ≤ max K Cv · r(x)^α`

`ĝ x = g (ρ(x)^{3α}) (|θ(x)|)` is the perturbation of the profile composed with the
self-similar variables.  The two data that control it are

* the *angular vanishing* `|g z θ| ≤ Cv · Γ(θ)`, whose angular factor is at most
  `Γ(θ) ≤ (r/ρ)^{2α}` off the axis, and
* the *linear vanishing at the origin* `|g z θ| ≤ K z` for `z ≤ 1`.

Off the axis one case-splits on which of the two dominates: if `r ≤ ρ²` then
`(r/ρ)^{2α} ≤ r^α` and the first gives `|ĝ| ≤ Cv r^α`; if `r > ρ²` then necessarily `ρ ≤ 1`, so
the second applies at `z = ρ^{3α} ≤ 1` and `ρ^{3α} ≤ ρ^{2α} ≤ r^α` gives `|ĝ| ≤ K r^α`.  On the
axis `r = 0` both `Γ` and `r^α` vanish.

This is the form in which the bound is consumed by the per-slice Hölder transfer
(`Work.ConstructionInstance.holder_smul_eTheta`): everything is stated directly in terms of the
two *given* constants `Cv` and `K`, with no auxiliary constant produced by a Taylor estimate.
-/

/-- `(r/ρ)^{2α} ≤ r^α` for `0 ≤ r ≤ ρ²`.  Writing `r = s ρ` (`s = r/ρ ≤ ρ`), this is
`s^{2α} ≤ s^α ρ^α`, i.e. `s^α ≤ ρ^α`. -/
private lemma rpow_two_mul_le_of_le_sq {α r ρ : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (h : r ≤ ρ ^ 2) : (r / ρ) ^ (2 * α) ≤ r ^ α := by
  have hs0 : 0 ≤ r / ρ := div_nonneg hr hρ.le
  have hsρ : r / ρ ≤ ρ := by
    rw [div_le_iff₀ hρ]; nlinarith
  have h1 : (r / ρ) ^ α ≤ ρ ^ α := Real.rpow_le_rpow hs0 hsρ hα.le
  have h2 : (r / ρ) ^ (2 * α) = (r / ρ) ^ α * (r / ρ) ^ α := by
    rw [show 2 * α = α + α from by ring, Real.rpow_add' hs0 (by positivity)]
  rw [h2]
  calc (r / ρ) ^ α * (r / ρ) ^ α ≤ (r / ρ) ^ α * ρ ^ α :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs0 α)
    _ = (r / ρ * ρ) ^ α := (Real.mul_rpow hs0 hρ.le).symm
    _ = r ^ α := by rw [div_mul_cancel₀ r hρ.ne']

/-- `ρ^{3α} ≤ r^α` for `0 < ρ ≤ 1` and `ρ² < r`.  Indeed `ρ^{3α} ≤ ρ^{2α} = (ρ²)^α ≤ r^α`. -/
private lemma rpow_three_mul_le_of_sq_lt {α r ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (h : ρ ^ 2 < r) : ρ ^ (3 * α) ≤ r ^ α := by
  have h1 : ρ ^ (3 * α) ≤ ρ ^ (2 * α) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
  have h2 : ρ ^ (2 * α) = (ρ ^ 2) ^ α := by
    rw [Real.rpow_mul hρ.le (2:ℝ) α, Real.rpow_two]
  calc ρ ^ (3 * α) ≤ ρ ^ (2 * α) := h1
    _ = (ρ ^ 2) ^ α := h2
    _ ≤ r ^ α := Real.rpow_le_rpow (sq_nonneg ρ) h.le hα.le

theorem gComp_abs_le_quant {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : ℝ → ℝ → ℝ}
    {Cv K : ℝ} (hCv : 0 ≤ Cv) (hK : 0 ≤ K)
    (hvt : Work.Spaces.VanishTheta g)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hlin : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → ∀ z : ℝ, 0 ≤ z → z ≤ 1 → |g z θ| ≤ K * z) :
    ∀ x : Work.FTS.Regularity.R3,
      |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
        ≤ max K Cv * (Work.Cyl.radial x) ^ α := by
  intro x
  by_cases hr : Work.Cyl.radial x = 0
  · -- On the axis `r = 0` the angular factor vanishes and the profile vanishes at `θ = 0`.
    have hθ : |Work.Cyl.theta x| = 0 := by
      rw [Work.Cyl.theta, hr, div_zero, Real.arctan_zero, abs_zero]
    have hz : Work.Cyl.radial x ^ α = 0 := by rw [hr, Real.zero_rpow hα.ne']
    rw [hθ, hvt.1, abs_zero, hz, mul_zero]
  · have hrpos : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hr)
    have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hrpos (Work.Cyl.radial_le_rho x)
    have hρnn : 0 ≤ Work.Cyl.rho x := hρpos.le
    have hrn : 0 ≤ Work.Cyl.radial x := hrpos.le
    have hIθ : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := by
      refine ⟨abs_nonneg _, ?_⟩
      rw [Work.Cyl.theta]
      exact abs_le.mpr ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
        le_of_lt (Real.arctan_lt_pi_div_two _)⟩
    -- The angular vanishing bound, with `Γ(θ) ≤ (r/ρ)^{2α}`.
    have hvan' : |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
        ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := by
      calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
          ≤ Cv * Work.ConstructionInstance.Gamma α (|Work.Cyl.theta x|) :=
            hvan _ _ (Real.rpow_nonneg hρnn _) hIθ
        _ ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) :=
            mul_le_mul_of_nonneg_left
              (Work.ConstructionInstance.Gamma_abs_theta_le hα hrpos) hCv
    by_cases hρ1 : Work.Cyl.rho x ≤ 1
    · by_cases hsub : Work.Cyl.radial x ≤ (Work.Cyl.rho x) ^ 2
      · -- Sub-critical radius: the angular factor alone suffices.
        calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
            ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := hvan'
          _ ≤ Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_left
                (rpow_two_mul_le_of_le_sq hα hrn hρpos hsub) hCv
          _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_right (le_max_right K Cv) (Real.rpow_nonneg hrn α)
      · -- Super-critical radius with `ρ ≤ 1`: the linear vanishing at `z = 0` takes over.
        have hz1 : Work.Cyl.rho x ^ (3 * α) ≤ 1 :=
          Real.rpow_le_one hρnn hρ1 (by positivity)
        have hKb : |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
            ≤ K * Work.Cyl.rho x ^ (3 * α) :=
          hlin _ hIθ _ (Real.rpow_nonneg hρnn _) hz1
        have h3 : Work.Cyl.rho x ^ (3 * α) ≤ (Work.Cyl.radial x) ^ α :=
          rpow_three_mul_le_of_sq_lt hα hρpos hρ1 (not_le.mp hsub)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
            ≤ K * (Work.Cyl.rho x ^ (3 * α)) := hKb
          _ ≤ K * (Work.Cyl.radial x) ^ α := mul_le_mul_of_nonneg_left h3 hK
          _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_right (le_max_left K Cv) (Real.rpow_nonneg hrn α)
    · -- `ρ ≥ 1`: then `r ≤ ρ ≤ ρ²`, so the angular factor alone suffices again.
      have hρge : 1 ≤ Work.Cyl.rho x := le_of_lt (not_le.mp hρ1)
      have hsub : Work.Cyl.radial x ≤ (Work.Cyl.rho x) ^ 2 := by
        have h1 : Work.Cyl.radial x ≤ Work.Cyl.rho x := Work.Cyl.radial_le_rho x
        nlinarith
      calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
          ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := hvan'
        _ ≤ Cv * (Work.Cyl.radial x) ^ α :=
            mul_le_mul_of_nonneg_left
              (rpow_two_mul_le_of_le_sq hα hrn hρpos hsub) hCv
        _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right K Cv) (Real.rpow_nonneg hrn α)

end

end Work.FTS.Regularity
end
-- ===== merged: Submission.Work.FTS.Regularity.pzFstarModuli =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FTS.Regularity

/-! ## The angular coefficient of `∂_z F_*(3α)` -/

/-- The angular coefficient `C(θ) = 3α·(Γ(θ)/c(3α))` of the profile's `z`-derivative:
`F_*(3α)(z,θ) = C(θ)·F̂(z)` with `F̂ = Work.FM.Fstar`. -/
def pzCoeff (α : ℝ) (θ : ℝ) : ℝ :=
  (3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))



/-! ## The two moduli of the radial factor `F̂'` -/


/-! ## The two moduli of the angular factor `Γ(3α) = Gam (3α)` -/

/-- `Gam (3α)` is the `α`-th power of the base `sinθcos²θ`. -/
theorem gam_three_eq {α θ : ℝ} :
    Work.Spaces.Gam (3 * α) θ = (Real.sin θ * Real.cos θ ^ 2) ^ α := by
  have h3 : (3 * α) / 3 = α := mul_div_cancel_left₀ α (by norm_num : (3 : ℝ) ≠ 0)
  rw [Work.Spaces.Gam, h3]

theorem gam_three_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam (3 * α) θ := by
  rw [gam_three_eq]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  exact Real.rpow_nonneg (mul_nonneg h1 (sq_nonneg (Real.cos θ))) α

theorem gam_three_le_one {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam (3 * α) θ ≤ 1 := by
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h3 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.cos_sq_le_one θ, sq_nonneg (Real.cos θ)]
  have hb0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg h1 (sq_nonneg _)
  have hb1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [h1, h2, sq_nonneg (Real.cos θ), h3]
  rw [gam_three_eq]
  exact Real.rpow_le_one hb0 hb1 hα.le

/-- **The angular modulus of `Gam (3α)`**: it is `α`-Hölder on `Iθ` with constant `3^α`, from
the `3`-Lipschitz modulus of the base `sinθcos²θ` and the `α`-Hölder modulus of `x ↦ x^α` on
`[0,∞)`. -/
theorem gam_three_holder {α θ θ' : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ'| ≤ 3 ^ α * |θ - θ'| ^ α := by
  have hb0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    exact mul_nonneg h1 (sq_nonneg _)
  have hb0' : 0 ≤ Real.sin θ' * Real.cos θ' ^ 2 := by
    have h1 : 0 ≤ Real.sin θ' :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos])
    exact mul_nonneg h1 (sq_nonneg _)
  rw [gam_three_eq (α := α) (θ := θ), gam_three_eq (α := α) (θ := θ')]
  calc |(Real.sin θ * Real.cos θ ^ 2) ^ α - (Real.sin θ' * Real.cos θ' ^ 2) ^ α|
      ≤ |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ^ α :=
        Moduli.rpow_abs_sub_le hb0 hb0' hα (le_trans hα13 (by norm_num))
    _ ≤ (3 * |θ - θ'|) ^ α :=
        Real.rpow_le_rpow (abs_nonneg _) (Moduli.sinCosSqLip θ θ') hα.le
    _ = 3 ^ α * |θ - θ'| ^ α := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (abs_nonneg _)]

/-! ## The two moduli of the angular coefficient `C` -/

/-- **The uniform bound `|C(θ)| ≤ 10`** on `Iθ`, for `0 < α ≤ 1/3`. -/
theorem pzCoeff_abs_le {α θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) : |pzCoeff α θ| ≤ 10 := by
  have h3a : 0 < 3 * α := by linarith
  have h3a1 : 3 * α ≤ 1 := by linarith
  have hc := Work.Spaces.c_bounds (3 * α) h3a h3a1
  have hcpos : 0 < Work.Spaces.c (3 * α) := by linarith [hc.1]
  have hG0 : 0 ≤ Work.Spaces.Gam (3 * α) θ := gam_three_nonneg hθ
  have hG1 : Work.Spaces.Gam (3 * α) θ ≤ 1 := gam_three_le_one hα hθ
  have hnonneg : 0 ≤ (3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) :=
    mul_nonneg h3a.le (div_nonneg hG0 hcpos.le)
  have hgoal : (3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) ≤ 10 := by
    rw [mul_div_assoc', div_le_iff₀ hcpos]
    nlinarith [hc.1, hG1, hG0, h3a.le, h3a1]
  calc |pzCoeff α θ|
      = |(3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))| := rfl
    _ = (3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) := abs_of_nonneg hnonneg
    _ ≤ 10 := hgoal

/-- The difference of the angular coefficients, with a common denominator. -/
theorem pzCoeff_sub (α θ θ' : ℝ) :
    pzCoeff α θ - pzCoeff α θ'
      = (3 * α) * ((Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ')
          / Work.Spaces.c (3 * α)) := by
  simp only [pzCoeff]
  rw [← mul_sub, div_sub_div_same]

/-- **The angular modulus of the coefficient `C`**: `C` is `α`-Hölder on `Iθ` with constant
`30`. -/
theorem pzCoeff_holder {α θ θ' : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |pzCoeff α θ - pzCoeff α θ'| ≤ 30 * |θ - θ'| ^ α := by
  have h3a : 0 < 3 * α := by linarith
  have h3a1 : 3 * α ≤ 1 := by linarith
  have hc := Work.Spaces.c_bounds (3 * α) h3a h3a1
  have hcpos : 0 < Work.Spaces.c (3 * α) := by linarith [hc.1]
  have hG := gam_three_holder hα hα13 hθ hθ'
  have hpow0 : 0 ≤ |θ - θ'| ^ α := Real.rpow_nonneg (abs_nonneg _) α
  have hfac : (3 * α) / Work.Spaces.c (3 * α) * 3 ^ α ≤ 30 := by
    have h1 : (3 * α) / Work.Spaces.c (3 * α) ≤ 10 := by
      rw [div_le_iff₀ hcpos]
      linarith [hc.1, h3a1]
    have h1' : 0 ≤ (3 * α) / Work.Spaces.c (3 * α) := by positivity
    have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
    have h2 : (3 : ℝ) ^ α ≤ 3 := by
      have h3 : (3 : ℝ) ^ α ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 3 by norm_num) hα1
      rwa [Real.rpow_one] at h3
    have h4 : 0 ≤ (3 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) α
    nlinarith [h1, h1', h2, h4]
  have hbound : (3 * α) * (|Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ'|
        / Work.Spaces.c (3 * α)) ≤ 30 * |θ - θ'| ^ α := by
    calc (3 * α) * (|Work.Spaces.Gam (3 * α) θ - Work.Spaces.Gam (3 * α) θ'|
          / Work.Spaces.c (3 * α))
        ≤ (3 * α) * (3 ^ α * |θ - θ'| ^ α / Work.Spaces.c (3 * α)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hG hcpos.le) h3a.le
      _ = ((3 * α) / Work.Spaces.c (3 * α) * 3 ^ α) * |θ - θ'| ^ α := by
          rw [div_eq_mul_inv]
          ring
      _ ≤ 30 * |θ - θ'| ^ α := mul_le_mul_of_nonneg_right hfac hpow0
  rw [pzCoeff_sub, abs_mul, abs_of_nonneg h3a.le, abs_div, abs_of_pos hcpos]
  exact hbound

/-! ## The target -/


end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.Regularity.smulEThetaHolder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open scoped NNReal

namespace Work.FTS.Regularity

/-- The azimuthal frame vector is a unit vector off the axis and `0` on it, so its norm is at
most `1`. -/
private theorem norm_eTheta_le_one_prv (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  by_cases h : Work.Cyl.radial x = 0
  · simp [Work.Cyl.eTheta, h]
  · rw [Work.Cyl.norm_eTheta x h]

theorem smulEThetaHolder {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {A : Work.FTS.Regularity.R3 → ℝ} {CA Ca : ℝ} (hCA : 0 ≤ CA) (hCa : 0 ≤ Ca)
    (hA : HolderWith ⟨CA, hCA⟩ (⟨α, hα.le⟩ : NNReal) A)
    (hvanA : ∀ x : Work.FTS.Regularity.R3, |A x| ≤ Ca * (Work.Cyl.radial x) ^ α) :
    HolderWith (Work.FTS.Regularity.smulEThetaConst CA Ca) (⟨α, hα.le⟩ : NNReal)
      (fun x : Work.FTS.Regularity.R3 => A x • Work.Cyl.eTheta x) := by
  -- the Hölder bound of `A`, as a `dist` estimate with the explicit constant `CA`
  have hcay : ∀ x y : R3, dist (A x) (A y) ≤ CA * dist x y ^ α := by
    intro x y
    exact hA.dist_le x y
  -- the weighted geometric bound `r(y)^α ‖e_θ x - e_θ y‖ ≤ 2 dist x y ^ α`
  have hw : ∀ x y : R3,
      Work.Cyl.radial y ^ α * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
        ≤ 2 * dist x y ^ α := by
    intro x y
    rw [mul_comm]
    refine Work.Stability.mul_rpow_le (p := ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖)
      (ρ := Work.Cyl.radial y) (d := dist x y) (α := α) hα hα1
      (Work.Cyl.radial_nonneg y) dist_nonneg (norm_nonneg _)
      (Work.Cyl.eTheta_sub_norm_mul_le x y) ?_
    calc ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
        ≤ ‖Work.Cyl.eTheta x‖ + ‖Work.Cyl.eTheta y‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by linarith [norm_eTheta_le_one_prv x, norm_eTheta_le_one_prv y]
      _ = 2 := by norm_num
  refine Work.Stability.holderWith_of_dist_le (C := smulEThetaConst CA Ca)
    (r := ⟨α, hα.le⟩) (f := fun x : R3 => A x • Work.Cyl.eTheta x) ?_
  intro x y
  rw [dist_eq_norm]
  have hsplit : A x • Work.Cyl.eTheta x - A y • Work.Cyl.eTheta y
      = (A x - A y) • Work.Cyl.eTheta x
        + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y) := by
    rw [sub_smul, smul_sub]; abel
  rw [hsplit]
  have hcore :
      ‖(A x - A y) • Work.Cyl.eTheta x + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖
        ≤ (CA + 2 * Ca) * dist x y ^ α := by
    calc ‖(A x - A y) • Work.Cyl.eTheta x + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖
        ≤ ‖(A x - A y) • Work.Cyl.eTheta x‖
          + ‖A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖ := norm_add_le _ _
      _ = |A x - A y| * ‖Work.Cyl.eTheta x‖
          + |A y| * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (CA) * dist x y ^ α
          + Ca * (Work.Cyl.radial y ^ α
              * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖) := by
          apply add_le_add
          · calc |A x - A y| * ‖Work.Cyl.eTheta x‖ ≤ |A x - A y| * 1 :=
                mul_le_mul_of_nonneg_left (norm_eTheta_le_one_prv x) (abs_nonneg _)
              _ = |A x - A y| := mul_one _
              _ = dist (A x) (A y) := by rw [Real.dist_eq]
              _ ≤ CA * dist x y ^ α := hcay x y
          · calc |A y| * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
                ≤ (Ca * Work.Cyl.radial y ^ α)
                    * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ :=
                  mul_le_mul_of_nonneg_right (hvanA y) (norm_nonneg _)
              _ = Ca * (Work.Cyl.radial y ^ α
                    * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖) := by ring
      _ ≤ CA * dist x y ^ α + Ca * (2 * dist x y ^ α) :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hw x y) hCa)
      _ = (CA + 2 * Ca) * dist x y ^ α := by ring
  calc ‖(A x - A y) • Work.Cyl.eTheta x + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖
      ≤ (CA + 2 * Ca) * dist x y ^ α := hcore
    _ ≤ ((smulEThetaConst CA Ca : NNReal) : ℝ)
          * dist x y ^ (((⟨α, hα.le⟩ : NNReal)) : ℝ) := by
        simp only [smulEThetaConst]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg dist_nonneg α)

end Work.FTS.Regularity
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.HJ.jetZsliceTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Filter Topology Set
open scoped Topology

namespace Work.FTS_RegExport.RXR1.HJ

theorem jetZsliceTendsto {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (hJet : Work.FTS.Regularity.Jet α S N h) (hα : 0 < α) {θ τ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc (0 : ℝ) S) :
    Filter.Tendsto (fun z : ℝ => h z θ τ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (h 0 θ τ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun z : ℝ => N * z ^ α)
    (Eventually.of_forall fun z => norm_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : (0:ℝ) ≤ z := le_of_lt hz
    have hb := hJet.zmod hz0 (le_refl (0:ℝ)) hθ hτ
    rw [Real.norm_eq_abs]
    rw [sub_zero, abs_of_nonneg hz0] at hb
    exact hb
  · have hcont : Continuous fun z : ℝ => N * z ^ α :=
      continuous_const.mul (Real.continuous_rpow_const hα.le)
    have h0 : N * (0:ℝ) ^ α = 0 := by
      rw [Real.zero_rpow (ne_of_gt hα), mul_zero]
    simpa [h0] using hcont.tendsto 0 |>.mono_left nhdsWithin_le_nhds

end Work.FTS_RegExport.RXR1.HJ
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.L12fAux.Fstar_dens_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L₁₂`-density of the profile `F_*` with exponent `pExp α = 3α`

Three facts about the profile `F_*(z,θ) = β (Γ(θ)/c(β)) 2z/(1+z)²` with `β = pExp α = 3α`:

* the angular density `θ ↦ K(θ) F_*(s,θ)/s` of `L₁₂` is integrable on `Iθ = [0,π/2]` for
  every `s > 0` (it is a constant multiple of the integrand `Γ(β)K` of the normalisation
  constant `c`);
* the radial density `s ↦ ∫_θ K(θ) F_*(s,θ)/s` is integrable on `(0,∞)`;
* that density is the elementary function `2β/(1+s)²`.

The last two are the `β = pExp α` instances of `Construction.L12dens_Fstar` and of
`MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn`.  The hypotheses `0 < α`, `α ≤ 1/3`
are exactly what is needed to discharge `0 < β` and `β ≤ 1`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXR5L.L12fAux

/-- The exponent `β = pExp α = 3α` of `F_*` satisfies `0 < β` under `0 < α`, and `β ≤ 1`
under `α ≤ 1/3`; both are the hypotheses needed to identify the `L₁₂`-density of `F_*`. -/
theorem Fstar_dens_facts {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    (∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.Construction.Fstar (Work.FTS.Regularity.pExp α) s θ / s)
      Work.Spaces.Iθ) ∧
    (MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)) (Set.Ioi 0)) ∧
    (∀ s : ℝ, 0 < s → Work.FM.L12dens Work.Spaces.K
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) s
      = 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2) := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  refine ⟨?_, ?_, ?_⟩
  · -- the angular density is a constant multiple of `Γ(β)K`, integrable on `Iθ`
    intro s _hs
    have hGK : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ * Work.Spaces.K θ)
        Work.Spaces.Iθ := Work.Spaces.CAux.integrableOn_GamK _ hβ
    have hscaled : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            * (Work.FM.Fstar s / s))
          * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ * Work.Spaces.K θ))
        Work.Spaces.Iθ := hGK.const_mul _
    refine hscaled.congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [Work.Construction.Fstar]
    ring
  · -- the radial density is `2β/(1+s)²`, integrable on `(0,∞)`
    change MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
      (Set.Ioi 0)
    exact Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hβ hβ1 0 le_rfl
  · -- the radial density is the elementary function `2β/(1+s)²`
    intro s hs
    have hkey := Work.Construction.L12dens_Fstar (α := Work.FTS.Regularity.pExp α) hβ hβ1 s
    have hFs : Work.FM.Fstar s / s = 2 / (1 + s) ^ 2 := by
      rw [Work.FM.Fstar]
      field_simp
    change Work.Construction.L12dens (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) s
      = 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
    rw [hkey, hFs]
    ring

end Work.FTS_RegExport.RXR5L.L12fAux
end
end
-- ===== merged: Submission.Work.R1G.vecResid_eq_scalar_smul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Work.Cyl
open Work.CoreResiduals.VorticityEquation

namespace Work.R1G


end Work.R1G
end
