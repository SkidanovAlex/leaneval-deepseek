import Mathlib
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.MuStepA
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_slot20_bound
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.SrdFork.EllWeakPos_DzIter_one_shift_fork
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.interp_lin_of_box =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Blocks

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# `Work.Blocks.interp_lin_of_box`

The mixed weighted interpolation estimate of the paper's §Elliptic Estimates in the general
(non-compactly-supported) case:

`α² ∫∫ (D_z∂_θG)² w² σ ≤ C (α⁴ ∫∫ (D_z²G)² w² σ + ∫∫ (∂_θ²G)² w² σ + α² ∫∫ (D_zG)² w² σ)`

for `G` of class `C^∞` on the open strip `(0,∞) × (-1, π/2+1)`, vanishing on the two angular
boundary lines, with the four `z`-slice integrability conditions `FourInt G` (which make the
four Bochner functionals honest numbers rather than the junk value `0`).

The proof is the composition of the two halves of the reduction that already exist in the
workspace:

* `Work.Blocks.interp_box_uniform_aux` (`interpol_mixed_box_proof.lean`) — the **box** case:
  the same inequality for `G` supported in a compact `[δ,R] ⊂ (0,∞)`, with a constant `C`
  uniform in `δ`, `R` and `G` (so the `∃ C` can be pulled outside the `∀ δ R`);
* `Work.Blocks.interp_truncation` (`interp_truncation.lean`) — the **truncation** step: from
  the box case for a fixed constant `C` (the logarithmic radial cut-offs
  `χ_k ↗ 1`, with the `O(1/log k)` truncation errors controlled by Fatou and the extra
  `FourInt` hypothesis), it produces the general case for the same `C`.

The only thing to check is that the quantifier order of the box hypothesis matches: the box
case is stated as `∀ α G, … → ∀ δ R, 0 < δ → δ < R → …`, while the truncation consumes
`∀ δ R, 0 < δ → δ < R → ∀ α G, …`.  Both are universally quantified hypotheses with no
dependencies between `δ, R` on the one side and `α, G` on the other, so they are the same
statement read in a different order.
-/


end Work.Blocks
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.transportWeakRR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

theorem transportWeakRR {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0,
          Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = ∫ p in Work.FTS.EllipticEst.Q0,
            F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) :
    Work.EllipticEst.InteriorRegularity.Q0.StripWeakRR
      (fun σ θ => (Work.EllipticEst.InteriorRegularity.Q0.VRR α Ψ σ θ : ℂ))
      (fun σ θ => (Work.EllipticEst.InteriorRegularity.Q0.GRR α F σ θ : ℂ)) :=
  transportWeakRR_of_pullback hα hΨ hweak
    (fun ψ h1 h2 h3 => pullbackExists hα h1 h2 h3)

end Work.EllipticEst.InteriorRegularity.Q0
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.Tower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap LineDeriv ContDiff

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The local Sobolev tower.** -/
theorem tower {V G : E2 → ℂ} (hV : Integrable V) (hG : Integrable G)
    (hGs : ∀ n : ℕ, ContDiff ℝ n G) {W : Set E2}
    (hweak : ∀ ψ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      Function.support ψ ⊆ W → ∫ x, V x * Kop ψ x = ∫ x, G x * ψ x)
    {x₀ : E2} {δ : ℝ} (hδ : 0 < δ) (hxδ : δ ≤ x₀ 1) (hyδ : δ ≤ Real.pi / 2 - x₀ 1)
    (hWball : Metric.closedBall x₀ (δ / 8) ⊆ W) (m : ℕ) :
    ∃ χ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n χ) ∧ HasCompactSupport χ ∧
      (∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Metric.closedBall x₀ ρ, χ x = 1) ∧
      ∀ (h : Integrable (fun x => χ x * V x)),
        TemperedDistribution.MemSobolev ((m : ℝ) + 2) 2 (Td (fun x => χ x * V x) h) := by
  classical
  set N : ℕ := m + 4 with hNdef
  set e : ℕ → ℝ := fun j => δ / (64 * 4 ^ N) * 4 ^ j with he
  have he_pos : ∀ j, 0 < e j := by
    intro j
    rw [he]
    positivity
  have he_succ : ∀ j, e (j + 1) = 4 * e j := by
    intro j
    simp only [he, pow_succ]
    ring
  have he_le : ∀ j ≤ N, e j ≤ e N := by
    intro j hj
    simp only [he]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) (by positivity)
  have he_N : e N = δ / 64 := by
    rw [he]
    field_simp
  have h3eN : 3 * e N ≤ δ / 8 := by
    rw [he_N]
    linarith
  have h8eN : 8 * e N < δ / 2 := by
    rw [he_N]
    linarith
  -- the balls `ball x₀ (3 e j)` lie in the strip and in `W`
  have hU_strip : ∀ j ≤ N, Metric.ball x₀ (3 * e j) ⊆ stripE := by
    intro j hj x hx
    rw [mem_stripE]
    exact mem_Ioo_of_mem_ball hδ hxδ hyδ
      (Metric.ball_subset_ball (by linarith [he_le j hj]) hx)
  have hU_W : ∀ j ≤ N, Metric.ball x₀ (3 * e j) ⊆ W := by
    intro j hj x hx
    apply hWball
    rw [Metric.mem_ball, dist_eq_norm] at hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h3 : 3 * e j ≤ 3 * e N := by linarith [he_le j hj]
    linarith
  -- the cut-off family
  let χ : ℕ → E2 → ℂ := fun j => cfun x₀ (e j) (he_pos j)
  have hχ_smooth : ∀ j (n : ℕ), ContDiff ℝ n (χ j) :=
    fun j n => cfun_contDiff x₀ (e j) (he_pos j) n
  have hχ_cc : ∀ j, HasCompactSupport (χ j) := fun j => cfun_hasCompactSupport x₀ (e j) (he_pos j)
  have hχ_ts : ∀ j, tsupport (χ j) = Metric.closedBall x₀ (2 * e j) :=
    fun j => cfun_tsupport x₀ (e j) (he_pos j)
  have hχ_one : ∀ j, ∀ x ∈ Metric.closedBall x₀ (e j), χ j x = 1 :=
    fun j x hx => cfun_one (he_pos j) hx
  have htsU : ∀ j, tsupport (χ j) ⊆ Metric.ball x₀ (3 * e j) := by
    intro j x hx
    rw [hχ_ts j, Metric.mem_closedBall, dist_eq_norm] at hx
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [he_pos j]
  have hsucc_one : ∀ j, ∀ x ∈ Metric.ball x₀ (3 * e j), χ (j + 1) x = 1 := by
    intro j x hx
    have hx' : ‖x - x₀‖ < 3 * e j := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    apply hχ_one (j + 1)
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h4 : e (j + 1) = 4 * e j := he_succ j
    have h5 : (0 : ℝ) < e j := he_pos j
    linarith
  have hmul_eq : ∀ j, (fun x => χ j x * (χ (j + 1) x * V x)) = fun x => χ j x * V x := by
    intro j
    funext x
    by_cases hx : χ j x = 0
    · simp [hx]
    · have hxU : x ∈ Metric.ball x₀ (3 * e j) :=
        htsU j (subset_closure (Function.mem_support.mpr hx))
      rw [hsucc_one j x hxU]
      ring
  -- integrability witnesses and the distributions `θ j`
  have hInt : ∀ j, Integrable (fun x => χ j x * V x) :=
    fun j => integrable_mul_of_cc hV (hχ_cc j) (hχ_smooth j)
  have hIntG : ∀ j, Integrable (fun x => χ j x * G x) :=
    fun j => integrable_mul_of_cc hG (hχ_cc j) (hχ_smooth j)
  let θ : ℕ → 𝓢'(E2, ℂ) := fun j => Td (fun x => χ j x * V x) (hInt j)
  have hθ_apply : ∀ j (ψ : 𝓢(E2, ℂ)), θ j ψ = ∫ x, ψ x • (χ j x * V x) :=
    fun j ψ => Td_apply _ _ ψ
  have hθ_eq : ∀ j, TemperedDistribution.smulLeftCLM ℂ (χ j) (θ (j + 1)) = θ j := by
    intro j
    ext ψ
    rw [TemperedDistribution.smulLeftCLM_apply_apply, hθ_apply (j + 1), hθ_apply j]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ((SchwartzMap.smulLeftCLM ℂ (χ j)) ψ) x • (χ (j + 1) x * V x)
      = ψ x • (χ j x * V x)
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (hasTemperateGrowth_of_cc (hχ_cc j) (hχ_smooth j))]
    simp only [smul_eq_mul]
    by_cases hx : χ j x = 0
    · simp [hx]
    · have hxU : x ∈ Metric.ball x₀ (3 * e j) :=
        htsU j (subset_closure (Function.mem_support.mpr hx))
      rw [hsucc_one j x hxU]
      ring
  -- the induction
  have hP : ∀ k, k ≤ N → TemperedDistribution.MemSobolev (-2 + (k : ℝ)) 2 (θ (N - k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero]
      have h := Td_memSobolev_neg_two (hInt N)
      have hm : (-2 : ℝ) + ((0 : ℕ) : ℝ) ≤ -2 := by norm_num
      exact h.mono hm
    | succ k ih =>
      intro hk
      have hkN : k ≤ N := by omega
      have hj1 : N - (k + 1) + 1 = N - k := by omega
      set j : ℕ := N - (k + 1) with hjdef
      have hIH : TemperedDistribution.MemSobolev (-2 + (k : ℝ)) 2 (θ (j + 1)) := by
        rw [hj1]
        exact ih hkN
      -- the tangent cut-off for the current step
      have hr4 : 0 < 4 * e j := by linarith [he_pos j]
      set tt : E2 → ℂ :=
        fun x => cfun x₀ (4 * e j) hr4 x * (Real.tan (x 1) : ℂ) with httdef
      have hcf_ts : tsupport (cfun x₀ (4 * e j) hr4) ⊆ Metric.ball x₀ (δ / 2) := by
        rw [cfun_tsupport]
        refine Metric.closedBall_subset_ball ?_
        have h := he_le j (by omega : j ≤ N)
        linarith
      have htt_smooth : ∀ n : ℕ, ContDiff ℝ n tt := by
        intro n
        rw [httdef]
        exact contDiff_mul_of_tsupport_subset (contDiffOn_tan_coord hδ hxδ hyδ n)
          Metric.isOpen_ball (cfun_contDiff x₀ (4 * e j) hr4) hcf_ts
      have htt_cc : HasCompactSupport tt := by
        rw [httdef]
        exact (cfun_hasCompactSupport x₀ (4 * e j) hr4).mul_right
      have htt_one : ∀ x ∈ Metric.ball x₀ (3 * e j), tt x = (Real.tan (x 1) : ℂ) := by
        intro x hx
        rw [Metric.mem_ball, dist_eq_norm] at hx
        have h4 : x ∈ Metric.closedBall x₀ (4 * e j) := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          linarith [he_pos j]
        show cfun x₀ (4 * e j) hr4 x * (Real.tan (x 1) : ℂ) = (Real.tan (x 1) : ℂ)
        rw [cfun_one hr4 h4, one_mul]
      -- the localized distributional equation
      have heq := localEqDist (V := V) (G := G) (W := W) hweak
        (hχ_cc j) (hχ_smooth j) (hχ_cc (j + 1)) (hχ_smooth (j + 1))
        (hχ_cc (j + 1)) (hχ_smooth (j + 1)) htt_cc htt_smooth
        Metric.isOpen_ball (htsU j) (hU_W j (by omega)) (fun x hx => hsucc_one j x hx)
        (fun x hx => hsucc_one j x hx) htt_one
        hV hG (hInt j) (hInt (j + 1)) (hIntG j)
      -- the source of the gain step
      set Gc : 𝓢'(E2, ℂ) :=
        (- Td (fun x => χ j x * G x) (hIntG j)
            + TemperedDistribution.smulLeftCLM ℂ (rho0 (χ j) tt) (θ (j + 1))
            + TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d0 (χ j) x)
                (LineDeriv.lineDerivOp e0 (θ (j + 1)))
            + TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d1 (χ j) x)
                (LineDeriv.lineDerivOp e1 (θ (j + 1)))) with hGcdef
      have heqG : Laplacian.laplacian (θ j)
          = Gc
            + TemperedDistribution.smulLeftCLM ℂ (fun x => 5 * χ (j + 1) x)
                (LineDeriv.lineDerivOp e0 (θ j))
            + TemperedDistribution.smulLeftCLM ℂ
                (fun x => -(χ (j + 1) x * tt x))
                (LineDeriv.lineDerivOp e1 (θ j))
            + TemperedDistribution.smulLeftCLM ℂ (fun x => -6 * χ (j + 1) x) (θ j) := by
        rw [hGcdef]
        exact heq
      have hGc_mem : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2 Gc := by
        rw [hGcdef]
        have h1 : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2
            (Td (fun x => χ j x * G x) (hIntG j)) :=
          Td_memSobolev_of_smooth_compact (hIntG j) ((hχ_cc j).mul_right)
            (fun n => (hχ_smooth j n).mul (hGs n)) _
        have h2 : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2
            (TemperedDistribution.smulLeftCLM ℂ (rho0 (χ j) tt) (θ (j + 1))) :=
          Q0.mulSob (hasCompactSupport_rho0 (hχ_cc j) (hχ_smooth j))
            (contDiff_rho0 (hχ_smooth j) htt_smooth) (hIH.mono (by linarith))
        have h3 : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2
            (TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d0 (χ j) x)
              (LineDeriv.lineDerivOp e0 (θ (j + 1)))) :=
          Q0.mulSob
            (hasCompactSupport_const_mul (hasCompactSupport_d0 (hχ_cc j) (hχ_smooth j)) 2)
            (fun n => contDiff_const.mul (contDiff_d0 (hχ_smooth j) n))
            (TemperedDistribution.MemSobolev.lineDerivOp (m := e0) hIH)
        have h4 : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2
            (TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d1 (χ j) x)
              (LineDeriv.lineDerivOp e1 (θ (j + 1)))) :=
          Q0.mulSob
            (hasCompactSupport_const_mul (hasCompactSupport_d1 (hχ_cc j) (hχ_smooth j)) 2)
            (fun n => contDiff_const.mul (contDiff_d1 (hχ_smooth j) n))
            (TemperedDistribution.MemSobolev.lineDerivOp (m := e1) hIH)
        exact ((h1.neg.add h2).add h3).add h4
      have hθ_mem : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2 (θ j) := by
        have h := Q0.mulSob (hχ_cc j) (hχ_smooth j) hIH
        rw [hθ_eq j] at h
        exact h.mono (by linarith)
      have hb_cc : HasCompactSupport (fun x => 5 * χ (j + 1) x) :=
        hasCompactSupport_const_mul (hχ_cc (j + 1)) 5
      have hb_sm : ∀ n : ℕ, ContDiff ℝ n (fun x => 5 * χ (j + 1) x) :=
        fun n => contDiff_const.mul (hχ_smooth (j + 1) n)
      have hb'_cc : HasCompactSupport (fun x => -(χ (j + 1) x * tt x)) :=
        ((hχ_cc (j + 1)).mul_right).neg
      have hb'_sm : ∀ n : ℕ, ContDiff ℝ n (fun x => -(χ (j + 1) x * tt x)) :=
        fun n => ((hχ_smooth (j + 1) n).mul (htt_smooth n)).neg
      have hc_cc : HasCompactSupport (fun x => -6 * χ (j + 1) x) :=
        hasCompactSupport_const_mul (hχ_cc (j + 1)) (-6)
      have hc_sm : ∀ n : ℕ, ContDiff ℝ n (fun x => -6 * χ (j + 1) x) :=
        fun n => contDiff_const.mul (hχ_smooth (j + 1) n)
      have hmain := gain_step (E := E2) (σ := -2 + (k : ℝ) - 1) (u := θ j) (G := Gc)
        (b := fun x => 5 * χ (j + 1) x)
        (b' := fun x => -(χ (j + 1) x * tt x))
        (c := fun x => -6 * χ (j + 1) x) e0 e1
        hb_cc hb_sm hb'_cc hb'_sm hc_cc hc_sm hGc_mem hθ_mem heqG
      have hk1 : (-2 + (k : ℝ) - 1) + 2 = -2 + ((k + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hk1] at hmain
      exact hmain
  -- conclusion
  have hfinal : TemperedDistribution.MemSobolev ((m : ℝ) + 2) 2 (θ 0) := by
    have h := hP N le_rfl
    rw [Nat.sub_self] at h
    have : (-2 + (N : ℝ)) = (m : ℝ) + 2 := by
      rw [hNdef]
      push_cast
      ring
    rwa [this] at h
  refine ⟨χ 0, hχ_smooth 0, hχ_cc 0, ?_, ?_⟩
  · exact ⟨e 0, he_pos 0, fun x hx => hχ_one 0 x hx⟩
  · intro h
    exact hfinal

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.DerivVanish =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
namespace Work.FTS.Apriori.Limit
set_option autoImplicit false
open Work.FTS.LocData (SmoothQuad)

/-! ## Small vanishing lemmas for the partial derivatives -/

theorem pz_eq_zero_of_forall_lt {W : ℝ → ℝ → ℝ} {A : ℝ} (hA : ∀ z θ, z < A → W z θ = 0) :
    ∀ z θ, z < A → Work.Spaces.pz W z θ = 0 := by
  intro z θ hz
  have hev : (fun z' => W z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hz] with z' hz'
    exact hA z' θ hz'
  rw [Work.Spaces.pz, Filter.EventuallyEq.deriv_eq hev]
  simp

theorem pz_eq_zero_of_forall_gt {W : ℝ → ℝ → ℝ} {B : ℝ} (hB : ∀ z θ, B < z → W z θ = 0) :
    ∀ z θ, B < z → Work.Spaces.pz W z θ = 0 := by
  intro z θ hz
  have hev : (fun z' => W z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hz] with z' hz'
    exact hB z' θ hz'
  rw [Work.Spaces.pz, Filter.EventuallyEq.deriv_eq hev]
  simp



theorem pth_eq_zero_of_forall_theta_lt {W : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : ∀ z θ, θ < C → W z θ = 0) : ∀ z θ, θ < C → Work.Spaces.pth W z θ = 0 := by
  intro z θ hθ
  have hev : (fun θ' => W z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hθ] with θ' hθ'
    exact hC z θ' hθ'
  rw [Work.Spaces.pth, Filter.EventuallyEq.deriv_eq hev]
  simp

theorem pth_eq_zero_of_forall_theta_gt {W : ℝ → ℝ → ℝ} {D : ℝ}
    (hD : ∀ z θ, D < θ → W z θ = 0) : ∀ z θ, D < θ → Work.Spaces.pth W z θ = 0 := by
  intro z θ hθ
  have hev : (fun θ' => W z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hθ] with θ' hθ'
    exact hD z θ' hθ'
  rw [Work.Spaces.pth, Filter.EventuallyEq.deriv_eq hev]
  simp
end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Profile.SliceDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Profile

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.Spaces










end Work.FTS.Apriori.Profile
end
end
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.zmollPthEq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.RopGen.Trace.ZmollAux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.EllSol.PkgK5.K5c (Qext thMoll zmoll sKer)
open Work.FTS.EllSol.EllPkgAux (sKerd Hxyc)

/-! ## A bound for compactly supported continuous kernels -/

/-- A continuous kernel vanishing outside `[-ε, ε]` with `ε > 0` is bounded on all of `ℝ`. -/
theorem exists_kernel_bound {k : ℝ → ℝ} (hk : Continuous k) {ε : ℝ} (hε0 : 0 < ε)
    (hvan : ∀ x : ℝ, ε < |x| → k x = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x : ℝ, |k x| ≤ M) ∧ (∀ x : ℝ, ε < |x| → k x = 0) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -ε) (b := ε)).exists_bound_of_continuousOn
    hk.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_, hvan⟩
  intro x
  by_cases hx : x ∈ Set.Icc (-ε) ε
  · have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · have hz : k x = 0 := by
      refine hvan x ?_
      rw [Set.mem_Icc, not_and_or] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    rw [hz, abs_zero]
    exact le_max_right _ _

/-! ## The packaged slice bound -/

/-- `kernelSliceBound` packaged along the parameter `t ↦ exp t`. -/
theorem kernel_slice_le (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {k : ℝ → ℝ} (hk : Continuous k) {ε M : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hM0 : 0 ≤ M) (hM : ∀ x : ℝ, |k x| ≤ M) (hvan : ∀ x : ℝ, ε < |x| → k x = 0) :
    ∀ (t θ' : ℝ), θ' ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) →
      |∫ s : ℝ, k (θ' - s) * Qext G (Real.exp t) s|
        ≤ 3 * M * ∫ s in Work.Spaces.Iθ, |Hxyc G t s| := by
  intro t θ' hθ'
  have h := kernelSliceBound G (Real.exp t)
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn G hT (Real.exp_pos t))
    hk hε0 hε1 hM0 hM hvan hθ'
  simpa only [Hxyc] using h

/-! ## The angular derivative of `zmoll` -/

/-- **The angular derivative of the log-radial mollification.** -/
theorem zmollPthEq (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hdom : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
      |Hxyc G t s|) MeasureTheory.volume)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.pth (zmoll G δ ε) z θ
      = ∫ t : ℝ, sKer δ (Real.log z - t)
          * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  -- bounds for the kernels
  obtain ⟨Mδ, hMδ0, hMδb, hMδv⟩ := exists_kernel_bound
    ((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous) hδ0
    (fun x hx => Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ0 (le_of_lt hx))
  obtain ⟨M₁, hM₁0, hM₁b, hM₁v⟩ := exists_kernel_bound
    ((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).continuous) hε0
    (fun x hx => Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 (le_of_lt hx))
  obtain ⟨M₂, hM₂0, hM₂b, hM₂v⟩ := exists_kernel_bound
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd ε) hε0
    (fun x hx => Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hε0 hx)
  -- a common bound `Mε` for both angular kernels
  set Mε : ℝ := max M₁ M₂ with hMεdef
  have hMε0 : 0 ≤ Mε := by rw [hMεdef]; exact le_max_of_le_left hM₁0
  have hMεKer : ∀ x : ℝ, |sKer ε x| ≤ Mε := fun x => by
    rw [hMεdef]; exact le_trans (hM₁b x) (le_max_left _ _)
  have hMεKerd : ∀ x : ℝ, |sKerd ε x| ≤ Mε := fun x => by
    rw [hMεdef]; exact le_trans (hM₂b x) (le_max_right _ _)
  have hkε : Continuous (sKer ε) :=
    (Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).continuous
  have hvanε : ∀ x : ℝ, ε < |x| → sKer ε x = 0 :=
    fun x hx => Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 (le_of_lt hx)
  have hkεd : Continuous (sKerd ε) :=
    Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd ε
  have hvanεd : ∀ x : ℝ, ε < |x| → sKerd ε x = 0 :=
    fun x hx => Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hε0 hx
  -- `θ` lies in the wider window on which `thMoll_hasDerivAt` is available
  have hθw : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := by
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hθ
    exact ⟨by linarith, by linarith⟩
  -- the auxiliary objects
  let Gfn : ℝ → ℝ := fun u : ℝ => ∫ s in Work.Spaces.Iθ, |Hxyc G u s|
  let K : Set ℝ := Set.Icc (Real.log z - δ) (Real.log z + δ)
  let bound : ℝ → ℝ := fun t : ℝ => Mδ * (3 * Mε) * K.indicator Gfn t
  let F : ℝ → ℝ → ℝ := fun θ' t : ℝ => sKer δ (Real.log z - t) * thMoll G ε (Real.exp t) θ'
  let F' : ℝ → ℝ → ℝ := fun θ' t : ℝ => sKer δ (Real.log z - t)
    * (∫ s : ℝ, sKerd ε (θ' - s) * Qext G (Real.exp t) s)
  have hKc : IsCompact K := isCompact_Icc
  have hKmeas : MeasurableSet K := measurableSet_Icc
  have hbound_int : Integrable bound MeasureTheory.volume := by
    have h : Integrable (K.indicator Gfn) MeasureTheory.volume :=
      (integrable_indicator_iff hKmeas).mpr (hdom.integrableOn_isCompact hKc)
    exact h.const_mul (Mδ * (3 * Mε))
  -- ## measurability of the sliced convolutions
  have hmeas_k : ∀ (k : ℝ → ℝ), Continuous k → (∀ x : ℝ, ε < |x| → k x = 0) →
      ∀ θ' : ℝ, θ' ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) →
      AEStronglyMeasurable (fun t : ℝ => sKer δ (Real.log z - t)
        * (∫ s : ℝ, k (θ' - s) * Hxyc G t s))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    intro k hk hvan θ' hθ'
    have hsm : AEStronglyMeasurable (fun t : ℝ => ∫ s : ℝ, k (θ' - s) * Hxyc G t s)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      hxycSliceAESM G hS hk hε0 hε1 hvan hθ'
    have hcont : Continuous (fun t : ℝ => sKer δ (Real.log z - t)) :=
      ((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous).comp
        (continuous_const.sub continuous_id)
    exact hcont.aestronglyMeasurable.mul hsm
  -- ## the small-window helper
  have hsmall : ∀ θ' : ℝ, θ' ∈ Set.Ioo (θ - 1 / 8) (θ + 1 / 8) →
      θ' ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := by
    intro θ' hθ'
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hθ'
    obtain ⟨h3, h4⟩ := Set.mem_Icc.mp hθ
    exact ⟨by linarith, by linarith⟩
  -- ## the seven hypotheses of the parametric integral theorem
  have hs : Set.Ioo (θ - 1 / 8) (θ + 1 / 8) ∈ 𝓝 θ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ θ' in 𝓝 θ, AEStronglyMeasurable (F θ')
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    refine Filter.Eventually.mono (Ioo_mem_nhds (show θ - 1 / 4 < θ by linarith)
      (show θ < θ + 1 / 4 by linarith)) ?_
    intro θ' hθ'
    have hθ'w : θ' ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := by
      obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hθ'
      obtain ⟨h3, h4⟩ := Set.mem_Icc.mp hθ
      exact ⟨by linarith, by linarith⟩
    exact hmeas_k (sKer ε) hkε hvanε θ' hθ'w
  have hF_int : Integrable (F θ) MeasureTheory.volume := by
    refine Integrable.mono' hbound_int (hF_meas.self_of_nhds) (Filter.Eventually.of_forall ?_)
    intro t
    show ‖sKer δ (Real.log z - t) * thMoll G ε (Real.exp t) θ‖
      ≤ Mδ * (3 * Mε) * K.indicator Gfn t
    by_cases ht : t ∈ K
    · rw [Set.indicator_of_mem ht]
      have h1 : |∫ s : ℝ, sKer ε (θ - s) * Qext G (Real.exp t) s| ≤ 3 * Mε * Gfn t :=
        kernel_slice_le G hT hkε hε0 hε1 hMε0 hMεKer hvanε t θ hθw
      have h1' : |thMoll G ε (Real.exp t) θ| ≤ 3 * Mε * Gfn t := h1
      rw [Real.norm_eq_abs, abs_mul]
      calc |sKer δ (Real.log z - t)| * |thMoll G ε (Real.exp t) θ|
          ≤ Mδ * (3 * Mε * Gfn t) := mul_le_mul (hMδb _) h1' (abs_nonneg _) hMδ0
        _ = Mδ * (3 * Mε) * Gfn t := by ring
    · rw [Set.indicator_of_notMem ht]
      have hzK : δ ≤ |Real.log z - t| := by
        have hmem : t ∉ Set.Icc (Real.log z - δ) (Real.log z + δ) := ht
        rw [Set.mem_Icc, not_and_or] at hmem
        rcases hmem with h | h
        · rw [abs_of_pos (by linarith)]
          linarith
        · rw [abs_of_neg (by linarith)]
          linarith
      rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ0 hzK, zero_mul, norm_zero]
      simp
  have hF'_meas : AEStronglyMeasurable (F' θ)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    hmeas_k (sKerd ε) hkεd hvanεd θ hθw
  have h_bound : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ x ∈ Set.Ioo (θ - 1 / 8) (θ + 1 / 8), ‖F' x t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall (fun t x hx => ?_)
    show ‖sKer δ (Real.log z - t)
        * (∫ s : ℝ, sKerd ε (x - s) * Qext G (Real.exp t) s)‖
      ≤ Mδ * (3 * Mε) * K.indicator Gfn t
    by_cases ht : t ∈ K
    · rw [Set.indicator_of_mem ht]
      have h1 : |∫ s : ℝ, sKerd ε (x - s) * Qext G (Real.exp t) s| ≤ 3 * Mε * Gfn t :=
        kernel_slice_le G hT hkεd hε0 hε1 hMε0 hMεKerd hvanεd t x (hsmall x hx)
      rw [Real.norm_eq_abs, abs_mul]
      calc |sKer δ (Real.log z - t)| * |∫ s : ℝ, sKerd ε (x - s) * Qext G (Real.exp t) s|
          ≤ Mδ * (3 * Mε * Gfn t) := mul_le_mul (hMδb _) h1 (abs_nonneg _) hMδ0
        _ = Mδ * (3 * Mε) * Gfn t := by ring
    · rw [Set.indicator_of_notMem ht]
      have hzK : δ ≤ |Real.log z - t| := by
        have hmem : t ∉ Set.Icc (Real.log z - δ) (Real.log z + δ) := ht
        rw [Set.mem_Icc, not_and_or] at hmem
        rcases hmem with h | h
        · rw [abs_of_pos (by linarith)]
          linarith
        · rw [abs_of_neg (by linarith)]
          linarith
      rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ0 hzK, zero_mul, norm_zero]
      simp
  have h_diff : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ x ∈ Set.Ioo (θ - 1 / 8) (θ + 1 / 8), HasDerivAt (F · t) (F' x t) x := by
    refine Filter.Eventually.of_forall (fun t x hx => ?_)
    have hxw : x ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := hsmall x hx
    have hd := Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt
      (Q := fun s : ℝ => Qext G (Real.exp t) s)
      (Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn G hT (Real.exp_pos t))
      hε0 hε1 hMεKerd hxw
    have h2 := hd.const_mul (sKer δ (Real.log z - t))
    show HasDerivAt (fun θ' : ℝ => sKer δ (Real.log z - t) * thMoll G ε (Real.exp t) θ')
      (sKer δ (Real.log z - t)
        * (∫ s : ℝ, sKerd ε (x - s) * Qext G (Real.exp t) s)) x
    exact h2
  -- ## the parametric integral theorem
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (F := F) (F' := F') (x₀ := θ) (s := Set.Ioo (θ - 1 / 8) (θ + 1 / 8))
    (bound := bound)
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hderiv := hmain.2
  show deriv (fun θ' : ℝ => ∫ a, F θ' a ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) θ
    = ∫ t : ℝ, sKer δ (Real.log z - t) * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s)
  rw [hderiv.deriv]
  rfl

end Work.FTS.ClassC.RopGen.Trace.ZmollAux
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.E2hat_RegQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `RegQ`-closure under the `D_z`-commutator defect `Ê₂`

`Work.FTS.CoercivityFix.E2hat f = (2zf + 3z·D_θf)/(1+z)²` is the `D_z`-commutator defect of the
clean operator `Lhat = 𝓛 − Transport` (`D_z (Lhat f) = Lhat (D_z f) + Ê₂ f`), and the modified
induction of the coercivity node runs on the interior class `RegQ` (`Work.FTS.Vocab`):

  `RegQ α k f = SmoothQuad f ∧ HkMem α k f ∧ BdryTraces α k f`.

This module proves the port

  `RegQ α (n+1) f → RegQ α n (Ê₂ f)`,

the `hregE2` slot of `Work.FTS.CoercivityFix.StepCoer.step_coer`.

The defect is a *radial multiplier* times a linear combination of `f` and `D_θf`:

  `Ê₂ f = φ(z)·(2f + 3·D_θf) = 2·(φ·f) + 3·(φ·D_θf)`,   `φ(z) = z/(1+z)²`.

Every `Zop`-iterate of `φ` (`Zop u = z ∂_z u`) is bounded on `(0,∞)` (`E2Bound.zop_phi_bound`:
under the Möbius chart `z ↦ (z-1)/(z+1)`, `φ` becomes a polynomial in the chart variable, which
maps `(0,∞)` into `(-1,1)`), so the multiplier `φ` preserves the three components of the class:

* `SmoothQuad` — `φ` is `C^∞` on `(-1,∞)` (`E2Bound.contDiffOn_zDiv`) and `SmoothQuad` is closed
  under products (`LocData.smoothQuad_mul`);
* `HkMem` — the Leibniz slots of `HkIntegrand α n (φ·g)` are the slots of `HkIntegrand α n g`
  with coefficients bounded by `C(n)(1+K)²` (`E2Bound.HkIntegrand_zmul_le`), which is exactly a
  pointwise *majorant* on the open quadrant; the null set `{θ = 0} ∪ {θ = π/2} ∪ {z = 0}` is
  handled by the a.e. membership criterion `EllipticEst.HkMem_of_majorant_ae`;
* `BdryTraces` — the mixed derivatives expand by the `z`-only Leibniz rule
  `E2Bound.mixed_zmul`,
  `mixed b a (φ·g) = Σ_{c≤b} C(b,c)·(Zop^c φ)·mixed (b-c) a g`, so the boundary limits of the
  product are finite combinations of those of `g`, squeezed by the boundedness of the multiplier
  (`tendsto_wsum_sq_le`, `tendsto_ssum_sq_le` below).

The three pieces assemble through the `RegQ`-algebra of `Work.FTS.Apriori.RegQApi`
(`regQ_add`, `regQ_smul`, `regQ_mono`) together with the `D_θ`-port
`QuadPorts.RegQ_dth`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.CoercivityFix.Assembly

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-! ## The radial multiplier `φ(z) = z/(1+z)²` -/



/-! ## The two squeezing lemmas for the boundary traces of a finite sum

Both have the same shape: a finite combination `Σ_c co_c·(ψ_c·m_c)` of terms whose *weighted
squares* tend to `0` (the traces of the summands), with multipliers `ψ_c` bounded by `K`, has
weighted square tending to `0` as well.  The weights `z·w(z)²` and `sin(2θ)^{1-γ}` are
nonnegative on the relevant sets, so the Cauchy–Schwarz inequality
`(Σ_c x_c)² ≤ card · Σ_c x_c²` applies verbatim. -/



/-! ## `HkMem` is preserved by the multiplier `φ` -/


/-! ## `BdryTraces` is preserved by the multiplier `φ` -/


/-! ## The class `RegQ` is closed under the multiplier `φ` -/



end Work.FTS.CoercivityFix.Assembly
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.H1IP_le_self_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false


end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.HkSq_succ_le_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)

/-! ## Elementary sum lemmas (local copies of the private helpers of `Work.Coercivity`) -/



/-! ## The pointwise integrand comparison in the interior class -/


/-! ## The honest memberships -/



/-! ## The target lemma -/


end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.RegQ_dth_ge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Assembly


end Work.FTS.CoercivityFix.Assembly
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.block_calc_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## Continuity of the weights on the open quadrant -/



/-! ## Continuity of the four blocks -/





/-! ## Vanishing on the axis `z = 0` (because `w 0 = 0`) -/





/-! ## The abstract block lemma -/


/-! ## The four blocks -/


end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1.IntFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Tools -/

theorem iz_prod_restrict : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]

theorem iz_ae_restrict : (MeasureTheory.volume.restrict Work.Spaces.Iz)
    = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  refine MeasureTheory.Measure.restrict_congr_set ?_
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · have h : Work.Spaces.Iz \ Set.Ioi 0 = {0} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, Work.Spaces.Iz,
        Set.mem_Ici, not_lt]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
      · rintro rfl; exact ⟨le_refl 0, le_refl 0⟩
    rw [h, Real.volume_singleton]
  · have h : Set.Ioi (0 : ℝ) \ Work.Spaces.Iz = ∅ := by
      rw [Work.Spaces.Iz, Set.sdiff_eq_empty]
      exact Set.Ioi_subset_Ici_self
    rw [h, MeasureTheory.measure_empty]

/-- The elementary `2|ab| ≤ a² + b²`, weighted by `ρ ≥ 0`. -/
theorem two_abs_mul_le (a b ρ : ℝ) (hρ : 0 ≤ ρ) :
    2 * (|a * b| * ρ) ≤ a ^ 2 * ρ + b ^ 2 * ρ := by
  have h : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
    rw [abs_mul, ← sq_abs a, ← sq_abs b]
    nlinarith [sq_nonneg (|a| - |b|)]
  nlinarith [h, hρ]

/-- `|abρ| ≤ a²ρ + b²ρ` for `ρ ≥ 0`. -/
theorem abs_mul_mul_le (a b ρ : ℝ) (hρ : 0 ≤ ρ) : |a * b * ρ| ≤ a ^ 2 * ρ + b ^ 2 * ρ := by
  have h := two_abs_mul_le a b ρ hρ
  have h1 : 0 ≤ a ^ 2 * ρ := mul_nonneg (sq_nonneg a) hρ
  have h2 : 0 ≤ b ^ 2 * ρ := mul_nonneg (sq_nonneg b) hρ
  rw [abs_mul, abs_of_nonneg hρ]
  linarith [h, h1, h2]

/-- Lifting an a.e. statement in the angle to the product measure on the quadrant. -/
theorem ae_prod_snd_mem {t : Set ℝ} (ht : MeasurableSet t)
    (h : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ t) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      p.2 ∈ t :=
  ((MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
    (s := Set.univ ×ˢ t) (MeasurableSet.univ.prod ht)).mpr
    (Filter.Eventually.of_forall fun _ => h.mono
      (fun y hy => ⟨Set.mem_univ _, hy⟩))).mono (fun p hp => hp.2)

/-- Lifting an a.e. statement in the radial variable to the product measure on the quadrant. -/
theorem ae_prod_fst_mem {s : Set ℝ} (hs : MeasurableSet s)
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ s) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      p.1 ∈ s :=
  ((MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
    (s := s ×ˢ Set.univ) (hs.prod MeasurableSet.univ)).mpr
    (h.mono (fun z hz => Filter.Eventually.of_forall
      (fun θ => ⟨hz, Set.mem_univ θ⟩)))).mono (fun p hp => hp.1)

theorem ae_prod_fst_pos :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 < p.1 := by
  have h1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Set.Ioi (0 : ℝ) := by
    rw [iz_ae_restrict]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  exact ae_prod_fst_mem (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi h1

theorem ae_prod_snd_mem_Ioo :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Set.Ioo 0 (π / 2) :=
  ae_prod_snd_mem measurableSet_Ioo ae_restrict_Iθ_mem_Ioo



/-- Sum of two `IntegrableOn` functions on the quadrant. -/
theorem integrableOn_add_Q {g h : Fn}
    (hg : MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hh : MeasureTheory.IntegrableOn (Function.uncurry h) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => g z θ + h z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.IntegrableOn]
  exact (hg.add hh).congr (Filter.Eventually.of_forall (fun p => by
    rcases p with ⟨z, θ⟩; rfl))

/-- Multiplication of an `IntegrableOn` function on the quadrant by the bounded factor
`1/(1+z)`. -/
theorem integrableOn_div_one_add_Q {g : Fn}
    (hg : MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => g z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.IntegrableOn]
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Function.uncurry g p * (1 + p.1)⁻¹)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    hg.aestronglyMeasurable.mul
      (((measurable_const.add measurable_fst).inv).aestronglyMeasurable)
  have hae : ∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)), 0 ≤ p.1 :=
    (MeasureTheory.ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)).mono
      (fun p hp => hp.1)
  have hmain : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Function.uncurry g p * (1 + p.1)⁻¹)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    refine hg.norm.mono' haesm ?_
    filter_upwards [hae] with p hp1
    rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + p.1)⁻¹)]
    calc ‖Function.uncurry g p‖ * (1 + p.1)⁻¹
        ≤ ‖Function.uncurry g p‖ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [inv_le_one₀ (by linarith : (0 : ℝ) < 1 + p.1)]
          linarith
      _ = ‖Function.uncurry g p‖ := mul_one _
  refine hmain.congr (Filter.Eventually.of_forall (fun p => ?_))
  rcases p with ⟨z, θ⟩
  rfl

/-- The product of two `L²`-blocks is integrable (`2|ab| ≤ a² + b²`); the a.e. strong
measurability of the product comes from continuity on the open quadrant. -/
theorem integrableOn_mul_of_sq_Q {ρ φ ψ : Fn}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2 * ψ p.1 p.2 * ρ p.1 p.2) Qd)
    (hρ : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => φ z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => ψ z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => φ z θ * ψ z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.IntegrableOn]
  have hmaj : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (φ p.1 p.2 ^ 2 * ρ p.1 p.2 + ψ p.1 p.2 ^ 2 * ρ p.1 p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    (h1.add h2).congr (Filter.Eventually.of_forall (fun p => by
      rcases p with ⟨z, θ⟩; rfl))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => φ z θ * ψ z θ * ρ z θ))
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    have h := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    rwa [iz_prod_restrict] at h
  refine hmaj.mono' haesm ?_
  have hmem : ∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc) |>.mono
      (fun p hp => hp.2)
  filter_upwards [hmem] with p hp
  have := abs_mul_mul_le (φ p.1 p.2) (ψ p.1 p.2) (ρ p.1 p.2) (hρ p.1 p.2 hp)
  rwa [Function.uncurry_apply_pair, Real.norm_eq_abs]

/-- Each summand of the `ℋ^k`-integrand, squared and weighted, is jointly integrable. -/
theorem joint_of_le_HkIntegrand (α : ℝ) (k : ℕ) {f A : Fn} (hm : Work.Spaces.HkMem α k f)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2) Qd)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => (A z θ) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hI2 := i2Mem_sq_of_le α k hm hcont hle
  have hAE : MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun z θ => (A z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (A z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hI2.1
  have hjoint := (Work.Spaces.integrable_prod_of_iterated (fun z θ => sq_nonneg _) hAE hslice
    hI2.2).1
  rw [MeasureTheory.IntegrableOn, ← iz_prod_restrict]
  exact hjoint

/-- Domination of an integrand by another whose a.e. bound is known, with the minorant
continuous on the open quadrant. -/
theorem integrableOn_of_le_Q {g h : Fn} (hcont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) Qd)
    (hh : MeasureTheory.IntegrableOn (Function.uncurry h) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hle : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), |g p.1 p.2| ≤ h p.1 p.2) :
    MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hh' : MeasureTheory.Integrable (Function.uncurry h)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact hh
  have haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hle' : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ‖Function.uncurry g p‖ ≤ h p.1 p.2 := by
    filter_upwards [hle] with p hp
    rwa [Function.uncurry_apply_pair, Real.norm_eq_abs]
  have hmain := hh'.mono' haesm hle'
  rw [MeasureTheory.IntegrableOn, ← iz_prod_restrict]
  exact hmain

/-- An `IntegrableOn` function on the quadrant has integrable `θ`-slices for a.e. angle. -/
theorem ae_slice_of_integrableOn {g : Fn}
    (hg : MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun z => g z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hg' : MeasureTheory.Integrable (Function.uncurry g)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact hg
  exact hg'.prod_left_ae

/-! ## Continuity of the blocks on the open quadrant -/

/-- The weight `w²` (no angular factor) is continuous on the open quadrant. -/
theorem continuousOn_w2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by
    funext p; rfl
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2

theorem continuousOn_Rho (β : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Rho β p.1 p.2) Qd := by
  have hsinpos : ∀ p ∈ Qd, 0 < Real.sin (2 * p.2) :=
    fun p hp =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2) Qd :=
    continuousOn_w2
  have hsig : ContinuousOn (fun p : ℝ × ℝ => sig β p.2) Qd := by
    have hfun : (fun p : ℝ × ℝ => sig β p.2)
        = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-β) := by
      funext p; rfl
    rw [hfun]
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Rho β p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2 * sig β p.2 := rfl
  rw [hfun]
  exact hw.mul hsig




/-- The weight `Rho β` is nonnegative on the closed angular interval. -/
theorem Rho_nonneg (β : ℝ) : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ Rho β z θ :=
  fun z θ hθ => by
    rw [Rho, sig]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_nonneg_of_mem_Iθ hθ) _)

theorem w2_nonneg : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ Work.Spaces.w z ^ 2 :=
  fun _ _ _ => sq_nonneg _

/-! ## The weighted squares -/



/-- The `η`-weight is dominated by the `γ`-weight on the *whole* closed angular interval. -/
theorem sig_eta_le_sig_gam_Iθ (α : ℝ) (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    sig Work.Spaces.eta θ ≤ sig (Work.Spaces.gam α) θ := by
  rcases eq_or_lt_of_le (sin_nonneg_of_mem_Iθ hθ) with h | h
  · simp only [sig]
    rw [← h, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta) ≠ 0),
      Real.zero_rpow (show -(Work.Spaces.gam α) ≠ 0 by
        have : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
        linarith)]
  · refine sig_eta_le_sig_gam α hα ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · exfalso
        rw [← h0, mul_zero, Real.sin_zero] at h
        exact lt_irrefl 0 h
      · exact h0
    · rcases eq_or_lt_of_le hθ.2 with h0 | h0
      · exfalso
        rw [h0, show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi] at h
        exact lt_irrefl 0 h
      · exact h0

/-- The `η`-weight is dominated by the `γ`-weight. -/
theorem Rho_eta_le_Rho_gam (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Rho Work.Spaces.eta z θ ≤ Rho (Work.Spaces.gam α) z θ := by
  simp only [Rho, sig]
  exact mul_le_mul_of_nonneg_left (sig_eta_le_sig_gam_Iθ α hα hθ) (sq_nonneg _)

/-- The plain radial weight is dominated by the `η`-weight on the open interval. -/
theorem w2_le_Rho_eta (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z ^ 2 ≤ Rho Work.Spaces.eta z θ := by
  have h := mul_le_mul_of_nonneg_left (one_le_sig_eta hθ) (sq_nonneg (Work.Spaces.w z))
  simpa only [Rho, sig, mul_one] using h

/-- The plain radial weight is dominated by the `γ`-weight on the open interval. -/
theorem w2_le_Rho_gam (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z ^ 2 ≤ Rho (Work.Spaces.gam α) z θ :=
  le_trans (w2_le_Rho_eta z θ hθ)
    (Rho_eta_le_Rho_gam α hα z θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)




/-! ## The `𝓛`- and transport pairings -/





/-- `Lhat u · u · ρ` is integrable when `𝓛u·u·ρ` and the transport pairing are. -/
theorem intLhat_of {u : Fn} {ρ : Fn}
    (hL : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hT : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.Transport u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.Lhat u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine (hL.sub hT).congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Pi.sub_apply, Work.FTS.CoercivityFix.Lhat]
  ring

/-- The `η`-weighted transport pairing of `u` (in the `wip` normalisation) is integrable as soon
as the corresponding `hint` is. -/
theorem intTransport_of {u : Fn} {ρ : Fn}
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ * ρ z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.Transport u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine (hint.const_mul 3).congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Work.Coercivity.Transport]
  ring

/-- The `D_z`-commutator defect `Ê₂f·D_zf·ρ` is integrable, from the pointwise bound
`|Ê₂f| ≤ (2|f| + 3|D_θf|)/4` and the three weighted squares. -/
theorem intE2hat_of {f : Fn} {ρ : Fn}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2
      * Work.Spaces.Dz f p.1 p.2 * ρ p.1 p.2) Qd)
    (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ ^ 2 * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dz f z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h3 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth f z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat f z θ
        * Work.Spaces.Dz f z θ * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hmaj : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (f z θ ^ 2 / 4 + 5 * (Work.Spaces.Dz f z θ) ^ 2 / 8
        + 3 * (Work.Spaces.Dth f z θ) ^ 2 / 8) * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have ha : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        (f z θ ^ 2 / 4) * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      (h1.const_mul (1 / 4)).congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => by
          rcases p with ⟨z, θ⟩; simp only [Function.uncurry_apply_pair]; ring))
    have hb : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        (5 * (Work.Spaces.Dz f z θ) ^ 2 / 8) * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      (h2.const_mul (5 / 8)).congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => by
          rcases p with ⟨z, θ⟩; simp only [Function.uncurry_apply_pair]; ring))
    have hc : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        (3 * (Work.Spaces.Dth f z θ) ^ 2 / 8) * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      (h3.const_mul (3 / 8)).congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => by
          rcases p with ⟨z, θ⟩; simp only [Function.uncurry_apply_pair]; ring))
    refine (integrableOn_add_Q ha (integrableOn_add_Q hb hc)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem (measurableSet_Ici.prod measurableSet_Icc)
      (fun p hp => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair]
    ring
  refine integrableOn_of_le_Q hcont hmaj ?_
  have hmem : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ :=
    ae_prod_snd_mem measurableSet_Icc (MeasureTheory.ae_restrict_mem measurableSet_Icc)
  filter_upwards [hmem, ae_prod_fst_pos] with p hp hzpos
  rcases p with ⟨z, θ⟩
  have hE2 := Work.FTS.CoercivityFix.E2hat_abs_le f (z := z) (θ := θ) (le_of_lt hzpos)
  have hf2 : 0 ≤ f z θ ^ 2 := sq_nonneg _
  have hd2 : 0 ≤ (Work.Spaces.Dz f z θ) ^ 2 := sq_nonneg _
  have ht2 : 0 ≤ (Work.Spaces.Dth f z θ) ^ 2 := sq_nonneg _
  have hρ := hρnn z θ hp
  have h1' : |f z θ| * |Work.Spaces.Dz f z θ| ≤ (f z θ ^ 2 + (Work.Spaces.Dz f z θ) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|f z θ| - |Work.Spaces.Dz f z θ|), sq_abs (f z θ),
      sq_abs (Work.Spaces.Dz f z θ)]
  have h2' : |Work.Spaces.Dth f z θ| * |Work.Spaces.Dz f z θ|
      ≤ ((Work.Spaces.Dth f z θ) ^ 2 + (Work.Spaces.Dz f z θ) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|Work.Spaces.Dth f z θ| - |Work.Spaces.Dz f z θ|),
      sq_abs (Work.Spaces.Dth f z θ), sq_abs (Work.Spaces.Dz f z θ)]
  have hkey : |Work.FTS.CoercivityFix.E2hat f z θ * Work.Spaces.Dz f z θ|
      ≤ f z θ ^ 2 / 4 + 5 * (Work.Spaces.Dz f z θ) ^ 2 / 8
        + 3 * (Work.Spaces.Dth f z θ) ^ 2 / 8 := by
    calc |Work.FTS.CoercivityFix.E2hat f z θ * Work.Spaces.Dz f z θ|
        = |Work.FTS.CoercivityFix.E2hat f z θ| * |Work.Spaces.Dz f z θ| := abs_mul _ _
      _ ≤ ((2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) / 4) * |Work.Spaces.Dz f z θ| := by
          refine mul_le_mul_of_nonneg_right hE2 (abs_nonneg _)
      _ = (2 * |f z θ| * |Work.Spaces.Dz f z θ| / 4)
            + (3 * |Work.Spaces.Dth f z θ| * |Work.Spaces.Dz f z θ| / 4) := by ring
      _ ≤ (2 * ((f z θ ^ 2 + (Work.Spaces.Dz f z θ) ^ 2) / 2) / 4)
            + (3 * ((Work.Spaces.Dth f z θ) ^ 2 + (Work.Spaces.Dz f z θ) ^ 2) / 2 / 4) := by
          have e1 : 2 * |f z θ| * |Work.Spaces.Dz f z θ|
              = 2 * (|f z θ| * |Work.Spaces.Dz f z θ|) := by ring
          have e2 : 3 * |Work.Spaces.Dth f z θ| * |Work.Spaces.Dz f z θ|
              = 3 * (|Work.Spaces.Dth f z θ| * |Work.Spaces.Dz f z θ|) := by ring
          rw [e1, e2]
          have := mul_le_mul_of_nonneg_left h1' (show (0:ℝ) ≤ 2 by norm_num)
          have := mul_le_mul_of_nonneg_left h2' (show (0:ℝ) ≤ 3 by norm_num)
          linarith
      _ = f z θ ^ 2 / 4 + 5 * (Work.Spaces.Dz f z θ) ^ 2 / 8
            + 3 * (Work.Spaces.Dth f z θ) ^ 2 / 8 := by ring
  rw [abs_mul, abs_of_nonneg hρ]
  calc |Work.FTS.CoercivityFix.E2hat f z θ * Work.Spaces.Dz f z θ| * ρ z θ
      ≤ (f z θ ^ 2 / 4 + 5 * (Work.Spaces.Dz f z θ) ^ 2 / 8
          + 3 * (Work.Spaces.Dth f z θ) ^ 2 / 8) * ρ z θ :=
        mul_le_mul_of_nonneg_right hkey hρ
    _ = _ := rfl


end Work.FTS.CoercivityFix.Coer1
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_HkSq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.E2Bound

set_option autoImplicit false



/- **The requested unrestricted statement is FALSE for `α < -1/10`** — it is true for `α ≥ -1/10`
(`E2hat_HkSq_le_of_ge`), and it fails for `α < -1/10` already at `n = 0`.  The statement is
kept here, unchanged, for the record, but no proof is given; the counterexample:

Let `γ = 1 + α/10 < η = 99/100`, `θ_c(z) := (log z)^{-s}` with `s > 0` (so `θ_c(z) → 0` as
`z → ∞`), `δ_N(z) := θ_c(z)·z^{-N}`, and let `g` be a smooth bump supported in `(-1/2, 1/2)`.
For `Φ(z) := z^{-1}(log z)^{-a}` with `a ∈ (1 - s(η-γ), 1]` put
`A_N(z)² := Φ(z)·δ_N(z)·θ_c(z)^{η-2}` and
`f_N(z,θ) := A_N(z)·g((θ - θ_c(z))/δ_N(z))` (times a smooth cut-off supported in `z ≥ 3`).

* `f_N ∈ RegQ α 1`: the three `ℋ¹`-conditions of `HkMem α 1 f_N` become
  `∫_z z^{-1-2N}(log z)^{-a}`, `c∫_z z^{-1}(log z)^{-a-2}` and
  `c∫_z z^{-1}(log z)^{-a-s(η-γ)}`, all finite, while `SmoothQuad` and `BdryTraces` are
  immediate from the cut-offs (the bump's support stays inside `(0, π/2)` and leaves every
  fixed angle as `z → ∞`).
* The `θ`-slice of the `ℋ⁰`-integrand of `Ê₂ f_N` is `≍ 36Φ(z)`: a derivative of a bump of
  width `δ_N` costs `δ_N^{-1}`, and the factors `θ_c^{η-2}` (from `A_N²`) and `θ^{-η}` cancel.
  Since `φ(z)²w(z)² = 1/z²`, this gives `HkSq α 0 (Ê₂ f_N) = 36m∫_3^∞ z^{-3}(log z)^{-a} dz > 0`,
  a positive constant *independent of `N`*.
* The `θ`-slice of the `ℋ⁰`-integrand of `D_θ f_N` is `≍ 4mΦ(z)`, whose `z`-integral
  `∫_z w²Φ = ∫_z (1+z)^4z^{-4}·z^{-1}(log z)^{-a}` diverges (as `a ≤ 1`), so
  `HkSq α 0 (D_θ f_N) = 0` by the junk-value convention of the Bochner integral.
* `HkSq α 0 f_N = ∫_z z^{-1-2N}(log z)^{-a} → 0` as `N → ∞` (the narrowness factor
  `δ_N² = θ_c²z^{-2N}`).

Hence for every `Cn` there is `N` violating the inequality, so the statement is false as soon
as the hypothesis `α ≥ -1/10` is dropped.  The mechanism is exactly the weight mismatch
`η > γ`: the right-hand side only sees `D_θ f` through `η`-weighted pure slots whose mass is
suppressed by `δ_N²`, while the defect `Ê₂ f` carries the extra factor `φ(z)² = z²/(1+z)^4`
that compensates the radial weight `w²` and leaves `1/z²`.  The correct form of the lemma is
`E2hat_HkSq_le_of_ge`, whose range contains the paper's `α ∈ (0, α₂]`. -/
/- The unrestricted form (all `α`) is **false**: see the counterexample documented above —
   the hypothesis `α ≥ -1/10` cannot be dropped.  The usable form is `E2hat_HkSq_le_of_ge`,
   whose range contains the paper's `α ∈ (0, α₂]`.  (The false statement is deliberately not
   retained here.) -/
end Work.FTS.CoercivityFix.E2Bound
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.PsiMul.BdryTraces_psi_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.PsiMul

set_option maxHeartbeats 1000000

/-! ## The pointwise bound -/


/-! ## The four traces -/


end Work.FTS.CoercivityFix.PsiMul
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.PsiMul.HkMem_psi_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.PsiMul

set_option autoImplicit false



end Work.FTS.CoercivityFix.PsiMul
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.StepCoer.step_coer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.StepCoer

open Work.FTS.Nonlin (RegQ)



end Work.FTS.CoercivityFix.StepCoer
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.Dz_LGammaT_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

set_option autoImplicit false

/-! ## The `z`-derivative of the transfer defect `Corr` -/

/-- The `z`-slice of the transfer defect `Corr`: since `Corr α f z θ = Γ(θ)·radA α f z`
(`Corr_eq_radA`), differentiating in `z` multiplies the radial derivative by `Γ(θ)`.
The derivative of `radA` is `radS/z` (`Transfer.hasDerivAt_radA`). -/
theorem hasDerivAt_Corr_slice (α : ℝ) (f : ℝ → ℝ → ℝ) (hfH : Work.Coercivity.HardyHyp f)
    {z θ : ℝ} (hz : 0 < z) :
    HasDerivAt (fun t => Work.FTS.CoercivityFix.Corr α f t θ)
      (Work.Spaces.Gam α θ * (radS α f z / z)) z :=
  ((hasDerivAt_radA α f hfH hz).const_mul (Work.Spaces.Gam α θ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t => by
      simpa using Corr_eq_radA α f t θ))

/-- **The `D_z`-commutator of the transfer defect.**
With `Corr α f = Γ(θ)·radA α f z` and `radS α f z = z·∂_z(radA α f) z`, the `z`-derivative of
`Corr` is `Γ(θ)·radS α f z` — no `L₁₂` of a differentiated datum appears. -/
theorem Dz_Corr_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (hfH : Work.Coercivity.HardyHyp f) {z θ : ℝ}
    (hz : 0 < z) :
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Corr α f) z θ
      = Work.Spaces.Gam α θ * radS α f z := by
  have h := hasDerivAt_Corr_slice (z := z) (θ := θ) α f hfH hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [h.deriv]
  field_simp

/-! ## The `D_z`-identity of the transfer -/


end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Qang_sq_w_sq_le_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

open MeasureTheory
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Null sets and the weight `w` -/

/-- The `z = 0`-slice of `Iz = [0,∞)` is null, so every almost-everywhere statement on
`Iz` may be proved on the open half-line. -/
private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- The two angular endpoints of `Iθ = [0,π/2]` are null. -/
private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- The radial weight `w` squared is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

/-! ## The general-level Cauchy–Schwarz bound in `θ` -/


/-! ## The slicewise domination by the `ℋ^k`-integrand -/

/-- For `z > 0` and `0 < θ < π/2` the square of the weighted pure `D_z`-iterate is
dominated by the `ℋ^k`-integrand, `(D_z^i g z θ)² w(z)² ≤ HkIntegrand α k g z θ` (`i ≤ k`).
This is `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` multiplied by `w² > 0`. -/
private theorem DzIter_sq_w_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {k i : ℕ} (hi : i ≤ k)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α k g i hi hz hθ
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Work.Spaces.w z))
  rwa [div_mul_cancel₀ _
    (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hz)))] at h2

/-! ## The target -/


end Work.FTS.CoercivityFix.Transfer.E1Norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.amp_iter_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

/-! ## The two elementary one-dimensional ingredients -/

/-- `z ↦ (1+z)^{-2}` is integrable on `(0,∞)`; this is the shift by `1` of the integrability of
`z ↦ z^{-2}` (Mathlib's `integrableOn_add_rpow_Ioi_of_lt` at exponent `-2`). -/
private theorem integrableOn_one_div_one_add_sq :
    IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hpow : IntegrableOn (fun z : ℝ => (z + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1) (by norm_num) (by norm_num)
  refine hpow.congr_fun (fun z hz => ?_) measurableSet_Ioi
  have hz1 : (0 : ℝ) < z + 1 := by linarith [Set.mem_Ioi.mp hz]
  show (z + 1) ^ (-2 : ℝ) = 1 / (1 + z) ^ 2
  rw [Real.rpow_neg (le_of_lt hz1), Real.rpow_two, inv_eq_one_div]
  ring_nf

/-- `∫_0^∞ (1+z)^{-2} dz = 1`, by the fundamental theorem of calculus applied to
`z ↦ -(1+z)^{-1}` (whose derivative is `(1+z)^{-2}` and whose limit at `+∞` is `0`). -/
private theorem integral_Ioi_one_div_one_add_sq :
    ∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2 = 1 := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun z : ℝ => -((1 + z)⁻¹)) (1 / (1 + x) ^ 2) x := by
    intro x hx
    have h0 : (1 + x) ≠ 0 := by
      have : (0 : ℝ) ≤ x := hx
      intro h
      linarith
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have h3 := (h1.inv h0).neg
    convert h3 using 1
    field_simp
  have htend : Tendsto (fun z : ℝ => -((1 + z)⁻¹)) atTop (𝓝 0) := by
    have h : Tendsto (fun z : ℝ => (1 + z)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    simpa using h.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (f := fun z : ℝ => -((1 + z)⁻¹)) (f' := fun z : ℝ => 1 / (1 + z) ^ 2) (m := 0)
    hderiv integrableOn_one_div_one_add_sq htend
  simpa using h

/-! ## The pointwise bound on the weighted iterates of `ampB` -/

/-- Pointwise domination of `(D_z^j (ampB α) z)² w(z)²` by `160000/(1+z)²`, for `z > 0` and
`j ≤ 4`.  The constant is four times the one carried by `E2pkg.rB_sq_w_integrable`
(`40000 = 200²`), the factor `4` coming from the square of the factor `2` in `ampB = 2·fB`. -/
private theorem ampB_iter_sq_w_le (α : ℝ) (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
      * (Work.Spaces.w z) ^ 2 ≤ 160000 * (1 / (1 + z) ^ 2) := by
  rw [congrFun (Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_ampB_eq α j) z,
    Work.FTS.CoercivityFix.Transfer.E2pkg.rB_iter j hj z hz]
  interval_cases j <;>
    simp only [Work.FTS.CoercivityFix.Transfer.E2pkg.rB_zero,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_one,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_two,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_three,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_four,
      Work.Spaces.w] <;>
    field_simp <;>
    nlinarith [sq_nonneg z, sq_nonneg (z * z), sq_nonneg (z ^ 3)]

/-! ## The target -/


end Work.FTS.CoercivityFix.Transfer.E1Norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.AngGam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The iterates of `Γ` -/

/-- **`D_θ^{j+1} Γ = Γ · (2α/3)·Aᵢ(cos²θ)`** on the open quadrant, for `j ≤ 4`. -/
theorem Lop_iter_Gam_succ (α : ℝ) (hα : 0 < α) :
    ∀ j : ℕ, j ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.Lop^[j + 1] (Work.Spaces.Gam α)) θ
        = Work.Spaces.Gam α θ
          * (2 * α / 3 * Work.Construction.Aang j (Real.cos θ ^ 2) α) := by
  intro j
  induction j with
  | zero =>
      intro _ θ hθ
      show Work.Spaces.Lop (Work.Spaces.Gam α) θ = _
      rw [Work.Construction.glop_Gam_deriv α θ hα hθ, Work.Construction.Aang_zero]
      ring
  | succ j ih =>
      intro hj θ hθ
      have hj4 : j ≤ 4 := by omega
      have hj3 : j ≤ 3 := by omega
      have hev : (Work.Spaces.Lop^[j + 1] (Work.Spaces.Gam α))
          =ᶠ[𝓝 θ] (fun y => Work.Spaces.Gam α y
              * (2 * α / 3 * Work.Construction.Aang j (Real.cos y ^ 2) α)) := by
        filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
        exact ih hj4 y hy
      have hidx : (Work.Spaces.Lop^[Nat.succ j + 1] (Work.Spaces.Gam α))
          = Work.Spaces.Lop (Work.Spaces.Lop^[j + 1] (Work.Spaces.Gam α)) :=
        Function.iterate_succ_apply' Work.Spaces.Lop (j + 1) (Work.Spaces.Gam α)
      rw [hidx]
      have hLop : Work.Spaces.Lop (Work.Spaces.Lop^[j + 1] (Work.Spaces.Gam α)) θ
          = Work.Spaces.Lop (fun y => Work.Spaces.Gam α y
              * (2 * α / 3 * Work.Construction.Aang j (Real.cos y ^ 2) α)) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j + 1] (Work.Spaces.Gam α)) θ
          = Real.sin (2 * θ) * deriv (fun y => Work.Spaces.Gam α y
              * (2 * α / 3 * Work.Construction.Aang j (Real.cos y ^ 2) α)) θ
        rw [hev.deriv_eq]
      rw [hLop]
      rw [Work.Construction.glop_step α hα
        (fun x : ℝ => 2 * α / 3 * Work.Construction.Aang j x α)
        ((Work.Construction.differentiable_Aang j hj4 α).const_mul (2 * α / 3)) θ hθ]
      rw [deriv_const_mul (2 * α / 3)
        ((Work.Construction.differentiable_Aang j hj4 α).differentiableAt)]
      rw [← Work.Construction.glop_Aang_succ j hj3 (Real.cos θ ^ 2) α]
      ring

/-- The coefficient `(2α/3)·Aang j x α` is bounded by `10^8` on `[0,1]` for `j ≤ 4`,
`0 < α ≤ 1`. -/
theorem coeff_abs_le (j : ℕ) (hj : j ≤ 4) (x α : ℝ) (hx : x ∈ Set.Icc 0 1)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    |2 * α / 3 * Work.Construction.Aang j x α| ≤ 10 ^ 8 := by
  have hα3 : 0 ≤ 2 * α / 3 := by linarith
  have hx41 : 4 * x * (1 - x) ≤ 1 := by nlinarith [sq_nonneg (x - 1 / 2)]
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    rw [Work.Construction.Aang_zero, abs_mul, abs_of_nonneg hα3]
    have h3x2 : |3 * x - 2| ≤ 3 := by
      rw [abs_le]; constructor <;> nlinarith [hx.1, hx.2]
    nlinarith
  · have hb : |Work.Construction.Aang j x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by
      interval_cases j
      · exact Work.Construction.glop_Aang_bound_one x α hx hα hα1
      · exact Work.Construction.glop_Aang_bound_two x α hx hα hα1
      · exact Work.Construction.glop_Aang_bound_three x α hx hα hα1
      · exact Work.Construction.glop_Aang_bound_four x α hx hα hα1
    rw [abs_mul, abs_of_nonneg hα3]
    have h2 : 10 ^ 7 * (α + 4 * x * (1 - x)) ≤ 2 * 10 ^ 7 := by nlinarith
    nlinarith

/-- **The angular iterate bound**: `|D_θ^k Γ θ| ≤ 10^8 Γ θ` for `1 ≤ k ≤ 4` and `θ ∈ Iθ`. -/
theorem Gam_Lop_iter_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.Lop^[k] (Work.Spaces.Gam α)) θ| ≤ 10 ^ 8 * Work.Spaces.Gam α θ := by
  have hGam : Work.Spaces.Gam α = fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := rfl
  intro k hk hk4 θ hθ
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  -- the `sin 2θ = 0` endpoints
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hzero : (Work.Spaces.Lop^[m + 1] (Work.Spaces.Gam α)) 0 = 0 := by
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by norm_num, zero_mul]
    rw [hzero, hGam]
    have hb : Real.sin 0 * Real.cos 0 ^ 2 = (0 : ℝ) := by norm_num
    show |(0 : ℝ)| ≤ 10 ^ 8 * ((Real.sin 0 * Real.cos 0 ^ 2) ^ (α / 3))
    rw [hb, Real.zero_rpow (by positivity : α / 3 ≠ 0)]
    norm_num
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · subst h1
    have hzero : (Work.Spaces.Lop^[m + 1] (Work.Spaces.Gam α)) (π / 2) = 0 := by
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      have hs : Real.sin (2 * (π / 2)) = 0 := by
        rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
      rw [hs, zero_mul]
    rw [hzero, hGam]
    have hb : Real.sin (π / 2) * Real.cos (π / 2) ^ 2 = (0 : ℝ) := by norm_num
    show |(0 : ℝ)| ≤ 10 ^ 8 * ((Real.sin (π / 2) * Real.cos (π / 2) ^ 2) ^ (α / 3))
    rw [hb, Real.zero_rpow (by positivity : α / 3 ≠ 0)]
    norm_num
  · have hm4 : m ≤ 4 := by omega
    rw [Lop_iter_Gam_succ α hα m hm4 θ ⟨h0, h1⟩, abs_mul]
    have hΓnn : 0 ≤ Work.Spaces.Gam α θ := by
      rw [hGam]
      exact Real.rpow_nonneg (mul_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi h0
        (by linarith [h1, Real.pi_pos]))) (sq_nonneg _)) _
    rw [abs_of_nonneg hΓnn]
    have hx : Real.cos θ ^ 2 ∈ Set.Icc 0 1 :=
      ⟨sq_nonneg _, Real.cos_sq_le_one θ⟩
    have := coeff_abs_le m hm4 (Real.cos θ ^ 2) α hx hα hα1
    nlinarith [hΓnn]

/-! ## The weighted squares of `Γ` are integrable -/

/-- On the open interval, `Γ θ² = (sinθ cos²θ)^{2α/3}`. -/
theorem Gam_sq_eq (α θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.Gam α θ) ^ 2 = (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) := by
  have hpos : 0 < Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  rw [show Work.Spaces.Gam α = fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl,
    pow_two, ← Real.rpow_add hpos (α / 3) (α / 3)]
  congr 1
  ring

/-- On the open interval, `sinθ cos²θ ≤ sin(2θ)`. -/
theorem sin_cos_sq_le_sin_two (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin (2 * θ) := by
  have h1 : 0 ≤ Real.sin θ := le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos]))
  have h2 : 0 ≤ Real.cos θ := le_of_lt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have h3 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [h2, Real.cos_le_one θ]
  have h4 : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * Real.cos θ :=
    mul_le_mul_of_nonneg_left h3 h1
  have h5 : Real.sin θ * Real.cos θ ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; nlinarith
  exact le_trans h4 h5

/-- `Γ²` is continuous on the open interval. -/
private theorem continuousOn_Gam_sq (α : ℝ) :
    ContinuousOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have hpow : ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    hbase.rpow_const (fun θ hθ => Or.inl (by
      have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos])
      have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity))
  have hmul : ContinuousOn (fun θ : ℝ => ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      * ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))) (Set.Ioo (0 : ℝ) (π / 2)) := hpow.mul hpow
  refine hmul.congr (fun θ _ => ?_)
  show (Work.Spaces.Gam α θ) ^ 2
      = ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) * ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
  rw [show Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl, pow_two]

/-- `Γ θ² · sin(2θ)^{-η}` is integrable on `Iθ`. -/
theorem Gam_sq_smE_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smE θ) Work.Spaces.Iθ := by
  have hsmE : Work.FTS.Nonlinear.RadialProd.smE
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [hIθ]; exact MeasureTheory.Ioo_ae_eq_Icc
  have hp1 : -1 < 2 * α / 3 - Work.Spaces.eta := by
    have h1 := Work.Spaces.eta_lt_one
    have h2 := Work.Spaces.eta_pos
    linarith
  have hp2 : 2 * α / 3 - Work.Spaces.eta ≤ 0 := by
    have h1 : 2 * α / 3 ≤ 2 / 3 := by linarith
    have h2 : (2 : ℝ) / 3 ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
    linarith
  have hmaj := (Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.eta) hp1 hp2).1
  have hcont : ContinuousOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smE θ) (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine ContinuousOn.mul (continuousOn_Gam_sq α) ?_
    rw [hsmE]
    refine ContinuousOn.rpow_const
      (f := fun θ : ℝ => Real.sin (2 * θ)) ?_ (fun θ hθ => Or.inl (ne_of_gt ?_))
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos])
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smE θ) (volume.restrict Work.Spaces.Iθ) := by
    have h1 : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smE θ) (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
      hcont.aestronglyMeasurable measurableSet_Ioo
    rwa [MeasureTheory.Measure.restrict_congr_set (μ := volume) hIoo] at h1
  refine MeasureTheory.Integrable.mono' hmaj hmeas ?_
  rw [(MeasureTheory.Measure.restrict_congr_set (μ := volume) hIoo).symm]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])
  have hΓ := Gam_sq_eq α θ hθ
  have hle := sin_cos_sq_le_sin_two θ hθ
  have hnonneg : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 ≤ Real.sin θ := le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1
      (by linarith [hθ.2, Real.pi_pos]))
    have h2 : 0 ≤ Real.cos θ := le_of_lt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
    positivity
  have hnn : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ := by
    rw [hsmE]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hsmE, hΓ]
  calc (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hnonneg hle (by linarith))
          (Real.rpow_nonneg hsin.le _)
    _ = (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta) := by
        rw [← Real.rpow_add hsin]
        ring_nf

/-- `Γ θ² · sin(2θ)^{-γ}` is integrable on `Iθ`. -/
theorem Gam_sq_smG_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ := by
  have hsmG : Work.FTS.Nonlinear.RadialProd.smG α
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [hIθ]; exact MeasureTheory.Ioo_ae_eq_Icc
  have hγpos : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hp2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by
    rw [Work.Spaces.gam]; linarith
  have hmaj := (Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.gam α) hp1 hp2).1
  have hcont : ContinuousOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smG α θ) (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine ContinuousOn.mul (continuousOn_Gam_sq α) ?_
    rw [hsmG]
    refine ContinuousOn.rpow_const
      (f := fun θ : ℝ => Real.sin (2 * θ)) ?_ (fun θ hθ => Or.inl (ne_of_gt ?_))
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos])
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smG α θ) (volume.restrict Work.Spaces.Iθ) := by
    have h1 : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ) (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
      hcont.aestronglyMeasurable measurableSet_Ioo
    rwa [MeasureTheory.Measure.restrict_congr_set (μ := volume) hIoo] at h1
  refine MeasureTheory.Integrable.mono' hmaj hmeas ?_
  rw [(MeasureTheory.Measure.restrict_congr_set (μ := volume) hIoo).symm]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])
  have hΓ := Gam_sq_eq α θ hθ
  have hle := sin_cos_sq_le_sin_two θ hθ
  have hnonneg : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 ≤ Real.sin θ := le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1
      (by linarith [hθ.2, Real.pi_pos]))
    have h2 : 0 ≤ Real.cos θ := le_of_lt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
    positivity
  have hnn : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    rw [hsmG]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hsmG, hΓ]
  calc (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hnonneg hle (by linarith))
          (Real.rpow_nonneg hsin.le _)
    _ = (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by
        rw [← Real.rpow_add hsin]
        ring_nf

/-- **The angular data of `E1`.** -/
theorem AngGam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.Lop^[k] (Work.Spaces.Gam α)) θ| ≤ 10 ^ 8 * Work.Spaces.Gam α θ) ∧
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
      Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      Work.Spaces.Iθ :=
  ⟨Gam_Lop_iter_bound α hα hα1, Gam_sq_smE_integrable α hα hα1,
    Gam_sq_smG_integrable α hα hα1⟩

end Work.FTS.CoercivityFix.Transfer.E1Parts
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Iterates of `Zop u = z·u'` agree on `(0,∞)` for functions agreeing there. -/
theorem Zop_iter_congr_of_eqOn (u v : ℝ → ℝ) (h : ∀ z ∈ Set.Ioi (0 : ℝ), u z = v z) :
    ∀ b : ℕ, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.Zop^[b] u z = Work.Spaces.Zop^[b] v z := by
  intro b
  induction b with
  | zero => exact h
  | succ k ih =>
      intro z hz
      have hev : Work.Spaces.Zop^[k] u =ᶠ[𝓝 z] Work.Spaces.Zop^[k] v := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih w hw
      have h1 : Work.Spaces.Zop^[k + 1] u = Work.Spaces.Zop (Work.Spaces.Zop^[k] u) :=
        Function.iterate_succ_apply' Work.Spaces.Zop k u
      have h2 : Work.Spaces.Zop^[k + 1] v = Work.Spaces.Zop (Work.Spaces.Zop^[k] v) :=
        Function.iterate_succ_apply' Work.Spaces.Zop k v
      rw [h1, h2]
      show z * deriv (Work.Spaces.Zop^[k] u) z = z * deriv (Work.Spaces.Zop^[k] v) z
      rw [hev.deriv_eq]

/-- **Additivity of the `Zop`-iterates** for functions whose iterates are differentiable on
`(0,∞)` up to one order below the level. -/
theorem Zop_iter_add_of (j : ℕ) (u v : ℝ → ℝ)
    (hu : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Spaces.Zop^[b] u) z)
    (hv : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Spaces.Zop^[b] v) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.Zop^[j] (u + v) z = Work.Spaces.Zop^[j] u z + Work.Spaces.Zop^[j] v z := by
  induction j with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      have hu' : ∀ b < k, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Spaces.Zop^[b] u) z :=
        fun b hb => hu b (by omega)
      have hv' : ∀ b < k, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Spaces.Zop^[b] v) z :=
        fun b hb => hv b (by omega)
      have hev : Work.Spaces.Zop^[k] (u + v)
          =ᶠ[𝓝 z] Work.Spaces.Zop^[k] u + Work.Spaces.Zop^[k] v := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih hu' hv' w hw
      have h1 : DifferentiableAt ℝ (Work.Spaces.Zop^[k] u) z := hu k (by omega) z hz
      have h2 : DifferentiableAt ℝ (Work.Spaces.Zop^[k] v) z := hv k (by omega) z hz
      have h3 : Work.Spaces.Zop^[k + 1] (u + v)
          = Work.Spaces.Zop (Work.Spaces.Zop^[k] (u + v)) :=
        Function.iterate_succ_apply' Work.Spaces.Zop k (u + v)
      have h4 : Work.Spaces.Zop^[k + 1] u = Work.Spaces.Zop (Work.Spaces.Zop^[k] u) :=
        Function.iterate_succ_apply' Work.Spaces.Zop k u
      have h5 : Work.Spaces.Zop^[k + 1] v = Work.Spaces.Zop (Work.Spaces.Zop^[k] v) :=
        Function.iterate_succ_apply' Work.Spaces.Zop k v
      rw [h3, h4, h5]
      show z * deriv (Work.Spaces.Zop^[k] (u + v)) z
        = z * deriv (Work.Spaces.Zop^[k] u) z + z * deriv (Work.Spaces.Zop^[k] v) z
      rw [hev.deriv_eq, deriv_add h1 h2]
      ring

/-- Additivity of the `DzdIter`s, in the vocabulary used by the Leibniz rule. -/
theorem DzdIter_add_of_diff (j : ℕ) (u v : ℝ → ℝ)
    (hu : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z)
    (hv : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b v) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (u + v) z
        = Work.Elliptic.DzdIter j u z + Work.Elliptic.DzdIter j v z := by
  intro z hz
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j (u + v),
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j u,
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j v]
  refine Zop_iter_add_of j u v ?_ ?_ z hz
  · intro b hb z' hz'
    rw [← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b u]
    exact hu b hb z' hz'
  · intro b hb z' hz'
    rw [← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b v]
    exact hv b hb z' hz'

/-- Congruence of the `DzdIter`s for functions agreeing on `(0,∞)`. -/
theorem DzdIter_congr_of_eqOn (u v : ℝ → ℝ) (h : ∀ z ∈ Set.Ioi (0 : ℝ), u z = v z) (j : ℕ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j u z = Work.Elliptic.DzdIter j v z := by
  intro z hz
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j u,
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j v]
  exact Zop_iter_congr_of_eqOn u v h j z hz

/-- The derivative of a `C^{n+1}` function on `(0,∞)` is `C^n`. -/
theorem contDiffOn_deriv_of_succ {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (n + 1) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ n (deriv u) (Set.Ioi (0 : ℝ)) := by
  have hfd : ContDiffOn ℝ n (fderiv ℝ u) (Set.Ioi (0 : ℝ)) :=
    hu.fderiv_of_isOpen isOpen_Ioi (by simp)
  have hev : ContDiffOn ℝ n (fun z : ℝ => (fderiv ℝ u z) 1) (Set.Ioi (0 : ℝ)) :=
    hfd.clm_apply contDiffOn_const
  refine hev.congr (fun z _ => ?_)
  rw [fderiv_apply_one_eq_deriv]

/-- A `C^{b+k}`-function has `C^k` `Zop`-iterates of order `b`. -/
theorem contDiffOn_Zop_iter' {u : ℝ → ℝ} (b k : ℕ)
    (hu : ContDiffOn ℝ (b + k) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ k (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) := by
  induction b generalizing k with
  | zero => simpa using hu
  | succ b ih =>
      have hu' : ContDiffOn ℝ (b + (k + 1)) u (Set.Ioi (0 : ℝ)) :=
        hu.of_le (by exact_mod_cast (by omega : b + (k + 1) ≤ (b + 1) + k))
      have h1 : ContDiffOn ℝ (k + 1) (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) := ih (k + 1) hu'
      have h2 : ContDiffOn ℝ k (deriv (Work.Spaces.Zop^[b] u)) (Set.Ioi (0 : ℝ)) :=
        contDiffOn_deriv_of_succ h1
      have h3 : ContDiffOn ℝ k
          (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z) (Set.Ioi (0 : ℝ)) :=
        (contDiff_id.contDiffOn).mul h2
      rw [Function.iterate_succ_apply']
      change ContDiffOn ℝ k (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z)
        (Set.Ioi (0 : ℝ))
      exact h3

/-- A `C^{b+1}`-function has differentiable `Zop`-iterate of order `b` on `(0,∞)`. -/
theorem differentiableAt_Zop_iter_of_contDiffOn {u : ℝ → ℝ} {b : ℕ}
    (hu : ContDiffOn ℝ (b + 1) u (Set.Ioi (0 : ℝ))) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Spaces.Zop^[b] u) z :=
  ((contDiffOn_Zop_iter' b 1 hu).differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- A `C^{b+n}`-function has continuous `Zop`-iterate of order `b` on `(0,∞)`. -/
theorem continuousOn_Zop_iter_of_contDiffOn {u : ℝ → ℝ} {b n : ℕ}
    (hu : ContDiffOn ℝ (b + n) u (Set.Ioi (0 : ℝ))) :
    ContinuousOn (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) :=
  (contDiffOn_Zop_iter' b n hu).continuousOn

end Work.FTS.CoercivityFix.Transfer.E1Parts
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadL12 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1000000


/-- `Qang f 0 z = ∫_θ K θ · f z θ`: the zeroth angular moment is the `K`-average of `f`. -/
theorem Qang_zero_eq_integral (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Qang f 0 z = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ := by
  have h := Work.Coercivity.DzRIter_L12f_bridge_Qang f 0 z
  simpa using h




end Work.FTS.CoercivityFix.Transfer.E1Parts
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.ampB_DzdIter_sq_w_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2norm

/-! ## The two elementary one-dimensional ingredients -/

/-- `z ↦ (1+z)^{-2}` is integrable on `(0,∞)`: this is the shift by `1` of the integrability of
`z ↦ z^{-2}` (Mathlib's `integrableOn_add_rpow_Ioi_of_lt` at exponent `-2`). -/
private theorem integrableOn_one_div_one_add_sq :
    IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hpow : IntegrableOn (fun z : ℝ => (z + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1) (by norm_num) (by norm_num)
  refine hpow.congr_fun (fun z hz => ?_) measurableSet_Ioi
  have hz1 : (0 : ℝ) < z + 1 := by linarith [Set.mem_Ioi.mp hz]
  show (z + 1) ^ (-2 : ℝ) = 1 / (1 + z) ^ 2
  rw [Real.rpow_neg (le_of_lt hz1), Real.rpow_two, inv_eq_one_div]
  ring_nf

/-- `∫_0^∞ (1+z)^{-2} dz = 1`, by the fundamental theorem of calculus applied to
`z ↦ -(1+z)^{-1}` (whose derivative is `(1+z)^{-2}` and whose limit at `+∞` is `0`). -/
private theorem integral_Ioi_one_div_one_add_sq :
    ∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2 = 1 := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun z : ℝ => -((1 + z)⁻¹)) (1 / (1 + x) ^ 2) x := by
    intro x hx
    have h0 : (1 + x) ≠ 0 := by
      have : (0 : ℝ) ≤ x := hx
      intro h
      linarith
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have h3 := (h1.inv h0).neg
    convert h3 using 1
    field_simp
  have htend : Tendsto (fun z : ℝ => -((1 + z)⁻¹)) atTop (𝓝 0) := by
    have h : Tendsto (fun z : ℝ => (1 + z)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    simpa using h.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (f := fun z : ℝ => -((1 + z)⁻¹)) (f' := fun z : ℝ => 1 / (1 + z) ^ 2) (m := 0)
    hderiv integrableOn_one_div_one_add_sq htend
  simpa using h

/-! ## The pointwise bound on the weighted iterates of `ampB` -/

/-- Pointwise domination of `(D_z^c (ampB α) z)² w(z)²` by `160000/(1+z)²`, for `z > 0` and
`c ≤ 4`.  The constant is four times the one carried by the explicit closed forms
(`40000 = 200²`, the square of the largest coefficient occurring in the numerators `N_c`), the
factor `4` coming from the square of the factor `2` in `ampB = 2·fB`. -/
private theorem ampB_iter_sq_w_le (α : ℝ) (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
      * (Work.Spaces.w z) ^ 2 ≤ 160000 * (1 / (1 + z) ^ 2) := by
  rw [congrFun (Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_ampB_eq α j) z,
    Work.FTS.CoercivityFix.Transfer.E2pkg.rB_iter j hj z hz]
  interval_cases j <;>
    simp only [Work.FTS.CoercivityFix.Transfer.E2pkg.rB_zero,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_one,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_two,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_three,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_four,
      Work.Spaces.w] <;>
    field_simp <;>
    nlinarith [sq_nonneg z, sq_nonneg (z * z), sq_nonneg (z ^ 3)]

/-! ## The target -/

theorem ampB_DzdIter_sq_w_sq_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c : ℕ, c ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2 ≤ K := by
  refine ⟨160000, by norm_num, ?_⟩
  intro α hα hα1 c hc
  have hInt : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    (Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1).2 c hc
  refine ⟨hInt, ?_⟩
  -- `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`
  have hmeas : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz :=
    Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))
  calc ∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2
      = ∫ z in Set.Ioi (0 : ℝ),
          (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by rw [← hmeas]
    _ ≤ ∫ z in Set.Ioi (0 : ℝ), 160000 * (1 / (1 + z) ^ 2) := by
        refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
        · exact hInt.mono_set Set.Ioi_subset_Ici_self
        · exact integrableOn_one_div_one_add_sq.const_mul 160000
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
          exact ampB_iter_sq_w_le α c hc hz
    _ = 160000 := by
        rw [MeasureTheory.integral_const_mul, integral_Ioi_one_div_one_add_sq, mul_one]

end Work.FTS.CoercivityFix.Transfer.E2norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.H1IP_add_weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.CoercivityFix.Assembly

/-! ## Honesty of the four pairings from block continuity on the open quadrant -/

/-- Honesty of the `D_z⁰`-pairing `∫ a b ρη` of `H1IP`, from continuity of `a`, `b` on
the open quadrant. -/
theorem PairHonest_eta_Qd (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hca : ContinuousOn (Function.uncurry a) Work.Construction.Qd)
    (hcb : ContinuousOn (Function.uncurry b) Work.Construction.Qd)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamEta a b := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ => a z θ * b z θ * Work.Coercivity.lamEta z θ)
        = fun p : ℝ × ℝ => Function.uncurry a p * Function.uncurry b p
            * Function.uncurry Work.Coercivity.lamEta p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (hca.mul hcb).mul continuousOn_lamEta
  · intro θ
    simp [Work.Coercivity.lamEta, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.Xeta_mul_eq a b z θ hθ]
    calc |Work.Coercivity.Xeta a z θ * Work.Coercivity.Xeta b z θ|
        = |Work.Coercivity.Xeta a z θ| * |Work.Coercivity.Xeta b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.Xeta a z θ) ^ 2 + (Work.Coercivity.Xeta b z θ) ^ 2) / 2 :=
          abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_Xeta_le_HkIntegrand α a z θ
          have h2 := sq_Xeta_le_HkIntegrand α b z θ
          linarith

/-- Honesty of the `D_z`-pairing `∫ (D_z a)(D_z b) ρη` of `H1IP`, from continuity of
`D_z a`, `D_z b` on the open quadrant. -/
theorem PairHonest_etaDz_Qd (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hca : ContinuousOn (Function.uncurry (Work.Spaces.Dz a)) Work.Construction.Qd)
    (hcb : ContinuousOn (Function.uncurry (Work.Spaces.Dz b)) Work.Construction.Qd)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamEta
      (Work.Spaces.Dz a) (Work.Spaces.Dz b) := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ =>
        Work.Spaces.Dz a z θ * Work.Spaces.Dz b z θ * Work.Coercivity.lamEta z θ)
        = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dz a) p
            * Function.uncurry (Work.Spaces.Dz b) p
            * Function.uncurry Work.Coercivity.lamEta p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (hca.mul hcb).mul continuousOn_lamEta
  · intro θ
    simp [Work.Coercivity.lamEta, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.XetaDz_mul_eq a b z θ hθ]
    calc |Work.Coercivity.XetaDz a z θ * Work.Coercivity.XetaDz b z θ|
        = |Work.Coercivity.XetaDz a z θ| * |Work.Coercivity.XetaDz b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.XetaDz a z θ) ^ 2
            + (Work.Coercivity.XetaDz b z θ) ^ 2) / 2 := abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_XetaDz_le_HkIntegrand α a z θ
          have h2 := sq_XetaDz_le_HkIntegrand α b z θ
          linarith

/-- Honesty of the `D_θ`-pairing `∫ (D_θ a)(D_θ b) ργ` of `H1IP`, from continuity of
`D_θ a`, `D_θ b` on the open quadrant. -/
theorem PairHonest_gam_Qd (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hca : ContinuousOn (Function.uncurry (Work.Spaces.Dth a)) Work.Construction.Qd)
    (hcb : ContinuousOn (Function.uncurry (Work.Spaces.Dth b)) Work.Construction.Qd)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest (Work.Coercivity.lamGam α)
      (Work.Spaces.Dth a) (Work.Spaces.Dth b) := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ =>
        Work.Spaces.Dth a z θ * Work.Spaces.Dth b z θ * Work.Coercivity.lamGam α z θ)
        = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dth a) p
            * Function.uncurry (Work.Spaces.Dth b) p
            * Function.uncurry (Work.Coercivity.lamGam α) p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (hca.mul hcb).mul (continuousOn_lamGam α)
  · intro θ
    simp [Work.Coercivity.lamGam, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.XgamDth_mul_eq α a b z θ hθ]
    calc |Work.Coercivity.XgamDth α a z θ * Work.Coercivity.XgamDth α b z θ|
        = |Work.Coercivity.XgamDth α a z θ| * |Work.Coercivity.XgamDth α b z θ| :=
          abs_mul _ _
      _ ≤ ((Work.Coercivity.XgamDth α a z θ) ^ 2
            + (Work.Coercivity.XgamDth α b z θ) ^ 2) / 2 := abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_XgamDth_le_HkIntegrand α a z θ
          have h2 := sq_XgamDth_le_HkIntegrand α b z θ
          linarith

/-- Honesty of the unweighted pairing `∫ a b w²` of `H1IP`, from continuity of `a`, `b`
on the open quadrant.  Off the two null endpoints of `Iθ` the plain `w²`-block is
dominated by the `D_z⁰`-summand of the `ℋ¹`-integrand, since `sin 2θ ≤ 1`. -/
theorem PairHonest_w_Qd (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hca : ContinuousOn (Function.uncurry a) Work.Construction.Qd)
    (hcb : ContinuousOn (Function.uncurry b) Work.Construction.Qd)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamW a b := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ => a z θ * b z θ * Work.Coercivity.lamW z θ)
        = fun p : ℝ × ℝ => Function.uncurry a p * Function.uncurry b p
            * Function.uncurry Work.Coercivity.lamW p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (hca.mul hcb).mul continuousOn_lamW
  · intro θ
    simp [Work.Coercivity.lamW, Work.Spaces.w]
  · intro z _
    filter_upwards [sq_Xw_le_HkIntegrand_ae α a z, sq_Xw_le_HkIntegrand_ae α b z]
      with θ h1 h2
    have hXw : Work.Coercivity.Xw a z θ * Work.Coercivity.Xw b z θ
        = a z θ * b z θ * Work.Coercivity.lamW z θ := by
      simp only [Work.Coercivity.Xw, Work.Coercivity.lamW]; ring
    rw [← hXw]
    calc |Work.Coercivity.Xw a z θ * Work.Coercivity.Xw b z θ|
        = |Work.Coercivity.Xw a z θ| * |Work.Coercivity.Xw b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.Xw a z θ) ^ 2 + (Work.Coercivity.Xw b z θ) ^ 2) / 2 :=
          abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          linarith

/-! ## The additivity of `H1IP` -/

theorem H1IP_add_weak (α : ℝ) {a₁ a₂ b : ℝ → ℝ → ℝ}
    (hm1 : Work.Spaces.HkMem α 1 a₁) (hm2 : Work.Spaces.HkMem α 1 a₂)
    (hmb : Work.Spaces.HkMem α 1 b)
    (hc1 : ContinuousOn (Function.uncurry a₁) Work.Construction.Qd)
    (hc2 : ContinuousOn (Function.uncurry a₂) Work.Construction.Qd)
    (hcb : ContinuousOn (Function.uncurry b) Work.Construction.Qd)
    (hdz1 : ContinuousOn (Function.uncurry (Work.Spaces.Dz a₁)) Work.Construction.Qd)
    (hdz2 : ContinuousOn (Function.uncurry (Work.Spaces.Dz a₂)) Work.Construction.Qd)
    (hdzb : ContinuousOn (Function.uncurry (Work.Spaces.Dz b)) Work.Construction.Qd)
    (hdth1 : ContinuousOn (Function.uncurry (Work.Spaces.Dth a₁)) Work.Construction.Qd)
    (hdth2 : ContinuousOn (Function.uncurry (Work.Spaces.Dth a₂)) Work.Construction.Qd)
    (hdthb : ContinuousOn (Function.uncurry (Work.Spaces.Dth b)) Work.Construction.Qd)
    (hdz : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (a₁ + a₂) z θ = Work.Spaces.Dz a₁ z θ + Work.Spaces.Dz a₂ z θ)
    (hdth : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (a₁ + a₂) z θ = Work.Spaces.Dth a₁ z θ + Work.Spaces.Dth a₂ z θ) :
    Work.Coercivity.H1IP α (a₁ + a₂) b = Work.Coercivity.H1IP α a₁ b + Work.Coercivity.H1IP α a₂ b := by
  have hA : Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz (a₁ + a₂))
        (Work.Spaces.Dz b)
      = Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz a₁) (Work.Spaces.Dz b)
        + Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz a₂) (Work.Spaces.Dz b) := by
    rw [Work.FTS.CoercivityFix.StepAssembly.wip_congr_Qd (A := Work.Spaces.Dz (a₁ + a₂))
      (A' := Work.Spaces.Dz a₁ + Work.Spaces.Dz a₂) hdz]
    exact Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamEta (Work.Spaces.Dz a₁)
      (Work.Spaces.Dz a₂) (Work.Spaces.Dz b)
      (PairHonest_etaDz_Qd α hdz1 hdzb hm1 hmb)
      (PairHonest_etaDz_Qd α hdz2 hdzb hm2 hmb)
  have hB : Work.Coercivity.wip Work.Coercivity.lamEta (a₁ + a₂) b
      = Work.Coercivity.wip Work.Coercivity.lamEta a₁ b
        + Work.Coercivity.wip Work.Coercivity.lamEta a₂ b :=
    Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamEta a₁ a₂ b
      (PairHonest_eta_Qd α hc1 hcb hm1 hmb) (PairHonest_eta_Qd α hc2 hcb hm2 hmb)
  have hC : Work.Coercivity.wip Work.Coercivity.lamW (a₁ + a₂) b
      = Work.Coercivity.wip Work.Coercivity.lamW a₁ b
        + Work.Coercivity.wip Work.Coercivity.lamW a₂ b :=
    Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamW a₁ a₂ b
      (PairHonest_w_Qd α hc1 hcb hm1 hmb) (PairHonest_w_Qd α hc2 hcb hm2 hmb)
  have hD : Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth (a₁ + a₂))
        (Work.Spaces.Dth b)
      = Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₁)
          (Work.Spaces.Dth b)
        + Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₂)
          (Work.Spaces.Dth b) := by
    rw [Work.FTS.CoercivityFix.StepAssembly.wip_congr_Qd (A := Work.Spaces.Dth (a₁ + a₂))
      (A' := Work.Spaces.Dth a₁ + Work.Spaces.Dth a₂) hdth]
    exact Work.Coercivity.wip_add_of_PairHonest (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₁)
      (Work.Spaces.Dth a₂) (Work.Spaces.Dth b)
      (PairHonest_gam_Qd α hdth1 hdthb hm1 hmb)
      (PairHonest_gam_Qd α hdth2 hdthb hm2 hmb)
  have hEtaW : (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = Work.Coercivity.lamEta := rfl
  have hGamW : (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = Work.Coercivity.lamGam α := rfl
  have hWtW : (fun z _ => Work.Spaces.w z ^ 2) = Work.Coercivity.lamW := rfl
  simp only [Work.Coercivity.H1IP]
  rw [hEtaW, hGamW, hWtW, hA, hB, hC, hD]
  ring

end

end Work.FTS.CoercivityFix.Transfer
end
-- ===== merged: Submission.Work.FTS.EllSol.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false



end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.InterpDomAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-! ## The folded kernel is dominated by the positive three-image kernel -/

/-- Each of the three summands of the folded kernel `Kern (sKer ε) θ s` is nonnegative, so the
folded kernel is dominated in absolute value by the positive three-image kernel
`KJ ε θ s = sKer ε (θ-s) + sKer ε (θ+s) + sKer ε (θ+s-π)`. -/
theorem Kern_abs_le_KJ {ε : ℝ} (hε : 0 < ε) (θ s : ℝ) :
    |Kern (sKer ε) θ s| ≤ KJ ε θ s := by
  have h1 : 0 ≤ sKer ε (θ - s) := sKer_nonneg hε _
  have h2 : 0 ≤ sKer ε (θ + s) := sKer_nonneg hε _
  have h3 : 0 ≤ sKer ε (θ + s - Real.pi) := sKer_nonneg hε _
  rw [Kern, KJ]
  exact abs_le.mpr ⟨by linarith, by linarith⟩



/-- Continuity of the folded kernel in the angular variable. -/
theorem continuous_Kern_slice (ε θ : ℝ) : Continuous (fun s : ℝ => Kern (sKer ε) θ s) := by
  have hc : Continuous (fun t : ℝ => sKer ε t) := Work.FTS.EllSol.K5cAux.continuous_sKer ε
  have hfun : (fun s : ℝ => Kern (sKer ε) θ s)
      = fun s : ℝ => sKer ε (θ - s) - sKer ε (θ + s) - sKer ε (θ + s - Real.pi) := by
    funext s
    rw [Kern]
  rw [hfun]
  exact ((hc.comp (continuous_const.sub continuous_id)).sub
    (hc.comp (continuous_const.add continuous_id))).sub
    (hc.comp ((continuous_const.add continuous_id).sub continuous_const))

/-- Continuity of the positive kernel in the angular variable. -/
theorem continuous_KJ_slice (ε θ : ℝ) : Continuous (fun s : ℝ => KJ ε θ s) := by
  have hc : Continuous (fun t : ℝ => sKer ε t) := Work.FTS.EllSol.K5cAux.continuous_sKer ε
  have hfun : (fun s : ℝ => KJ ε θ s)
      = fun s : ℝ => sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi) := by
    funext s
    rw [KJ]
  rw [hfun]
  exact ((hc.comp (continuous_const.sub continuous_id)).add
    (hc.comp (continuous_const.add continuous_id))).add
    (hc.comp ((continuous_const.add continuous_id).sub continuous_const))

/-- **The folded kernel against a function is dominated by the positive kernel against its
modulus.** -/
theorem abs_kernSlot_le_kjSlot {ε θ : ℝ} (hε : 0 < ε) (h : ℝ → ℝ)
    (hh : MeasureTheory.IntegrableOn h Work.Spaces.Iθ) :
    |∫ s in Work.Spaces.Iθ, Kern (sKer ε) θ s * h s|
      ≤ ∫ s in Work.Spaces.Iθ, KJ ε θ s * |h s| := by
  have hint1 : MeasureTheory.IntegrableOn
      (fun s : ℝ => Kern (sKer ε) θ s * h s) Work.Spaces.Iθ :=
    (MeasureTheory.IntegrableOn.mul_continuousOn hh (continuous_Kern_slice ε θ).continuousOn
      isCompact_Icc).congr_fun (fun s _ => by ring) measurableSet_Icc
  have hint2 : MeasureTheory.IntegrableOn (fun s : ℝ => KJ ε θ s * |h s|) Work.Spaces.Iθ :=
    (MeasureTheory.IntegrableOn.mul_continuousOn hh.abs (continuous_KJ_slice ε θ).continuousOn
      isCompact_Icc).congr_fun (fun s _ => by ring) measurableSet_Icc
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  refine MeasureTheory.integral_mono_ae hint1.abs hint2 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (Kern_abs_le_KJ hε θ s) (abs_nonneg _)

/-! ## The angular Jensen step for the folded kernel -/


/-! ## Continuity of the angular slice of the datum -/



end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.MuStepB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open Work.FTS.EllSol.PkgK5.K5c

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-! ## Step B — integration in `θ` -/

/-- Measurability of the `ℝ≥0∞`-valued radial weight `muWHat`. -/
lemma mu_measurable_wHat : Measurable muWHat := by
  unfold muWHat
  exact ENNReal.measurable_ofReal.comp (mu_measurable_w.pow_const 2)

/-- **Step B.**  `muMHat F ≤ 3 · muNHat δ ε X`. -/
theorem mu_MHat_le {F X : ℝ → ℝ → ℝ} {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hdom : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ θ ∈ Iθ,
      |F z θ| ≤ ∫ t : ℝ, sKer δ (Real.log z - t) *
        (∫ s in Iθ, KJ ε θ s * |X (Real.exp t) s|))
    (hFhon : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (F z θ) ^ 2 * σθ θ) Iθ)
    (hXhon : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (X z θ) ^ 2 * σθ θ) Iθ)
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ))) :
    muMHat F ≤ 3 * muNHat δ ε X := by
  change (∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * σθ θ)))
    ≤ 3 * (∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ))
  have hpt := mu_pointwise hδ hδ2 hε hε2 hdom hXhon hXmeas
  have hstep : (∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * σθ θ)))
      ≤ ∫⁻ z in Iz, muWHat z * (3 * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hpt] with z hz
    refine mul_le_mul' le_rfl ?_
    calc (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * σθ θ))
        ≤ ∫⁻ θ in Iθ, 3 * (muSigHat θ * muQHat δ ε X z θ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hz]
            with θ hθ
          calc ENNReal.ofReal ((F z θ) ^ 2 * σθ θ)
              ≤ 3 * muSigHat θ * muQHat δ ε X z θ := hθ
            _ = 3 * (muSigHat θ * muQHat δ ε X z θ) := by ring
      _ = 3 * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ) :=
          MeasureTheory.lintegral_const_mul' 3 _ mu_three_ne_top
  have hstep2 : (∫⁻ z in Iz, muWHat z
        * (3 * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)))
      = 3 * ∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ) := by
    rw [show (∫⁻ z in Iz, muWHat z
          * (3 * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)))
        = ∫⁻ z in Iz, 3 * (muWHat z
            * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)) from
      lintegral_congr (fun z => by ring)]
    exact MeasureTheory.lintegral_const_mul' _ _ mu_three_ne_top
  exact hstep.trans (le_of_eq hstep2)

/-! ## The radial slice bound -/

/-- `z ↦ w(z)² sKer δ (log z - t)` is integrable on `(0,∞)`. -/
lemma mu_integrableOn_wsKer {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (t : ℝ) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * sKer δ (Real.log z - t))
      (Set.Ioi 0) := by
  rw [← MeasureTheory.integrable_comp_exp
    (fun z : ℝ => (Work.Spaces.w z) ^ 2 * sKer δ (Real.log z - t))]
  have hker : Integrable (fun x : ℝ => sKer δ (x - t)) volume :=
    (Work.FTS.EllSol.EllPkgAux.lj_sKer_integrable hδ).comp_sub_right t
  refine Integrable.mono' (hker.const_mul (5 * ljOm t)) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine Real.continuous_exp.measurable.smul ?_
    exact ((mu_measurable_w.comp Real.continuous_exp.measurable).pow_const 2).mul
      ((Work.FTS.EllSol.K5cAux.continuous_sKer δ).measurable.comp
        ((Real.measurable_log.comp Real.continuous_exp.measurable).sub measurable_const))
  · filter_upwards with x
    have hx : (Real.exp x • ((Work.Spaces.w (Real.exp x)) ^ 2
          * sKer δ (Real.log (Real.exp x) - t)))
        = Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2 * sKer δ (x - t)) := by
      rw [smul_eq_mul, Real.log_exp]
    rw [hx, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos x).le
      (mul_nonneg (sq_nonneg _) (sKer_nonneg hδ _)))]
    by_cases hcomp : |x - t| ≤ 1 / 2
    · have hc := Work.FTS.EllSol.EllPkgAux.wExpCmp x t hcomp
      calc Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2 * sKer δ (x - t))
          = (Real.exp x * (Work.Spaces.w (Real.exp x)) ^ 2) * sKer δ (x - t) := by ring
        _ ≤ (5 * ljOm t) * sKer δ (x - t) := by
            refine mul_le_mul_of_nonneg_right ?_ (sKer_nonneg hδ _)
            rw [ljOm]
            linarith [hc]
    · have hz : sKer δ (x - t) = 0 := sKer_eq_zero_of_le_abs hδ (by
        have h : 1 / 2 < |x - t| := not_le.mp hcomp
        linarith [hδ2])
      rw [hz]
      simpa only [mul_zero] using le_refl (0 : ℝ)

/-- The radial slice bound in `ℝ≥0∞`: `∫⁻_z w² k δ z t ≤ ofReal (5 Ω t)`. -/
lemma mu_lintegral_wsKer_le {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (t : ℝ) :
    (∫⁻ z in Iz, muWHat z * muKHat δ z t) ≤ ENNReal.ofReal (5 * ljOm t) := by
  rw [mu_Ioi]
  have h1 : (∫⁻ z in Set.Ioi (0 : ℝ), muWHat z * muKHat δ z t)
      = ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * sKer δ (Real.log z - t)) := by
    have hfun : (fun z : ℝ => muWHat z * muKHat δ z t)
        = fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * sKer δ (Real.log z - t)) := by
      funext z
      exact muWHat_mul_muKHat δ z t
    rw [hfun]
  rw [h1, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (mu_integrableOn_wsKer hδ hδ2 t)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z _ => mul_nonneg (sq_nonneg _) (sKer_nonneg hδ _)))]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa only [ljOm, Real.log_exp] using
    Work.FTS.ClassC.UopGenAux.wsq_sKer_log_integral_le (δ := δ) (y := Real.exp t)
      hδ hδ2 (Real.exp_pos t)

/-! ## The change of variables `z = e^t` -/

/-- **The change of variables.**  The `Ω`-weighted `t`-integral of the slice functional of `X`
equals `ofReal` of the `w²`-weighted `z`-integral. -/
lemma mu_expChange (X : ℝ → ℝ → ℝ)
    (hXhon : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (X z θ) ^ 2 * σθ θ) Iθ)
    (hXint : IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)) Iz) :
    (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
        * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      = ENNReal.ofReal (∫ z in Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)) := by
  have hMmnn : ∀ t : ℝ, 0 ≤ MmV X t := fun t =>
    integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun s hs => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs)))
  have hIoi : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)) (Set.Ioi (0 : ℝ)) := by
    change MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)) (volume.restrict Iz) at hXint
    rw [mu_Ioi] at hXint
    exact hXint
  have hφ : Integrable (fun t : ℝ => ljOm t * MmV X t) volume := by
    have h := (MeasureTheory.integrable_comp_exp (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ))).mpr hIoi
    refine h.congr (Eventually.of_forall (fun x => ?_))
    simp only [smul_eq_mul, ljOm, MmV]
    ring
  have hR : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 *
        (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ))
      = ∫ t : ℝ, ljOm t * MmV X t := by
    rw [← MeasureTheory.integral_comp_exp (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ))]
    refine integral_congr_ae (Eventually.of_forall (fun s => ?_))
    simp only [smul_eq_mul, ljOm, MmV]
    ring
  have hIz : (∫ z in Iz, (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ))
      = ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 *
          (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
  calc (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
        * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      = ∫⁻ t : ℝ, ENNReal.ofReal (ljOm t) * ENNReal.ofReal (MmV X t) :=
        lintegral_congr (fun t => by rw [mu_VsHat_eq hXhon t])
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (ljOm t * MmV X t) :=
        lintegral_congr (fun t => by rw [ENNReal.ofReal_mul (ljOm_nonneg t)])
    _ = ENNReal.ofReal (∫ t : ℝ, ljOm t * MmV X t) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφ
          (Eventually.of_forall (fun t => mul_nonneg (ljOm_nonneg t) (hMmnn t)))).symm
    _ = ENNReal.ofReal (∫ z in Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Iθ, (X z θ) ^ 2 * σθ θ)) := by rw [hIz, hR]

/-! ## Step C — the `z`-integration and the radial Schur step -/

/-- **Step C.**  `muNHat δ ε X` is bounded by `ofReal (5 K₁)` times the `Ω`-weighted `t`-integral
of the slice functional of `X`. -/
theorem mu_NHat_le {X : ℝ → ℝ → ℝ} {δ ε K₁ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hε : 0 < ε)
    (hXhon : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (X z θ) ^ 2 * σθ θ) Iθ)
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ)))
    (hK₁pos : 0 < K₁)
    (hSchur : ∀ u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ θ in Iθ, σθ θ * KJ ε θ u) ≤ K₁ * σθ u) :
    muNHat δ ε X ≤ ENNReal.ofReal (5 * K₁)
      * (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) := by
  change (∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ))
    ≤ ENNReal.ofReal (5 * K₁)
      * (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
  have hVs_aesm : AEMeasurable (fun t : ℝ => ∫⁻ s in Iθ, muXsHat X t s * muSigHat s) volume :=
    ((mu_aemeasurable_XsHat hXmeas).mul (mu_aemeasurable_sigHat.comp_snd)).lintegral_prod_right'
  have hVs_ne : ∀ t : ℝ, (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) ≠ ⊤ := fun t => by
    rw [mu_VsHat_eq hXhon t]
    exact ENNReal.ofReal_ne_top
  have hStep1 : (∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ))
      ≤ ∫⁻ z in Iz, muWHat z * (ENNReal.ofReal K₁ * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))) := by
    refine lintegral_mono (fun z => ?_)
    exact mul_le_mul' le_rfl (mu_schurSwap hε hK₁pos.le hXmeas hSchur z)
  have hStep2 : (∫⁻ z in Iz, muWHat z * (ENNReal.ofReal K₁ * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))))
      = ENNReal.ofReal K₁ * ∫⁻ z in Iz, muWHat z * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) := by
    rw [show (∫⁻ z in Iz, muWHat z * (ENNReal.ofReal K₁ * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))))
        = ∫⁻ z in Iz, ENNReal.ofReal K₁ * (muWHat z * (∫⁻ t, muKHat δ z t
            * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))) from
      lintegral_congr (fun z => by ring)]
    exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hpull : (∫⁻ z in Iz, muWHat z * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)))
      = ∫⁻ z in Iz, ∫⁻ t, (muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) := by
    refine lintegral_congr (fun z => ?_)
    exact (MeasureTheory.lintegral_const_mul' (muWHat z) _
      ENNReal.ofReal_ne_top).symm.trans (lintegral_congr (fun t => by ring))
  have hswap : (∫⁻ z in Iz, ∫⁻ t, (muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      = ∫⁻ t, ∫⁻ z in Iz, (muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) :=
    MeasureTheory.lintegral_lintegral_swap (μ := volume.restrict Iz) (ν := volume)
      (f := fun z t : ℝ =>
        (muWHat z * muKHat δ z t) * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      (((mu_measurable_wHat.comp measurable_fst).aemeasurable.mul
        (mu_measurable_kHat' δ).aemeasurable).mul (hVs_aesm.comp_snd))
  have hsplit : (∫⁻ t, ∫⁻ z in Iz, (muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      = ∫⁻ t, (∫⁻ z in Iz, muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) :=
    lintegral_congr (fun t => MeasureTheory.lintegral_mul_const' _ _ (hVs_ne t))
  have hStep3 : (∫⁻ t, (∫⁻ z in Iz, muWHat z * muKHat δ z t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      ≤ ∫⁻ t, ENNReal.ofReal (5 * ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) := by
    refine lintegral_mono (fun t => ?_)
    exact mul_le_mul' (mu_lintegral_wsKer_le hδ hδ2 t) le_rfl
  have hZE : (∫⁻ z in Iz, muWHat z * (∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)))
      ≤ ∫⁻ t, ENNReal.ofReal (5 * ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) :=
    (hpull.trans (hswap.trans hsplit)).le.trans hStep3
  have hW : ENNReal.ofReal K₁ * (∫⁻ t, ENNReal.ofReal (5 * ljOm t)
        * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
      = ENNReal.ofReal (5 * K₁) * (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) := by
    have hA : (∫⁻ t, ENNReal.ofReal (5 * ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
        = ENNReal.ofReal 5 * (∫⁻ t : ℝ, ENNReal.ofReal (ljOm t)
            * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) := by
      rw [show (∫⁻ t, ENNReal.ofReal (5 * ljOm t)
            * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s))
          = ∫⁻ t, ENNReal.ofReal 5 * (ENNReal.ofReal (ljOm t)
              * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) from
        lintegral_congr (fun t => by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5), mul_assoc])]
      exact MeasureTheory.lintegral_const_mul' (ENNReal.ofReal 5)
        (fun t : ℝ => ENNReal.ofReal (ljOm t)
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s)) ENNReal.ofReal_ne_top
    have h5comm : ENNReal.ofReal K₁ * ENNReal.ofReal 5 = ENNReal.ofReal (5 * K₁) :=
      (mul_comm _ _).trans (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)).symm
    rw [hA, ← mul_assoc, h5comm]
  exact (hStep1.trans (le_of_eq hStep2)).trans
    ((mul_le_mul' le_rfl hZE).trans (le_of_eq hW))

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollMix.integrable_sKerd_KJ_pth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the *mixed* kernel `sKerd δ (log z - t) · KJ ε θ s · ∂_θG(eᵗ,s)`

The product-integrability statement behind the Fubini/Tonelli arguments that mix the
log-radial mollification `sKerd δ (log z - ·)` (`δ ≤ 1/2`, supported in `|·| ≤ δ ≤ 1`) with
the angular Jensen kernel `KJ ε θ ·` (`ε ≤ 1/2`) applied to the *angular* derivative
`∂_θG` of a trace-class datum `G` (`TraceClass G`, `FourInts G`).

The proof is a direct application of `MollDom.prod_integrable_of_slice_bound`, whose
hypotheses are exactly what the trace-class structure supplies:

* the radial kernel `sKerd δ` is continuous with compact support in `[-δ, δ]`, hence
  measurable, bounded, and vanishing for `|x| > 1` (`δ ≤ 1/2 < 1`);
* the `t`-slice `s ↦ KJ ε θ s · ∂_θG(eᵗ,s)` is a.e. strongly measurable (the angular
  kernel is continuous and `∂_θG` is continuous on the open quadrant) and integrable on
  `Iθ` for every `t` (dominated by the constant `3(ε·sMass)⁻¹ · sup_s|∂_θG(eᵗ,s)|`);
* the slice integrals are dominated by `3(ε·sMass)⁻¹ √(π/2) MGf G (eᵗ)`, where `MGf G` is
  the slice domination of `MollBase`'s companion `mollSliceBound`:
  `|∂_θG(w,s)| ≤ |∂_θG(w,π/4)| + √(π/2)√(E2s G w) ≤ √(π/2) MGf G w` a.e. in `s`
  (`pthSliceLeE2s`);
* `t ↦ MGf G (eᵗ)` is integrable on compact intervals in the logarithmic variable
  (`PkgK5.i0TraceMoll.integrableOn_MGf_exp_of_trace`, from `FourInts`), and the window
  `[log z - 1, log z + 1]` is compact, so the closed-interval form required by the
  product-integrability lemma follows from the open-interval form by nullity of the
  endpoints.
-/

namespace Work.FTS.EllSol.EllPkgAux.MollDom.ZmollMix

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-! ## Elementary pieces -/

/-- The derivative kernel `sKerd δ = (sKer δ)'` is bounded for `δ > 0`: it is continuous and
supported in `[-δ, δ]`. -/
private theorem sKerd_bdd_of_pos {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ t : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd δ t| ≤ M := by
  have hcontOn : ContinuousOn (Work.FTS.EllSol.EllPkgAux.sKerd δ) (Set.Icc (-δ) δ) :=
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd δ).continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontOn
  refine ⟨max M 0, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-δ) δ
  · have h1 : ‖Work.FTS.EllSol.EllPkgAux.sKerd δ t‖ ≤ M := hM t ht
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  · have hgt : δ < |t| := by
      rw [Set.mem_Icc, not_and_or] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hδ hgt, abs_zero]
    exact le_max_right _ _

/-- **The a.e. slice bound for `∂_θG`**: for `w > 0` and almost every `s ∈ Iθ`,
`|∂_θG(w,s)| ≤ √(π/2) MGf G w`. -/
private theorem abs_pth_le_sqrt_MGf {G : ℝ → ℝ → ℝ}
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) {w : ℝ} (hw : 0 < w)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Work.Spaces.pth G w θ| ≤ Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G w := by
  have hp := Work.FTS.EllSol.PkgK5.i0TraceMoll.PsiAux.pthSliceLeE2s G hT w hw θ hθ.1 hθ.2
  have hsp : (1 : ℝ) ≤ Real.sqrt (Real.pi / 2) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hMG : Work.FTS.EllSol.EllPkgAux.MGf G w
      = 1 + |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)|
        + Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G w) := rfl
  have hA : |Work.Spaces.pth G w (Real.pi / 4)|
      ≤ Real.sqrt (Real.pi / 2) * |Work.Spaces.pth G w (Real.pi / 4)| := by
    nlinarith [hsp, abs_nonneg (Work.Spaces.pth G w (Real.pi / 4))]
  rw [hMG] at *
  nlinarith [hp, hA, hsp, abs_nonneg (G w (Real.pi / 4)),
    Real.sqrt_nonneg (Work.FTS.EllSol.EllPkgAux.E2s G w)]

/-- The a.e. slice bound for the full mixed slice `KJ ε θ s · ∂_θG(eᵗ,s)`. -/
private theorem abs_KJ_pth_slice_le {G : ℝ → ℝ → ℝ}
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) {ε θ c : ℝ} (hε0 : 0 < ε)
    (hc : ∀ s : ℝ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s ≤ c) (hc0 : 0 ≤ c) (t : ℝ) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.FTS.EllSol.EllPkgAux.KJ ε θ s * Work.Spaces.pth G (Real.exp t) s|
        ≤ c * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)) := by
  filter_upwards [Work.FTS.EllSol.EllPkgAux.ae_mem_Ioo_Iθ] with s hs
  have hp := abs_pth_le_sqrt_MGf hT (Real.exp_pos t) hs
  have hKJ := hc s
  rw [abs_mul, abs_of_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε0 θ s)]
  exact mul_le_mul hKJ hp (abs_nonneg _) hc0

/-- The domination `t ↦ MGf G (eᵗ)` is integrable on the closed window
`[log z - 1, log z + 1]`. -/
private theorem phi_integrable (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (K : ℝ) {z : ℝ} (_hz : 0 < z) :
    MeasureTheory.Integrable (fun t : ℝ => K * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))
      (MeasureTheory.volume.restrict (Set.Icc (Real.log z - 1) (Real.log z + 1))) := by
  have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))
      (Set.Ioo (Real.log z - 1) (Real.log z + 1)) :=
    Work.FTS.EllSol.PkgK5.i0TraceMoll.integrableOn_MGf_exp_of_trace G hT hF (by linarith)
  have h2 : MeasureTheory.Integrable (fun t : ℝ => K * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))
      (MeasureTheory.volume.restrict (Set.Ioo (Real.log z - 1) (Real.log z + 1))) := h1.const_mul K
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)
      (a := Real.log z - 1) (b := Real.log z + 1))]
  exact h2

/-! ## The target -/

theorem integrable_sKerd_KJ_pth (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.1)
        * (Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 * Work.Spaces.pth G (Real.exp p.1) p.2))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  obtain ⟨M, hM⟩ := sKerd_bdd_of_pos hδ0
  -- the constant `3(ε sMass)⁻¹` dominating `KJ`
  have hKJ0 : (0 : ℝ) ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ :=
    mul_nonneg (by norm_num)
      (inv_nonneg.mpr (mul_nonneg hε0.le Work.FTS.EllSol.PkgK5.K5c.sMass_pos.le))
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  refine Work.FTS.EllSol.EllPkgAux.MollDom.prod_integrable_of_slice_bound
    (k := Work.FTS.EllSol.EllPkgAux.sKerd δ)
    (w := fun t s => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * Work.Spaces.pth G (Real.exp t) s)
    (Φ := fun t => (Real.pi / 2) * (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
      * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))))
    (M := M) (σ := Real.log z) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd δ).measurable
  · exact hM
  · intro x hx
    exact Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hδ0 (by linarith)
  · -- a.e. strong measurability of the uncurried integrand
    have hA : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.pth G (Real.exp p.1) p.2)
        (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.FTS.EllSol.EllPkgAux.MollDom.aeStronglyMeasurable_exp
        (X := Work.Spaces.pth G) hsm.pth.continuousOn
    have hB : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2)
        (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      ((Work.FTS.EllSol.EllPkgAux.continuous_KJ ε).comp
        (continuous_const.prodMk continuous_snd)).aestronglyMeasurable
    exact hB.mul hA
  · -- integrability of every `t`-slice
    intro t
    have hle := abs_KJ_pth_slice_le hT hε0
      (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ_le hε0 θ s) hKJ0 t
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
        Work.Spaces.Iθ :=
      (hone.const_mul (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))).congr
        (Filter.Eventually.of_forall (fun s => by simp))
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * Work.Spaces.pth G (Real.exp t) s)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hg : ContinuousOn
          (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 * Work.Spaces.pth G p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (((Work.FTS.EllSol.EllPkgAux.continuous_KJ ε).comp
            (continuous_const.prodMk continuous_snd)).continuousOn).mul hsm.pth.continuousOn
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hg (Real.exp_pos t)
    exact MeasureTheory.Integrable.mono' hconst haesm
      (by filter_upwards [hle] with s hs; simpa only [Real.norm_eq_abs] using hs)
  · -- the domination of the slice integrals
    intro t
    have hle := abs_KJ_pth_slice_le hT hε0
      (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ_le hε0 θ s) hKJ0 t
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
        Work.Spaces.Iθ :=
      (hone.const_mul (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))).congr
        (Filter.Eventually.of_forall (fun s => by simp))
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun s : ℝ => |Work.FTS.EllSol.EllPkgAux.KJ ε θ s * Work.Spaces.pth G (Real.exp t) s|)
      (g := fun _ : ℝ => 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
      (Filter.Eventually.of_forall (fun s => abs_nonneg _)) hconst hle
    have hvol : (∫ s in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
      rw [intervalIntegral.integral_const]
      simp
    have hval : (∫ s in Work.Spaces.Iθ, 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
        = (Real.pi / 2) * (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))) := by
      have h1 : (∫ s in Work.Spaces.Iθ, (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
            * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))) * (1 : ℝ))
          = (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
            * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
            * ∫ s in Work.Spaces.Iθ, (1 : ℝ) :=
        MeasureTheory.integral_const_mul _ _
      have h2 : (∫ s in Work.Spaces.Iθ, 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
            * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
          = (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
            * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
            * ∫ s in Work.Spaces.Iθ, (1 : ℝ) := by
        rw [← h1]
        congr 1
        funext s
        ring
      rw [h2, hvol]
      ring
    rw [hval] at hmono
    exact hmono
  · -- integrability of the domination on the compact window
    exact (phi_integrable G hT hF
        (Real.pi / 2 * (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ * Real.sqrt (Real.pi / 2)))
        hz).congr
      (Filter.Eventually.of_forall (fun t => by ring))

end Work.FTS.EllSol.EllPkgAux.MollDom.ZmollMix
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.hasDerivAt_thMoll_fold =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open Work.FTS.EllSol.PkgK5.K5c

set_option maxHeartbeats 1000000

theorem hasDerivAt_thMoll_fold (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {ε w : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hw : 0 < w) :
    ∀ θ ∈ Work.Spaces.Iθ,
      HasDerivAt (fun θ' : ℝ => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε w θ')
        (∫ s in Work.Spaces.Iθ,
          Work.FTS.EllSol.EllPkgAux.Kern (deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε)) θ s
            * G w s) θ := by
  -- the slice `s ↦ G w s` is continuous on `Iθ` (this is where `0 < w` and the endpoint
  -- values/traces of `TraceClass` are used)
  have hgc : ContinuousOn (fun s : ℝ => G w s) Work.Spaces.Iθ :=
    slice_continuousOn G hT hw
  obtain ⟨-, h0, hp, -, -, -, -, -⟩ := hT
  -- the fold identity holds on the whole open window `(-1/4, π/2 + 1/4)` containing `Iθ`
  have hfold : ∀ θ' ∈ Set.Ioo (-(1 / 4 : ℝ)) (Real.pi / 2 + 1 / 4),
      thMoll G ε w θ' = ∫ s in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ' s * G w s := by
    intro θ' hθ'
    rw [Work.FTS.EllSol.EllPkgAux.thMoll_fold hε hε1 (h0 w) (hp w) hgc hθ'.1 hθ'.2,
      Work.FTS.EllSol.EllPkgAux.setIntegral_Iθ_eq_interval]
  obtain ⟨C, hC⟩ := Work.FTS.EllSol.EllPkgAux.exists_bound_deriv_sKer hε
  -- differentiation under the integral sign of the fold
  have hA := Work.FTS.EllSol.EllPkgAux.hasDerivAt_intervalIntegral_Kern
    (ρ := sKer ε) (ρ' := deriv (sKer ε)) (g := fun s : ℝ => G w s) (C := C)
    (a := 0) (b := Real.pi / 2)
    (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.hasDerivAt_sKer ε t) hC (by
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
      exact hgc)
  intro θ hθ
  have h1 : -(1 / 4 : ℝ) < θ := by linarith [hθ.1]
  have h2 : θ < Real.pi / 2 + 1 / 4 := by linarith [hθ.2]
  have hfold_ev : (fun θ' : ℝ => thMoll G ε w θ') =ᶠ[𝓝 θ]
      (fun θ' : ℝ => ∫ s in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ' s * G w s) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨h1, h2⟩) hfold
  have hd1 : HasDerivAt (fun θ' : ℝ => thMoll G ε w θ')
      (∫ s in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.EllSol.EllPkgAux.Kern (deriv (sKer ε)) θ s * G w s) θ :=
    (hA θ).congr_of_eventuallyEq hfold_ev
  simpa only [Work.FTS.EllSol.EllPkgAux.setIntegral_Iθ_eq_interval] using hd1

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.pth_slice_sq_le_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option maxHeartbeats 800000

theorem pth_slice_sq_le_majorant (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) :
    ∀ z : ℝ, 0 < z → ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.pth G z s) ^ 2
        ≤ Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G z := by
  intro z hz s hs
  obtain ⟨hsm, h0, hpi, htr0, htrpi, hdz0, hdzpi, hhon⟩ := hT
  -- ## The `C²`-regularity of the slice
  have hsmo : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => G z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsm.curry_θ hz).of_le hsmo
  -- ## Honesty of the `σ_η`-weighted `∂_θ²`-slice
  have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := pth2_slice_integrable G hhon.1 z hz
  have hq0 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hq1 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- ## The interval Cauchy–Schwarz bound on a subinterval of length `≤ π/4`
  have hkey : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 → b - a ≤ Real.pi / 4 →
      |∫ t in a..b, Work.Spaces.pth (Work.Spaces.pth G) z t|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)
          * Real.sqrt (Real.pi / 4) := by
    intro a b ha hab hb hlen
    have hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
    exact abs_interval_integral_le_sqrt_thEta
      ((Work.FTS.EllSol.c2_continuousOn_deriv_deriv hf2).mono hsub) hInt ha hab hb hlen
  -- ## The pointwise bound, by the fundamental theorem of calculus from the landmark `π/4`
  have hpt : |Work.Spaces.pth G z s|
      ≤ |Work.Spaces.pth G z (Real.pi / 4)|
        + Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) * Real.sqrt (Real.pi / 4) := by
    rcases le_total s (Real.pi / 4) with hle | hge
    · -- ## `s ≤ π/4`: run the fundamental theorem from `s` up to the landmark
      have hFTC : ∫ t in s..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) z t
          = Work.Spaces.pth G z (Real.pi / 4) - Work.Spaces.pth G z s := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := Work.Spaces.pth G z) (f' := Work.Spaces.pth (Work.Spaces.pth G) z) ?_ ?_
        · intro t ht
          rw [Set.uIcc_of_le hle] at ht
          exact Work.FTS.EllSol.c2_hasDerivAt_deriv hf2
            ⟨lt_of_lt_of_le hs.1 ht.1, lt_of_le_of_lt ht.2 hq1⟩
        · exact Work.FTS.EllSol.c2_intervalIntegrable_deriv_deriv hf2 hs.1 hle hq1
      have hsq := hkey s (Real.pi / 4) hs.1 hle hq1 (by linarith [hs.1])
      have heq : Work.Spaces.pth G z s
          = Work.Spaces.pth G z (Real.pi / 4)
            + (- ∫ t in s..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) z t) := by
        rw [hFTC]; ring
      rw [heq]
      calc |Work.Spaces.pth G z (Real.pi / 4)
              + (- ∫ t in s..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) z t)|
          ≤ |Work.Spaces.pth G z (Real.pi / 4)|
            + |∫ t in s..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) z t| := by
            simpa only [abs_neg] using abs_add_le (Work.Spaces.pth G z (Real.pi / 4))
              (- ∫ t in s..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) z t)
        _ ≤ |Work.Spaces.pth G z (Real.pi / 4)|
            + Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) * Real.sqrt (Real.pi / 4) := by
            linarith [hsq]
    · -- ## `π/4 ≤ s`: run the fundamental theorem from the landmark up to `s`
      have hFTC : ∫ t in (Real.pi / 4)..s, Work.Spaces.pth (Work.Spaces.pth G) z t
          = Work.Spaces.pth G z s - Work.Spaces.pth G z (Real.pi / 4) := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := Work.Spaces.pth G z) (f' := Work.Spaces.pth (Work.Spaces.pth G) z) ?_ ?_
        · intro t ht
          rw [Set.uIcc_of_le hge] at ht
          exact Work.FTS.EllSol.c2_hasDerivAt_deriv hf2
            ⟨lt_of_lt_of_le hq0 ht.1, lt_of_le_of_lt ht.2 hs.2⟩
        · exact Work.FTS.EllSol.c2_intervalIntegrable_deriv_deriv hf2 hq0 hge hs.2
      have hsq := hkey (Real.pi / 4) s hq0 hge hs.2 (by linarith [hs.2])
      have heq : Work.Spaces.pth G z s
          = Work.Spaces.pth G z (Real.pi / 4)
            + ∫ t in (Real.pi / 4)..s, Work.Spaces.pth (Work.Spaces.pth G) z t := by
        rw [hFTC]; ring
      rw [heq]
      calc |Work.Spaces.pth G z (Real.pi / 4)
              + ∫ t in (Real.pi / 4)..s, Work.Spaces.pth (Work.Spaces.pth G) z t|
          ≤ |Work.Spaces.pth G z (Real.pi / 4)|
            + |∫ t in (Real.pi / 4)..s, Work.Spaces.pth (Work.Spaces.pth G) z t| :=
            abs_add_le _ _
        _ ≤ |Work.Spaces.pth G z (Real.pi / 4)|
            + Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) * Real.sqrt (Real.pi / 4) := by
            linarith [hsq]
  -- ## Square both sides
  calc (Work.Spaces.pth G z s) ^ 2 = |Work.Spaces.pth G z s| ^ 2 := by rw [← sq_abs]
    _ ≤ (|Work.Spaces.pth G z (Real.pi / 4)|
          + Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) * Real.sqrt (Real.pi / 4)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hpt 2
    _ = Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G z := rfl

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.sliceIbp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-- The derivative of the mollifying kernel `sKer ε` vanishes outside the support of `sKer ε`:
at a point `x` with `ε < |x|` the kernel is locally identically zero, hence so is its
derivative. -/
private theorem deriv_sKer_eq_zero_of_lt_abs {ε x : ℝ} (hε : 0 < ε) (hx : ε < |x|) :
    deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0 := by
  have hev : Work.FTS.EllSol.PkgK5.K5c.sKer ε =ᶠ[nhds x] (fun _ : ℝ => (0 : ℝ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    rcases lt_abs.mp hx with h | h
    · exact ⟨Set.Ioi ε, isOpen_Ioi.mem_nhds h, fun y hy => by
        refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε ?_
        have hy' : ε < y := hy
        rw [abs_of_pos (by linarith)]
        linarith⟩
    · exact ⟨Set.Iio (-ε), isOpen_Iio.mem_nhds (by simp only [Set.mem_Iio]; linarith),
        fun y hy => by
        refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε ?_
        have hy' : y < -ε := hy
        rw [abs_of_neg (by linarith)]
        linarith⟩
  rw [hev.deriv_eq, deriv_const]

theorem sliceIbp {f f' : ℝ → ℝ} {δ σ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hder : ∀ t : ℝ, HasDerivAt f (f' t) t) (hf'c : Continuous f') :
    ∫ t : ℝ, deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - t) * f t
      = ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (σ - t) * f' t := by
  -- ## the integrands vanish off the window `(σ - 1, σ + 1]`, so the integrals over `ℝ` are the
  -- interval integrals over `[σ - 1, σ + 1]`
  have key_gl : ∀ g : ℝ → ℝ, (∀ t : ℝ, t ∉ Set.Ioc (σ - 1) (σ + 1) → g t = 0) →
      (∫ t : ℝ, g t) = ∫ t in (σ - 1)..(σ + 1), g t := by
    intro g hg
    rw [intervalIntegral.integral_of_le (show σ - 1 ≤ σ + 1 by linarith)]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hg).symm
  have hlt : ∀ t : ℝ, t ∉ Set.Ioc (σ - 1) (σ + 1) → δ < |σ - t| := by
    intro t ht
    rw [Set.mem_Ioc, not_and_or] at ht
    rcases ht with h | h
    · rw [not_lt] at h
      rw [abs_of_pos (by linarith)]; linarith
    · rw [not_le] at h
      rw [abs_of_neg (by linarith)]; linarith
  have hvan_d : ∀ t : ℝ, t ∉ Set.Ioc (σ - 1) (σ + 1) →
      deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - t) * f t = 0 := by
    intro t ht
    rw [deriv_sKer_eq_zero_of_lt_abs hδ (hlt t ht), zero_mul]
  have hvan_k : ∀ t : ℝ, t ∉ Set.Ioc (σ - 1) (σ + 1) →
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (σ - t) * f' t = 0 := by
    intro t ht
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (le_of_lt (hlt t ht)), zero_mul]
  rw [key_gl _ hvan_d, key_gl _ hvan_k]
  -- ## integration by parts on the interval `[σ - 1, σ + 1]`
  have hu : ∀ x ∈ Set.uIcc (σ - 1) (σ + 1),
      HasDerivAt (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (σ - t))
        (-(deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - x))) x := by
    intro x _
    have h : HasDerivAt (Work.FTS.EllSol.PkgK5.K5c.sKer δ)
        (deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - x)) (σ - x) :=
      ((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).differentiable_one (σ - x)).hasDerivAt
    exact h.comp_const_sub σ x
  have hv : ∀ x ∈ Set.uIcc (σ - 1) (σ + 1), HasDerivAt f (f' x) x := fun x _ => hder x
  have hu' : IntervalIntegrable (fun t : ℝ => -(deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - t)))
      volume (σ - 1) (σ + 1) :=
    ((((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous_deriv_one).comp
      (continuous_const.sub continuous_id)).neg).intervalIntegrable _ _
  have hv' : IntervalIntegrable f' volume (σ - 1) (σ + 1) := hf'c.intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  -- ## the two boundary terms vanish because `sKer δ (±1) = 0` (`δ ≤ 1/2`)
  have hb1 : Work.FTS.EllSol.PkgK5.K5c.sKer δ (σ - (σ + 1)) = 0 := by
    rw [show σ - (σ + 1) = -1 by ring]
    exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (by rw [abs_neg, abs_one]; linarith)
  have hb2 : Work.FTS.EllSol.PkgK5.K5c.sKer δ (σ - (σ - 1)) = 0 := by
    rw [show σ - (σ - 1) = 1 by ring]
    exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (by rw [abs_one]; linarith)
  rw [hb1, hb2] at h
  simp only [zero_mul, zero_sub, neg_zero] at h
  have hkey : (∫ x in (σ - 1)..(σ + 1), deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - x) * f x)
      = -(∫ x in (σ - 1)..(σ + 1),
          (-(deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - x))) * f x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hkey, h]

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.win_majorant_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Two elementary facts about the logarithmic window -/

/-- The logarithmic window `{|log z - t| ≤ δ}` is the compact interval
`[log z - δ, log z + δ]`. -/
theorem win_window_eq_Icc {δ z : ℝ} :
    {t : ℝ | |Real.log z - t| ≤ δ} = Set.Icc (Real.log z - δ) (Real.log z + δ) := by
  ext t
  rw [Set.mem_ofPred_eq, abs_le, Set.mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- The logarithmic window has finite Lebesgue measure. -/
theorem win_window_ne_top {δ z : ℝ} :
    (MeasureTheory.volume {t : ℝ | |Real.log z - t| ≤ δ}) ≠ ⊤ := by
  rw [win_window_eq_Icc]
  exact (isCompact_Icc.measure_lt_top).ne

/-! ## The elementary bound on the majorant -/

/-- The squared majorant `(|a| + √b · √(π/4))²` is dominated by `2 M² + 2 b` as soon as
`|a| ≤ M` and `0 ≤ b`: expand the square, use `√b² = b`, and `√(π/4)² = π/4 ≤ 1`. -/
theorem sq_majorant_le (a b M : ℝ) (ha : |a| ≤ M) (hb : 0 ≤ b) :
    (|a| + Real.sqrt b * Real.sqrt (Real.pi / 4)) ^ 2 ≤ 2 * M ^ 2 + 2 * b := by
  have h1 : (|a| + Real.sqrt b * Real.sqrt (Real.pi / 4)) ^ 2
      ≤ 2 * |a| ^ 2 + 2 * (Real.sqrt b * Real.sqrt (Real.pi / 4)) ^ 2 := by
    nlinarith [sq_nonneg (|a| - Real.sqrt b * Real.sqrt (Real.pi / 4))]
  have h2 : 2 * |a| ^ 2 ≤ 2 * M ^ 2 := by nlinarith [ha, abs_nonneg a]
  have h3 : 2 * (Real.sqrt b * Real.sqrt (Real.pi / 4)) ^ 2 ≤ 2 * b := by
    have h := Real.sq_sqrt hb
    rw [mul_pow, h, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi / 4)]
    nlinarith [Real.pi_lt_four, hb]
  linarith

/-! ## The majorant is integrable along the logarithmic window -/

/-- **Integrability of the windowed slice majorant.**  For a trace-class datum `G`, the
pointwise majorant `thSliceMajorant G (exp t)` of the angular derivative of the slice at radius
`exp t` is integrable on the logarithmic window `|log z - t| ≤ δ`.

The window is compact, so the landmark value `|∂_θG(exp t, π/4)|` is bounded on it (the datum is
`C^∞` on the open quadrant), while the slice energy
`∫_θ (∂_θ²G(exp t, θ))² σ_η θ` is window-integrable by `window_ttIntS_integrable`; the majorant
is dominated by `2M² + 2·(slice energy)` there. -/
theorem win_majorant_integrable (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ z : ℝ) (hδ : 0 < δ) (hz : 0 < z) :
    MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ
        then Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G (Real.exp t) else 0) := by
  -- ## the window is measurable and of finite measure
  have hWmeas : MeasurableSet {t : ℝ | |Real.log z - t| ≤ δ} :=
    measurableSet_le (continuous_abs.comp (continuous_const.sub continuous_id)).measurable
      measurable_const
  have hWtop : (MeasureTheory.volume {t : ℝ | |Real.log z - t| ≤ δ}) ≠ ⊤ :=
    win_window_ne_top
  -- ## the slice energy is nonnegative and, windowed, integrable
  have hBnn : ∀ t : ℝ, 0 ≤ (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) := by
    intro t
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hBint : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) else 0) :=
    (window_ttIntS_integrable G hT hF δ z hδ hz).2
  -- ## the landmark value is continuous along `t ↦ exp t`, hence bounded on the window
  have hAcont : Continuous (fun t : ℝ => Work.Spaces.pth G (Real.exp t) (Real.pi / 4)) := by
    have hq0 : (0 : ℝ) < Real.pi / 4 := by positivity
    have hq1 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
    have hmap : Continuous (fun t : ℝ => (Real.exp t, Real.pi / 4)) :=
      Real.continuous_exp.prodMk continuous_const
    exact (hT.1.pth).continuousOn.comp_continuous hmap (fun t => ⟨Real.exp_pos t, hq0, hq1⟩)
  obtain ⟨M, hM0, hAM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |Real.log z - t| ≤ δ →
      |Work.Spaces.pth G (Real.exp t) (Real.pi / 4)| ≤ M := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hAcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (Real.log z - δ) (Real.log z + δ) := by
      rw [← win_window_eq_Icc]
      exact ht
    rw [← Real.norm_eq_abs]
    exact le_trans (hC t ht') (le_max_left _ _)
  -- ## the integrable majorant `2M² + 2·(slice energy)`
  have hmaj1 : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then 2 * M ^ 2 else 0) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff (f := fun _ : ℝ => 2 * M ^ 2) hWmeas).mpr
      (MeasureTheory.integrableOn_const hWtop)
  have hmaj2 : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) else 0) MeasureTheory.volume := by
    refine (hBint.const_mul 2).congr (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : |Real.log z - t| ≤ δ <;> simp [ht]
  have hmaj : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then 2 * M ^ 2 + 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) else 0) MeasureTheory.volume := by
    refine (hmaj1.add hmaj2).congr (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : |Real.log z - t| ≤ δ <;> simp [ht]
  -- ## the target function, written with the two windowed factors
  have htarget : ∀ t : ℝ,
      (if |Real.log z - t| ≤ δ
          then Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G (Real.exp t) else 0)
        = ((if |Real.log z - t| ≤ δ
              then |Work.Spaces.pth G (Real.exp t) (Real.pi / 4)| else 0)
            + Real.sqrt (if |Real.log z - t| ≤ δ then (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) else 0)
              * Real.sqrt (Real.pi / 4)) ^ 2 := by
    intro t
    by_cases ht : |Real.log z - t| ≤ δ
    · rw [if_pos ht, if_pos ht, if_pos ht]
      rfl
    · rw [if_neg ht, if_neg ht, if_neg ht, Real.sqrt_zero, zero_mul, add_zero, sq, mul_zero]
  -- ## a.e. strong measurability of the target
  have htarget_aesm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ
        then Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G (Real.exp t) else 0)
      MeasureTheory.volume := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
        ((if |Real.log z - t| ≤ δ
              then |Work.Spaces.pth G (Real.exp t) (Real.pi / 4)| else 0)
            + Real.sqrt (if |Real.log z - t| ≤ δ then (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) else 0)
              * Real.sqrt (Real.pi / 4)) ^ 2) MeasureTheory.volume :=
      ((hAcont.abs.aestronglyMeasurable.indicator hWmeas).add
        ((Real.continuous_sqrt.comp_aestronglyMeasurable hBint.aestronglyMeasurable).mul
          aestronglyMeasurable_const)).pow 2
    refine h1.congr (Filter.Eventually.of_forall fun t => ?_)
    exact (htarget t).symm
  -- ## pointwise domination by the majorant
  refine MeasureTheory.Integrable.mono' hmaj htarget_aesm ?_
  filter_upwards with t
  by_cases ht : |Real.log z - t| ≤ δ
  · rw [if_pos ht, if_pos ht, Real.norm_of_nonneg (thSliceMajorant_nonneg G (Real.exp t))]
    have h1 : Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G (Real.exp t)
        = (|Work.Spaces.pth G (Real.exp t) (Real.pi / 4)|
            + Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) * Real.sqrt (Real.pi / 4)) ^ 2 := rfl
    rw [h1]
    exact sq_majorant_le _ _ M (hAM t ht) (hBnn t)
  · rw [if_neg ht, if_neg ht]
    simp

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zSchur_sq_le_window =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The logarithmic Schur bound on the window, with the explicit constant.**

For `δ > 0` and a kernel `K = sKerd δ` which is bounded by `M` and vanishes off `[-δ, δ]`, the
functional `y ↦ ∫ t, K (log z - t) · y t` satisfies

  `(∫ t, K (log z - t) · y t)² ≤ 2 δ M² ∫ t, 1_{|log z - t| ≤ δ} y t²`

for every `y` whose windowed square is integrable (and whose windowed restriction is
a.e.-strongly measurable).  The right-hand side only sees the window
`S = [log z - δ, log z + δ]`, on which the kernel lives and on which it is bounded by `M`; the
integral of `K²` over `S` is therefore at most `M² · |S| = 2 δ M²`, and Cauchy–Schwarz
(`Work.Spaces.cs_integral`) on the window finishes. -/
theorem zSchur_sq_le_window {δ z M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hk : ∀ u : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd δ u| ≤ M)
    (hvan : ∀ u : ℝ, δ < |u| → Work.FTS.EllSol.EllPkgAux.sKerd δ u = 0)
    {y : ℝ → ℝ} (hz : 0 < z)
    (hy : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then y t ^ 2 else 0))
    (hym : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then y t else 0) MeasureTheory.volume) :
    (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * y t) ^ 2
      ≤ 2 * δ * M ^ 2 * (∫ t : ℝ, if |Real.log z - t| ≤ δ then y t ^ 2 else 0) := by
  -- The window on which the kernel lives.
  set S : Set ℝ := Set.Icc (Real.log z - δ) (Real.log z + δ) with hSdef
  have hSmeas : MeasurableSet S := by rw [hSdef]; exact measurableSet_Icc
  haveI : IsFiniteMeasure (volume.restrict S) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, hSdef, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- Membership in `S` is membership in the window.
  have hmem : ∀ t : ℝ, t ∈ S ↔ |Real.log z - t| ≤ δ := by
    intro t
    rw [hSdef, Set.mem_Icc, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  -- The window has length `2 δ`.
  have hrealS : volume.real S = 2 * δ := by
    have hvolS : volume S = ENNReal.ofReal (2 * δ) := by
      rw [hSdef, Real.volume_Icc]; congr 1; ring
    rw [MeasureTheory.Measure.real_def, hvolS, ENNReal.toReal_ofReal (by linarith)]
  -- The kernel as a function of `t`, and the windowed datum.
  set F : ℝ → ℝ := fun t => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) with hFdef
  set g : ℝ → ℝ := fun t => if |Real.log z - t| ≤ δ then y t else 0 with hgdef
  -- The kernel vanishes off the window.
  have hFzero : ∀ t : ℝ, t ∉ S → F t = 0 := by
    intro t ht
    rw [hFdef]
    exact hvan _ (lt_of_not_ge (fun hc => ht ((hmem t).mpr hc)))
  -- The square of the windowed datum is the windowed square.
  have hgsq : ∀ t : ℝ, g t ^ 2 = (if |Real.log z - t| ≤ δ then y t ^ 2 else 0) := by
    intro t
    simp only [hgdef]
    by_cases h : |Real.log z - t| ≤ δ
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; norm_num
  -- The kernel is continuous, hence a.e.-strongly measurable.
  have hFcont : Continuous F := by
    rw [hFdef]
    exact (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd δ).comp
      (continuous_const.sub continuous_id)
  -- `F ∈ L²` on the window: it is bounded there by `M`.
  have hFmem : MemLp F 2 (volume.restrict S) :=
    MemLp.of_bound
      (hFcont.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self) M
      (MeasureTheory.ae_restrict_of_forall_mem hSmeas (fun t _ => by
        rw [Real.norm_eq_abs, hFdef]; exact hk (Real.log z - t)))
  -- `g ∈ L²` on the window: the hypotheses give exactly this.
  have hg_int : Integrable (fun t : ℝ => g t ^ 2) volume :=
    hy.congr (Eventually.of_forall (fun t => (hgsq t).symm))
  have hgvol : MemLp g 2 volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq (by simpa only [hgdef] using hym)).mpr hg_int
  have hgind : S.indicator g = g := by
    funext t
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      rw [hgdef]
      simp only [if_neg (fun hc => ht ((hmem t).mpr hc))]
  have hgmem : MemLp g 2 (volume.restrict S) :=
    (MeasureTheory.memLp_indicator_iff_restrict (μ := volume) (f := g) (p := 2) (s := S)
      hSmeas).mp (by rwa [hgind])
  -- Cauchy–Schwarz on the window.
  have hcs := Work.Spaces.cs_integral (u := F) (v := g) hFmem hgmem
  -- The windowed `L²`-norm of the kernel is at most `2 δ M²`.
  have hFbound : ∫ t in S, F t ^ 2 ≤ 2 * δ * M ^ 2 := by
    have hpt : ∀ t : ℝ, F t ^ 2 ≤ M ^ 2 := by
      intro t
      have habs : |F t| ≤ M := by rw [hFdef]; exact hk (Real.log z - t)
      rw [show F t ^ 2 = |F t| ^ 2 by rw [sq_abs]]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have h1 : ∫ t in S, F t ^ 2 ≤ ∫ t in S, M ^ 2 :=
      MeasureTheory.setIntegral_mono_ae hFmem.integrable_sq
        (MeasureTheory.integrable_const (M ^ 2)) (Eventually.of_forall hpt)
    calc ∫ t in S, F t ^ 2 ≤ ∫ t in S, M ^ 2 := h1
      _ = volume.real S * M ^ 2 := by rw [MeasureTheory.setIntegral_const, smul_eq_mul]
      _ = 2 * δ * M ^ 2 := by rw [hrealS]
  have hgnn : 0 ≤ ∫ t in S, g t ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  -- The windowed square integral is the one displayed in the statement.
  have hwind : ∫ t in S, g t ^ 2 = ∫ t : ℝ, if |Real.log z - t| ≤ δ then y t ^ 2 else 0 := by
    rw [← MeasureTheory.integral_indicator (μ := volume) hSmeas (f := fun t => g t ^ 2)]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun t => ?_))
    simp only [Set.indicator_apply]
    rw [hgsq t]
    by_cases ht : t ∈ S
    · rw [if_pos ht, if_pos ((hmem t).mp ht)]
    · rw [if_neg ht, if_neg (fun hc => ht ((hmem t).mpr hc))]
  -- The integral against `y` is already an integral over the window.
  have hstep1 : ∫ t : ℝ, F t * y t = ∫ t in S, F t * g t := by
    calc ∫ t : ℝ, F t * y t = ∫ t : ℝ, F t * g t :=
          MeasureTheory.integral_congr_ae (Eventually.of_forall (fun t => by
            show F t * y t = F t * g t
            by_cases ht : |Real.log z - t| ≤ δ
            · rw [hgdef]; simp only [if_pos ht]
            · have htS : t ∉ S := fun hc => ht ((hmem t).mp hc)
              rw [hFzero t htS, hgdef]; simp only [if_neg ht, mul_zero, zero_mul]))
      _ = ∫ t in S, F t * g t :=
          (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
            (f := fun t => F t * g t) (fun t ht => by rw [hFzero t ht, zero_mul])).symm
  calc (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * y t) ^ 2
      = (∫ t : ℝ, F t * y t) ^ 2 := rfl
    _ = (∫ t in S, F t * g t) ^ 2 := by rw [hstep1]
    _ ≤ (∫ t in S, F t ^ 2) * (∫ t in S, g t ^ 2) := hcs
    _ ≤ (2 * δ * M ^ 2) * (∫ t in S, g t ^ 2) := mul_le_mul_of_nonneg_right hFbound hgnn
    _ = 2 * δ * M ^ 2 * (∫ t : ℝ, if |Real.log z - t| ≤ δ then y t ^ 2 else 0) := by
          rw [hwind]

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollKernelLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option maxHeartbeats 1000000

/-- **The kernel-moment limit**, for an arbitrary `C²` function `F` on an open set and the
*uncurried* form of the integral. -/
theorem mollKernelLimit {H : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {x y : ℝ} (hU : IsOpen U)
    (hxy : (x, y) ∈ U) (hH : ContDiffOn ℝ 2 (Function.uncurry H) U) :
    Filter.Tendsto
      (fun t : ℝ => ∫ u : ℝ, ∫ v : ℝ,
        Work.FTS.EllSol.EllPkgAux.sKerd t u * Work.FTS.EllSol.EllPkgAux.sKerd t v *
          H (x - u) (y - v))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (deriv (fun x' => deriv (fun y' => H x' y') y) x)) := by
  have hred : (fun t : ℝ => ∫ u : ℝ, ∫ v : ℝ,
        Work.FTS.EllSol.EllPkgAux.sKerd t u * Work.FTS.EllSol.EllPkgAux.sKerd t v *
          H (x - u) (y - v))
      = fun t : ℝ => ∫ u : ℝ, sKerd t u *
          (∫ v : ℝ, sKerd t v * Function.uncurry H (x - u, y - v)) := by
    funext t
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show (∫ v : ℝ, sKerd t u * sKerd t v * H (x - u) (y - v))
      = sKerd t u * (∫ v : ℝ, sKerd t v * Function.uncurry H (x - u, y - v))
    have hpt : (fun v : ℝ => sKerd t u * sKerd t v * H (x - u) (y - v))
        = fun v : ℝ => sKerd t u * (sKerd t v * Function.uncurry H (x - u, y - v)) := by
      funext v; simp only [Function.uncurry_apply_pair]; ring
    rw [hpt, MeasureTheory.integral_const_mul]
  rw [hred, mixedPartialEq hU hxy hH]
  exact mollKernel_aux hU hxy hH

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.dthBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The strip `ℝ × (0,π/2)` on which `NiceFlat` data are smooth. -/
private abbrev strip : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_strip : IsOpen strip := isOpen_univ.prod isOpen_Ioo

private lemma measurableSet_strip : MeasurableSet strip :=
  MeasurableSet.univ.prod measurableSet_Ioo

private lemma sin_two_pos_of_mem_strip {p : ℝ × ℝ} (hp : p ∈ strip) :
    0 < Real.sin (2 * p.2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])

private lemma sin_two_nonneg_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The angular weight `sin(2θ)^{-η}` is nonnegative on `Iθ`. -/
private lemma wE_nonneg_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Icc hθ) _

/-- An (uncurried) function continuous on the strip has its square times `sin(2θ)^{-η}`
strongly measurable for the product of Lebesgue measure with the restriction to `Iθ`. -/
private lemma aesm_joint {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) strip) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) strip :=
    (hf.pow 2).mul
      (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem_strip hp))))
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume.prod volume).restrict strip) :=
    hcont.aestronglyMeasurable measurableSet_strip
  have hvol : (volume : Measure (ℝ × ℝ)) = Measure.prod (volume : Measure ℝ) volume := rfl
  have hstrip : ((volume : Measure (ℝ × ℝ)).restrict strip)
      = (volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [hvol, ← Measure.prod_restrict, Measure.restrict_univ]
    congr 1
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hstrip]
  exact h1

theorem dthBound : ∀ (g : ℝ → ℝ → ℝ), Work.FTS.EllSol.FlatFT.NiceFlat g →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth g) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) (Set.univ ×ˢ Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pth g p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (g p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) (Set.univ ×ˢ Work.Spaces.Iθ) := by
  intro g hg h2
  set ν : Measure ℝ := volume.restrict Work.Spaces.Iθ with hν
  have hθ₁ : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  -- the hypothesis in product form
  have h2' : Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth g) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod ν) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = Measure.prod (volume : Measure ℝ) volume := rfl
    rw [IntegrableOn, hvol, ← Measure.prod_restrict, Measure.restrict_univ] at h2
    rw [hν]
    exact h2
  -- a.e. slice integrability of the second-derivative slot, and its `z`-integral
  have h2slice : ∀ᵐ z ∂(volume : Measure ℝ), Integrable (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ν := h2'.prod_right_ae
  have hNint : Integrable (fun z : ℝ => ∫ θ, (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν) volume := by
    have h := h2'.integral_norm_prod_left
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (wE_nonneg_of_mem_Icc hθ))
  -- strong measurability of the two joint integrands
  have hsmP1 : ContinuousOn (Function.uncurry (Work.Spaces.pth g)) strip :=
    (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pth_fin isOpen_strip hg.1).continuousOn
  have hsmP0 : ContinuousOn (Function.uncurry g) strip := hg.1.continuousOn
  have haesm1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.pth g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod ν) := by
    rw [hν]
    exact aesm_joint hsmP1
  have haesm0 : AEStronglyMeasurable (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod ν) := by
    rw [hν]
    exact aesm_joint hsmP0
  -- the reference values at the fixed interior angle are in `L²(dz)`
  obtain ⟨hc0, hc1⟩ := niceFlatSliceL2 g hg hθ₁
  -- ===== first half: the first derivative =====
  have hF1slice : ∀ᵐ z ∂(volume : Measure ℝ), Integrable (fun θ : ℝ =>
      (Work.Spaces.pth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ν := by
    filter_upwards [h2slice] with z hz
    exact (slicePthBound g hg.1 hθ₁ hz).1
  have hF1bound : ∀ᵐ z ∂(volume : Measure ℝ),
      (∫ θ, (Work.Spaces.pth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
        ≤ (2 * (Real.pi / 2) * (∫ θ, (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
            + 2 * (Work.Spaces.pth g z (Real.pi / 4)) ^ 2)
          * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν) := by
    filter_upwards [h2slice] with z hz
    exact (slicePthBound g hg.1 hθ₁ hz).2
  have hAESMout1 : AEStronglyMeasurable (fun z : ℝ =>
      ∫ θ, (Work.Spaces.pth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
      (volume : Measure ℝ) := haesm1.integral_prod_right'
  have hSconst : Integrable (fun z : ℝ =>
      2 * (Real.pi / 2) * (∫ θ, (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
        + 2 * (Work.Spaces.pth g z (Real.pi / 4)) ^ 2) volume :=
    (hNint.const_mul (2 * (Real.pi / 2))).add (hc1.const_mul 2)
  have hB : Integrable (fun z : ℝ => |(2 * (Real.pi / 2) *
        (∫ θ, (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
        + 2 * (Work.Spaces.pth g z (Real.pi / 4)) ^ 2)
      * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)|) volume :=
    (hSconst.mul_const (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)).abs
  have hF1out : Integrable (fun z : ℝ =>
      ∫ θ, (Work.Spaces.pth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
      volume := by
    refine Integrable.mono' hB hAESMout1 ?_
    filter_upwards [hF1bound] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg_of_ae ?_)]
    · exact le_trans hz (le_abs_self _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (wE_nonneg_of_mem_Icc hθ)
  have hF1 : Integrable (fun p : ℝ × ℝ => (Work.Spaces.pth g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod ν) := by
    rw [integrable_prod_iff haesm1]
    refine ⟨hF1slice, ?_⟩
    refine hF1out.congr (Filter.Eventually.of_forall (fun z => ?_))
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact (Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (wE_nonneg_of_mem_Icc hθ))).symm
  have hF1on : IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) (Set.univ ×ˢ Work.Spaces.Iθ) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = Measure.prod (volume : Measure ℝ) volume := rfl
    rw [IntegrableOn, hvol, ← Measure.prod_restrict, Measure.restrict_univ, ← hν]
    exact hF1
  -- ===== second half: the datum itself =====
  have hN1int : Integrable (fun z : ℝ => ∫ θ, (Work.Spaces.pth g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν) volume := hF1out
  have hF0slice : ∀ᵐ z ∂(volume : Measure ℝ), Integrable (fun θ : ℝ =>
      (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ν := by
    filter_upwards [hF1slice] with z hz
    exact (sliceFunBound g hg.1 hθ₁ hz).1
  have hF0bound : ∀ᵐ z ∂(volume : Measure ℝ),
      (∫ θ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
        ≤ (2 * (Real.pi / 2) * (∫ θ, (Work.Spaces.pth g z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
            + 2 * (g z (Real.pi / 4)) ^ 2)
          * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν) := by
    filter_upwards [hF1slice] with z hz
    exact (sliceFunBound g hg.1 hθ₁ hz).2
  have hAESMout0 : AEStronglyMeasurable (fun z : ℝ =>
      ∫ θ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
      (volume : Measure ℝ) := haesm0.integral_prod_right'
  have hB0 : Integrable (fun z : ℝ => |(2 * (Real.pi / 2) *
        (∫ θ, (Work.Spaces.pth g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
        + 2 * (g z (Real.pi / 4)) ^ 2)
      * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)|) volume :=
    (((hN1int.const_mul (2 * (Real.pi / 2))).add (hc0.const_mul 2)).mul_const
      (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)).abs
  have hF0out : Integrable (fun z : ℝ =>
      ∫ θ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν) volume := by
    refine Integrable.mono' hB0 hAESMout0 ?_
    filter_upwards [hF0bound] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg_of_ae ?_)]
    · exact le_trans hz (le_abs_self _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (wE_nonneg_of_mem_Icc hθ)
  have hF0 : Integrable (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod ν) := by
    rw [integrable_prod_iff haesm0]
    refine ⟨hF0slice, ?_⟩
    refine hF0out.congr (Filter.Eventually.of_forall (fun z => ?_))
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact (Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (wE_nonneg_of_mem_Icc hθ))).symm
  have hF0on : IntegrableOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) (Set.univ ×ˢ Work.Spaces.Iθ) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = Measure.prod (volume : Measure ℝ) volume := rfl
    rw [IntegrableOn, hvol, ← Measure.prod_restrict, Measure.restrict_univ, ← hν]
    exact hF0
  exact ⟨hF1on, hF0on⟩

end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.Shift2Flat.niceRangePlanch =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

open Work.FTS.EllSol.FlatFT (slice slice1 NiceFlat niceFlat_slice_contDiff
  niceFlat_hasCompactSupport niceFlat_hasCompactSupport_pth niceFlat_slice_pth_contDiff
  contDiff_ofReal_comp deriv_ofReal_comp)

namespace Work.FTS.EllSol.Shift2Flat

set_option maxHeartbeats 1000000

/-! ## Elementary facts about the a.e. angle and about complex norms -/

/-- Almost every angle of `Iθ` lies in the open interval `(0, π/2)`. -/
theorem nrp_ae_mem_Ioo :
    ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
  filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)]
    with θ h hmem
  exact h.mpr hmem

/-- `‖(x:ℂ) - b (y:ℂ)‖² = (x - b y)²` for real `x y b`. -/
theorem nrp_normSq_sub (x y b : ℝ) :
    ‖(x : ℂ) - b * (y : ℂ)‖ ^ 2 = (x - b * y) ^ 2 := by
  have h : (x : ℂ) - b * (y : ℂ) = ((x - b * y : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.sq_norm, Complex.normSq_ofReal]
  ring

/-- `‖(x:ℂ) - 2b(y:ℂ) + b²(z:ℂ)‖² = (x - 2by + b²z)²` for real `x y z b`. -/
theorem nrp_normSq_sub2 (x y z b : ℝ) :
    ‖(x : ℂ) - 2 * b * (y : ℂ) + b ^ 2 * (z : ℂ)‖ ^ 2 = (x - 2 * b * y + b ^ 2 * z) ^ 2 := by
  have h : (x : ℂ) - 2 * b * (y : ℂ) + b ^ 2 * (z : ℂ)
      = ((x - 2 * b * y + b ^ 2 * z : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.sq_norm, Complex.normSq_ofReal]
  ring

/-! ## The slice data of a `NiceFlat` datum, as a complex-valued function of `t` -/

/-- The `t`-derivative of the coerced slice of `u` is the coerced slice of `∂_t u`. -/
theorem nrp_deriv_slice {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t : ℝ => (u t θ : ℂ)) = fun t : ℝ => (Work.Spaces.pz u t θ : ℂ) := by
  funext t
  have hs2 := niceFlat_slice_contDiff hg hθ (n := 2) (by norm_num)
  rw [deriv_ofReal_comp (ContDiff.differentiable hs2 (by norm_num)).differentiableAt]
  rfl

/-- The `t`-slice of `∂_t u` is `C¹`. -/
theorem nrp_slice_pz_contDiff {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiff ℝ 1 (fun t : ℝ => Work.Spaces.pz u t θ) := by
  have hV : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (isOpen_univ : IsOpen (Set.univ : Set ℝ)).prod isOpen_Ioo
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz u))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllSol.FlatFT.pz_contDiffOn_succ hV hg.1
  have h := h1.comp (t := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      (f := fun t : ℝ => (t, θ)) (s := Set.univ)
    ((show ContDiff ℝ 1 (fun t : ℝ => (t, θ)) from by fun_prop).contDiffOn (s := Set.univ))
    (fun t _ => ⟨trivial, hθ⟩)
  exact contDiffOn_univ.1 (by simpa [Function.comp_def, Function.uncurry] using h)

/-- The second `t`-derivative of the coerced slice of `u` is the coerced slice of `∂_t²u`. -/
theorem nrp_deriv2_slice {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (fun t : ℝ => (u t θ : ℂ)))
      = fun t : ℝ => (Work.Spaces.pz (Work.Spaces.pz u) t θ : ℂ) := by
  have hpz := nrp_slice_pz_contDiff hg hθ
  have h2 : deriv (fun t : ℝ => (Work.Spaces.pz u t θ : ℂ))
      = fun t : ℝ => (Work.Spaces.pz (Work.Spaces.pz u) t θ : ℂ) := by
    funext t
    rw [deriv_ofReal_comp (ContDiff.differentiable hpz (by norm_num)).differentiableAt]
    rfl
  rw [nrp_deriv_slice hg hθ]
  exact h2

/-- The `t`-derivative of the coerced slice of `∂_θu` is the coerced slice of `∂_t∂_θu`. -/
theorem nrp_deriv_pth_slice {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t : ℝ => (Work.Spaces.pth u t θ : ℂ))
      = fun t : ℝ => (Work.Spaces.pz (Work.Spaces.pth u) t θ : ℂ) := by
  funext t
  have hs1 := niceFlat_slice_pth_contDiff hg hθ (n := 1) (by norm_num)
  rw [deriv_ofReal_comp (ContDiff.differentiable hs1 (by norm_num)).differentiableAt]
  rfl

/-- Clairaut on the open strip, at an interior angle. -/
theorem nrp_pz_pth_comm {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (t : ℝ) :
    Work.Spaces.pz (Work.Spaces.pth u) t θ = Work.Spaces.pth (Work.Spaces.pz u) t θ := by
  refine Work.Spaces.pz_pth_comm (hg.1.contDiffAt ?_)
  exact (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, hθ⟩


/-! ## The second-order shifted Plancherel identity, from the first-order one applied twice

The sibling module `FlatFT.shiftPlancherel1` gives the first-order identity.  Applying it to the
shifted profile `t ↦ ∂_t h t - b·h t` — which is again `C¹` with compact support when `h` is
`C²` with compact support — and using `𝓕(∂_t h - b·h)(ξ) = (2πiξ - b)·𝓕h(ξ)` pointwise yields the
second-order identity (the multiplier `(2πiξ)² - 2b(2πiξ) + b²` of `h'' - 2bh' + b²h` being the
square of `2πiξ - b`).  Keeping the derivation here makes this module depend only on the
first-order sibling.
-/

/-- The squared modulus of the shifted Fourier multiplier `2πIξ - b`:
`‖(2πIξ - b)F‖² = ((2πξ)² + b²)·‖F‖²`. -/
theorem nrp_norm_sq_mul_shift (F : ℂ) (b ξ : ℝ) :
    ‖(2 * Real.pi * Complex.I * ξ - (b : ℂ)) * F‖ ^ 2
      = ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖F‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (2 * Real.pi * Complex.I * ξ - (b : ℂ)).re = -b := by simp
  have him : (2 * Real.pi * Complex.I * ξ - (b : ℂ)).im = 2 * Real.pi * ξ := by simp
  rw [hre, him]
  ring

/-- Linearity of the `t`-Fourier slice for a difference with a constant multiple,
`slice1 (f - c·g) ξ = slice1 f ξ - c·slice1 g ξ`; all the integrals involved converge absolutely
because the exponential factor has modulus one and `f`, `g` are continuous with compact
support. -/
theorem nrp_slice1_sub_const_mul (f g : ℝ → ℂ) (c : ℂ) (hf : Continuous f)
    (hfs : HasCompactSupport f) (hg : Continuous g) (hgs : HasCompactSupport g) (ξ : ℝ) :
    slice1 (fun t => f t - c * g t) ξ = slice1 f ξ - c * slice1 g ξ := by
  set κ : ℝ → ℂ := fun t => Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)) with hκ
  have hκc : Continuous κ := by rw [hκ]; fun_prop
  have hfs' : HasCompactSupport (fun t => f t * κ t) :=
    hfs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have hgs' : HasCompactSupport (fun t => g t * κ t) :=
    hgs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have h1 : Integrable (fun t => f t * κ t) :=
    (hf.mul hκc).integrable_of_hasCompactSupport hfs'
  have h2 : Integrable (fun t => g t * κ t) :=
    (hg.mul hκc).integrable_of_hasCompactSupport hgs'
  have h3 : Integrable (fun t => c * (g t * κ t)) := h2.const_mul c
  calc slice1 (fun t => f t - c * g t) ξ
      = ∫ t, (f t - c * g t) * κ t := rfl
    _ = ∫ t, (f t * κ t - c * (g t * κ t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        ring
    _ = (∫ t, f t * κ t) - ∫ t, c * (g t * κ t) := integral_sub h1 h3
    _ = (∫ t, f t * κ t) - c * ∫ t, g t * κ t := by rw [integral_const_mul]
    _ = slice1 f ξ - c * slice1 g ξ := rfl

/-- The pointwise multiplier identity for the shifted profile `∂_t h - b·h`. -/
theorem nrp_key {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (b ξ : ℝ) :
    ‖slice1 (fun t => deriv h t - b * h t) ξ‖ ^ 2
      = ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2 := by
  rw [nrp_slice1_sub_const_mul (deriv h) h (b : ℂ) hh.continuous_deriv_one hs.deriv
    hh.continuous hs ξ, Work.FTS.EllSol.FlatFT.slice1_deriv h hh hs ξ, ← sub_mul,
    nrp_norm_sq_mul_shift]

/-- **Second-order shifted Plancherel**, obtained from `FlatFT.shiftPlancherel1` applied to `h`
and to `∂_t h - b·h`. -/
theorem nrp_shiftPlancherel2 {h : ℝ → ℂ} (hh : ContDiff ℝ 2 h) (hs : HasCompactSupport h)
    (b : ℝ) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice1 h ξ‖ ^ 2) ∧
      (∫ ξ : ℝ, (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice1 h ξ‖ ^ 2
        = ∫ t : ℝ, ‖deriv (deriv h) t - 2 * b * deriv h t + b ^ 2 * h t‖ ^ 2) := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hdc : ContDiff ℝ 1 (deriv h) := hh.deriv'
  have hcd' : ContDiff ℝ 1 (fun t : ℝ => deriv h t - b * h t) :=
    hdc.sub ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (b : ℂ))).mul hh1)
  have hb : HasCompactSupport (fun t : ℝ => (b : ℂ) * h t) :=
    hs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have hs' : HasCompactSupport (fun t : ℝ => deriv h t - b * h t) := hs.deriv.sub hb
  obtain ⟨hint', heq'⟩ := Work.FTS.EllSol.FlatFT.shiftPlancherel1
    (h := fun t : ℝ => deriv h t - b * h t) hcd' hs' b
  have hpt : ∀ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2)
      * ‖slice1 (fun t : ℝ => deriv h t - b * h t) ξ‖ ^ 2
      = (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice1 h ξ‖ ^ 2 := by
    intro ξ
    rw [nrp_key hh1 hs b ξ]
    ring
  refine ⟨hint'.congr (Filter.Eventually.of_forall hpt), ?_⟩
  have hderiv' : deriv (fun t : ℝ => deriv h t - b * h t)
      = fun t : ℝ => deriv (deriv h) t - b * deriv h t := by
    funext t
    have h1 : HasDerivAt (fun t : ℝ => deriv h t) (deriv (deriv h) t) t :=
      (hdc.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => (b : ℂ) * h t) ((b : ℂ) * deriv h t) t :=
      ((hh1.differentiable (by norm_num)).differentiableAt.hasDerivAt).const_mul (b : ℂ)
    exact (h1.sub h2).deriv
  calc (∫ ξ : ℝ, (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice1 h ξ‖ ^ 2)
      = ∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2)
          * ‖slice1 (fun t : ℝ => deriv h t - b * h t) ξ‖ ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun ξ => (hpt ξ).symm)
    _ = ∫ t : ℝ, ‖deriv (fun t : ℝ => deriv h t - b * h t) t
          - b * ((fun t : ℝ => deriv h t - b * h t) t)‖ ^ 2 := heq'
    _ = ∫ t : ℝ, ‖deriv (deriv h) t - 2 * b * deriv h t + b ^ 2 * h t‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        have h1 : deriv (fun t : ℝ => deriv h t - b * h t) t
            = deriv (deriv h) t - b * deriv h t := by
          rw [hderiv']
        rw [h1, show (deriv (deriv h) t - b * deriv h t) - b * (deriv h t - b * h t)
            = deriv (deriv h) t - 2 * b * deriv h t + b ^ 2 * h t from by ring]

/-! ## The three Plancherel identities at an interior angle -/

/-- The first-order shifted Plancherel identity at a fixed interior angle. -/
theorem nrp_conj1 {b : ℝ} {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice u ξ θ‖ ^ 2)
        = ∫ t : ℝ, (Work.Spaces.pz u t θ - b * u t θ) ^ 2 := by
  have hs2 := niceFlat_slice_contDiff hg hθ (n := 2) (by norm_num)
  have hcd : ContDiff ℝ 1 (fun t : ℝ => (u t θ : ℂ)) :=
    contDiff_ofReal_comp (hs2.of_le (by norm_num))
  have hsupp := niceFlat_hasCompactSupport hg θ
  have hderiv := nrp_deriv_slice hg hθ
  obtain ⟨hint, heq⟩ := Work.FTS.EllSol.FlatFT.shiftPlancherel1 hcd hsupp b
  refine ⟨hint, ?_⟩
  calc (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice u ξ θ‖ ^ 2)
      = ∫ t : ℝ,
          ‖deriv (fun t : ℝ => (u t θ : ℂ)) t - b * ((fun t : ℝ => (u t θ : ℂ)) t)‖ ^ 2 :=
        heq
    _ = ∫ t : ℝ, ‖(Work.Spaces.pz u t θ : ℂ) - b * (u t θ : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hderiv]
    _ = ∫ t : ℝ, (Work.Spaces.pz u t θ - b * u t θ) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        exact nrp_normSq_sub _ _ _

/-- The second-order shifted Plancherel identity at a fixed interior angle. -/
theorem nrp_conj2 {b : ℝ} {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice u ξ θ‖ ^ 2)
        = ∫ t : ℝ, (Work.Spaces.pz (Work.Spaces.pz u) t θ - 2 * b * Work.Spaces.pz u t θ
            + b ^ 2 * u t θ) ^ 2 := by
  have hs2 := niceFlat_slice_contDiff hg hθ (n := 2) (by norm_num)
  have hcd : ContDiff ℝ 2 (fun t : ℝ => (u t θ : ℂ)) := contDiff_ofReal_comp hs2
  have hsupp := niceFlat_hasCompactSupport hg θ
  have hd1 := nrp_deriv_slice hg hθ
  have hd2 := nrp_deriv2_slice hg hθ
  obtain ⟨hint, heq⟩ := nrp_shiftPlancherel2 hcd hsupp b
  refine ⟨hint, ?_⟩
  calc (∫ ξ : ℝ, (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice u ξ θ‖ ^ 2)
      = ∫ t : ℝ, ‖deriv (deriv (fun t : ℝ => (u t θ : ℂ))) t
          - 2 * b * deriv (fun t : ℝ => (u t θ : ℂ)) t
          + b ^ 2 * ((fun t : ℝ => (u t θ : ℂ)) t)‖ ^ 2 :=
        heq
    _ = ∫ t : ℝ, ‖(Work.Spaces.pz (Work.Spaces.pz u) t θ : ℂ)
          - 2 * b * (Work.Spaces.pz u t θ : ℂ) + b ^ 2 * (u t θ : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hd2, hd1]
    _ = ∫ t : ℝ, (Work.Spaces.pz (Work.Spaces.pz u) t θ - 2 * b * Work.Spaces.pz u t θ
          + b ^ 2 * u t θ) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        exact nrp_normSq_sub2 _ _ _ _

/-- The first-order shifted Plancherel identity for `∂_θu` at a fixed interior angle. -/
theorem nrp_conj3 {b : ℝ} {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice (Work.Spaces.pth u) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice (Work.Spaces.pth u) ξ θ‖ ^ 2)
        = ∫ t : ℝ, (Work.Spaces.pth (Work.Spaces.pz u) t θ
            - b * Work.Spaces.pth u t θ) ^ 2 := by
  have hs1 := niceFlat_slice_pth_contDiff hg hθ (n := 1) (by norm_num)
  have hcd : ContDiff ℝ 1 (fun t : ℝ => (Work.Spaces.pth u t θ : ℂ)) :=
    contDiff_ofReal_comp hs1
  have hsupp := niceFlat_hasCompactSupport_pth hg θ
  have hderiv := nrp_deriv_pth_slice hg hθ
  obtain ⟨hint, heq⟩ := Work.FTS.EllSol.FlatFT.shiftPlancherel1 hcd hsupp b
  refine ⟨hint, ?_⟩
  calc (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice (Work.Spaces.pth u) ξ θ‖ ^ 2)
      = ∫ t : ℝ, ‖deriv (fun t : ℝ => (Work.Spaces.pth u t θ : ℂ)) t
          - b * ((fun t : ℝ => (Work.Spaces.pth u t θ : ℂ)) t)‖ ^ 2 :=
        heq
    _ = ∫ t : ℝ, ‖(Work.Spaces.pz (Work.Spaces.pth u) t θ : ℂ)
          - b * (Work.Spaces.pth u t θ : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hderiv]
    _ = ∫ t : ℝ, ‖(Work.Spaces.pth (Work.Spaces.pz u) t θ : ℂ)
          - b * (Work.Spaces.pth u t θ : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [nrp_pz_pth_comm hg hθ t]
    _ = ∫ t : ℝ, (Work.Spaces.pth (Work.Spaces.pz u) t θ
          - b * Work.Spaces.pth u t θ) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        exact nrp_normSq_sub _ _ _

theorem niceRangePlanch {b : ℝ} {u : ℝ → ℝ → ℝ} (hg : Work.FTS.EllSol.FlatFT.NiceFlat u) :
    (∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) ∧
        (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pz u t θ - b * u t θ) ^ 2)
    ∧ (∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable (fun ξ : ℝ => (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) ∧
        (∫ ξ : ℝ, (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pz (Work.Spaces.pz u) t θ - 2 * b * Work.Spaces.pz u t θ + b ^ 2 * u t θ) ^ 2)
    ∧ (∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖Work.FTS.EllSol.FlatFT.slice (Work.Spaces.pth u) ξ θ‖ ^ 2) ∧
        (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖Work.FTS.EllSol.FlatFT.slice (Work.Spaces.pth u) ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pth (Work.Spaces.pz u) t θ - b * Work.Spaces.pth u t θ) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [nrp_ae_mem_Ioo] with θ hθ
    exact nrp_conj1 hg hθ
  · filter_upwards [nrp_ae_mem_Ioo] with θ hθ
    exact nrp_conj2 hg hθ
  · filter_upwards [nrp_ae_mem_Ioo] with θ hθ
    exact nrp_conj3 hg hθ

end Work.FTS.EllSol.Shift2Flat
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false


/-- A definite integral over an interval is the set integral over the closed interval. -/
theorem intervalIntegral_eq_setIntegral_Icc (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ s in a..b, f s) = ∫ s in Set.Icc a b, f s := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The restricted product measure on the half-strip `ℝ × Iθ` is the product of the line
measure with the (restricted) angular measure. -/
theorem uTrAtwo_prodRestrict_Iθ :
    ((volume : Measure (ℝ × ℝ))).restrict (Set.univ ×ˢ Work.Spaces.Iθ)
      = (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
    MeasureTheory.Measure.restrict_univ]

/-- The coefficient `phiTr' · chi + 2 · phiTr · chi'` of `L_b u` in `W` is bounded by
`Kd/N + 2·Kd/(4096·N)`. -/
theorem abs_coeff_L1_le (N : ℝ) {Kd : ℝ} (hKd : ∀ t : ℝ, |deriv Trunc.tk t| ≤ Kd)
    (hN : 0 < N) (t : ℝ) :
    |phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t|
      ≤ Kd / N + 2 * (Kd / (4096 * N)) := by
  have h1 : |deriv (Trunc.chi N) t| ≤ Kd / N := Trunc.abs_deriv_chi_le hKd hN t
  have h2 : |deriv (phiTr N) t| ≤ Kd / (4096 * N) := abs_deriv_phiTr_le N hKd hN
  have h3 : |Trunc.chi N t| ≤ 1 := by
    rw [abs_of_nonneg (Trunc.chi_nonneg N t)]; exact Trunc.chi_le_one N t
  have h4 : |phiTr N t| ≤ 1 := by
    rw [abs_of_nonneg (phiTr_nonneg N t)]; exact phiTr_le_one N t
  have hKd0 : 0 ≤ Kd := le_trans (abs_nonneg _) (hKd 0)
  have hN4 : 0 < 4096 * N := by linarith
  have hb0 : 0 ≤ Kd / (4096 * N) := div_nonneg hKd0 (le_of_lt hN4)
  have hm1 : |phiTr N t * deriv (Trunc.chi N) t| ≤ 1 * (Kd / N) := by
    rw [abs_mul]
    exact mul_le_mul h4 h1 (abs_nonneg _) (by norm_num)
  have hm2 : |2 * deriv (phiTr N) t * Trunc.chi N t| ≤ 2 * (Kd / (4096 * N)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h5 : |deriv (phiTr N) t| * |Trunc.chi N t| ≤ (Kd / (4096 * N)) * 1 :=
      mul_le_mul h2 h3 (abs_nonneg _) hb0
    linarith
  calc |phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t|
      ≤ |phiTr N t * deriv (Trunc.chi N) t| + |2 * deriv (phiTr N) t * Trunc.chi N t| :=
        abs_add_le _ _
    _ ≤ 1 * (Kd / N) + 2 * (Kd / (4096 * N)) := add_le_add hm1 hm2
    _ = Kd / N + 2 * (Kd / (4096 * N)) := by ring


/-- The dominating function of the estimate: the three pointwise bounds for the three pieces
of `W`, each carrying the weight `wE`. -/
def uTrAtwo_D (N b : ℝ) (u : ℝ → ℝ → ℝ) (Kd : ℝ) (p : ℝ × ℝ) : ℝ :=
  3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
    + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
        * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
    + 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
        * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
            * Work.FTS.EllSol.FlatFT.wE p.2))

/-- The tail bound for the third piece of `W`: `(phiTr'' · Gc)²` is dominated by
`(phiTr'')²` times the window `L²`-norm of `L_b u`.  This is where the truncation is used:
`phiTr''` vanishes on `|t| < 4096N` and `Gc` vanishes (a.e.) beyond the window `|t| ≥ 2N`. -/
theorem uTrAtwo_phiTr_Gc_sq_le (N b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (deriv (deriv (phiTr N)) t * Gc N b u t θ) ^ 2
        ≤ (deriv (deriv (phiTr N)) t) ^ 2 *
          (4 * N * ∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2) := by
  intro t θ hθ
  have hnn : 0 ≤ 4 * N * ∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2 :=
    mul_nonneg (by linarith) (MeasureTheory.integral_nonneg (fun s => sq_nonneg _))
  rcases lt_or_ge |t| (4096 * N) with hlt | hge
  · rw [deriv2_phiTr_eq_zero_of_abs_lt hN hlt]
    nlinarith [sq_nonneg (deriv (deriv (phiTr N)) t), hnn]
  · have h2N : 2 * N ≤ |t| := by linarith
    rcases le_or_gt 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0] at hge
      have hz : Gc N b u t θ = 0 := (Aux2.gcTail N b u hb hN hu).2.2 t θ hθ (by linarith)
      rw [hz]
      nlinarith [sq_nonneg (deriv (deriv (phiTr N)) t), hnn]
    · have htle : t ≤ -(2 * N) := by
        rw [abs_of_neg ht0] at hge
        linarith
      have hb2 := (Aux2.gcTail N b u hb hN hu).2.1 t θ hθ htle
      rw [intervalIntegral_eq_setIntegral_Icc (-(2 * N)) (2 * N) (by linarith)] at hb2
      simp only [uTrAtwo_L1] at hb2 ⊢
      calc (deriv (deriv (phiTr N)) t * Gc N b u t θ) ^ 2
          = (deriv (deriv (phiTr N)) t) ^ 2 * (Gc N b u t θ) ^ 2 := by ring
        _ ≤ (deriv (deriv (phiTr N)) t) ^ 2 *
              (4 * N * ∫ s in Set.Icc (-(2 * N)) (2 * N),
                (Work.Spaces.pz u s θ - b * u s θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)

/-- The pointwise bound `W² · wE ≤ D` on the open strip. -/
theorem uTrAtwo_W_sq_le_D (N b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {Kd : ℝ} (hKd : ∀ t : ℝ, |deriv Trunc.tk t| ≤ Kd) (hKd0 : 0 ≤ Kd) :
    ∀ p : ℝ × ℝ, p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (uTrAtwo_W N b u p) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2 ≤ uTrAtwo_D N b u Kd p := by
  intro p hp
  obtain ⟨t, θ⟩ := p
  have hθI : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hp
  have hwE : 0 ≤ Work.FTS.EllSol.FlatFT.wE θ := Work.FTS.EllSol.FlatFT.wE_nonneg hθI
  set P : ℝ := uTrAtwo_L2 b u t θ with hP
  set Q : ℝ := uTrAtwo_L1 b u t θ with hQ
  set Rr : ℝ := deriv (deriv (phiTr N)) t with hR
  set Wv : ℝ := ∫ s in Set.Icc (-(2 * N)) (2 * N), uTrAtwo_L1 b u s θ ^ 2 with hW
  set cc : ℝ := Kd / N + 2 * (Kd / (4096 * N)) with hcc
  have hA : (phiTr N t * Work.FTS.EllSol.Trunc.chi N t * P) ^ 2 ≤ P ^ 2 := by
    have h1 : |phiTr N t * Work.FTS.EllSol.Trunc.chi N t| ≤ 1 := by
      rw [abs_mul]
      refine mul_le_one₀ ?_ (abs_nonneg _) ?_
      · rw [abs_of_nonneg (phiTr_nonneg N t)]; exact phiTr_le_one N t
      · rw [abs_of_nonneg (Trunc.chi_nonneg N t)]; exact Trunc.chi_le_one N t
    have h2 : (phiTr N t * Work.FTS.EllSol.Trunc.chi N t) ^ 2 ≤ 1 := by
      nlinarith [h1, abs_nonneg (phiTr N t * Work.FTS.EllSol.Trunc.chi N t),
        sq_abs (phiTr N t * Work.FTS.EllSol.Trunc.chi N t)]
    nlinarith [h2, sq_nonneg P]
  have hB : ((phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t)
        * Q) ^ 2 ≤ cc ^ 2 * Q ^ 2 := by
    have h1 := abs_coeff_L1_le N hKd hN t
    have h2 : (phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t) ^ 2
        ≤ cc ^ 2 := by
      rw [hcc]
      nlinarith [h1, abs_nonneg (phiTr N t * deriv (Trunc.chi N) t
        + 2 * deriv (phiTr N) t * Trunc.chi N t),
        sq_abs (phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t)]
    nlinarith [h2, sq_nonneg Q]
  have hC : (Rr * Gc N b u t θ) ^ 2 ≤ Rr ^ 2 * (4 * N * Wv) := by
    rw [hR, hW]
    exact uTrAtwo_phiTr_Gc_sq_le N b u hb hN hu t θ hp
  have hkey : (phiTr N t * Work.FTS.EllSol.Trunc.chi N t * P
        + (phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t) * Q
        + Rr * Gc N b u t θ) ^ 2 ≤ 3 * (P ^ 2 + cc ^ 2 * Q ^ 2 + Rr ^ 2 * (4 * N * Wv)) := by
    have h3 := Work.FTS.EllSol.Trunc.three_sq_le
      (phiTr N t * Work.FTS.EllSol.Trunc.chi N t * P)
      ((phiTr N t * deriv (Trunc.chi N) t + 2 * deriv (phiTr N) t * Trunc.chi N t) * Q)
      (Rr * Gc N b u t θ)
    nlinarith [h3, hA, hB, hC]
  rw [uTrAtwo_W, uTrAtwo_D]
  nlinarith [hkey, hwE]

end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.Trunc.CxAgmonAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

theorem deriv_re_eq {F : ℝ → ℂ} {θ : ℝ} (h : DifferentiableAt ℝ F θ) :
    deriv (fun θ' => (F θ').re) θ = (deriv F θ).re := by
  have h2 : HasFDerivAt (fun θ' => (F θ').re)
      ((Complex.reCLM : ℂ →L[ℝ] ℝ).comp (fderiv ℝ F θ)) θ :=
    (Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp θ h.hasFDerivAt
  rw [h2.hasDerivAt.deriv, ContinuousLinearMap.comp_apply]
  rw [← h.hasFDerivAt.hasDerivAt.deriv, Complex.reCLM_apply]

theorem deriv_im_eq {F : ℝ → ℂ} {θ : ℝ} (h : DifferentiableAt ℝ F θ) :
    deriv (fun θ' => (F θ').im) θ = (deriv F θ).im := by
  have h2 : HasFDerivAt (fun θ' => (F θ').im)
      ((Complex.imCLM : ℂ →L[ℝ] ℝ).comp (fderiv ℝ F θ)) θ :=
    (Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp θ h.hasFDerivAt
  rw [h2.hasDerivAt.deriv, ContinuousLinearMap.comp_apply]
  rw [← h.hasFDerivAt.hasDerivAt.deriv, Complex.imCLM_apply]

theorem contDiffOn_re {n : ℕ} {F : ℝ → ℂ} {s : Set ℝ} (h : ContDiffOn ℝ n F s) :
    ContDiffOn ℝ n (fun θ => (F θ).re) s := by
  have hcomp := (Complex.reCLM : ℂ →L[ℝ] ℝ).contDiff.comp_contDiffOn h
  simpa [Function.comp_def, Complex.reCLM_apply] using hcomp

theorem contDiffOn_im {n : ℕ} {F : ℝ → ℂ} {s : Set ℝ} (h : ContDiffOn ℝ n F s) :
    ContDiffOn ℝ n (fun θ => (F θ).im) s := by
  have hcomp := (Complex.imCLM : ℂ →L[ℝ] ℝ).contDiff.comp_contDiffOn h
  simpa [Function.comp_def, Complex.imCLM_apply] using hcomp

/-- On the open interval, differentiating the real projection twice commutes with projecting the
second derivative. -/
theorem deriv_deriv_re_eq {F : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s) {θ : ℝ} (hθ : θ ∈ s)
    (hF : ContDiffOn ℝ 2 F s) :
    deriv (deriv (fun θ' => (F θ').re)) θ = (deriv (deriv F) θ).re := by
  have hJ : s ∈ 𝓝 θ := hs.mem_nhds hθ
  have h1 : DifferentiableAt ℝ F θ :=
    (hF.differentiableOn (by norm_num)).differentiableAt hJ
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ F) s := hF.fderiv_of_isOpen hs (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ F) θ :=
    (hfd.differentiableOn (by norm_num)).differentiableAt hJ
  have h3 : DifferentiableAt ℝ (deriv F) θ := by
    have he : deriv F =ᶠ[𝓝 θ] (fun θ' => (fderiv ℝ F θ') 1) := by
      filter_upwards [hJ] with θ' hθ'
      exact ((hF.differentiableOn (by norm_num)).differentiableAt
        (hs.mem_nhds hθ')).hasFDerivAt.hasDerivAt.deriv
    exact (Filter.EventuallyEq.differentiableAt_iff he).mpr
      (h2.clm_apply (differentiableAt_const (1 : ℝ)))
  have h4 : deriv (deriv (fun θ' => (F θ').re)) θ
      = deriv (fun θ' => (deriv F θ').re) θ := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hJ] with θ' hθ'
    exact deriv_re_eq ((hF.differentiableOn (by norm_num)).differentiableAt
      (hs.mem_nhds hθ'))
  rw [h4]
  exact deriv_re_eq h3

/-- Same as `deriv_deriv_re_eq` for the imaginary part. -/
theorem deriv_deriv_im_eq {F : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s) {θ : ℝ} (hθ : θ ∈ s)
    (hF : ContDiffOn ℝ 2 F s) :
    deriv (deriv (fun θ' => (F θ').im)) θ = (deriv (deriv F) θ).im := by
  have hJ : s ∈ 𝓝 θ := hs.mem_nhds hθ
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ F) s := hF.fderiv_of_isOpen hs (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ F) θ :=
    (hfd.differentiableOn (by norm_num)).differentiableAt hJ
  have h3 : DifferentiableAt ℝ (deriv F) θ := by
    have he : deriv F =ᶠ[𝓝 θ] (fun θ' => (fderiv ℝ F θ') 1) := by
      filter_upwards [hJ] with θ' hθ'
      exact ((hF.differentiableOn (by norm_num)).differentiableAt
        (hs.mem_nhds hθ')).hasFDerivAt.hasDerivAt.deriv
    exact (Filter.EventuallyEq.differentiableAt_iff he).mpr
      (h2.clm_apply (differentiableAt_const (1 : ℝ)))
  have h4 : deriv (deriv (fun θ' => (F θ').im)) θ
      = deriv (fun θ' => (deriv F θ').im) θ := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hJ] with θ' hθ'
    exact deriv_im_eq ((hF.differentiableOn (by norm_num)).differentiableAt
      (hs.mem_nhds hθ'))
  rw [h4]
  exact deriv_im_eq h3

/-- `√(a b) + √(c d) ≤ √((a+c)(b+d))` for `a,b,c,d ≥ 0`. -/
theorem sqrt_add_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * b) + Real.sqrt (c * d) ≤ Real.sqrt ((a + c) * (b + d)) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hcd : 0 ≤ c * d := mul_nonneg hc hd
  have habcd : 0 ≤ a * b * (c * d) := mul_nonneg hab hcd
  have hfirst : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2
      = a * b + c * d + 2 * Real.sqrt (a * b * (c * d)) := by
    rw [add_sq, Real.sq_sqrt hab, Real.sq_sqrt hcd, Real.sqrt_mul hab (c * d)]
    ring
  have hamgm : 2 * Real.sqrt (a * b * (c * d)) ≤ a * d + c * b := by
    have h1 : (0:ℝ) ≤ a * d := mul_nonneg ha hd
    have h2 : (0:ℝ) ≤ c * b := mul_nonneg hc hb
    have h3 : a * b * (c * d) = (a * d) * (c * b) := by ring
    rw [h3, Real.sqrt_mul h1 (c * b)]
    nlinarith [sq_nonneg (Real.sqrt (a * d) - Real.sqrt (c * b)),
      Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sqrt_nonneg (a * d), Real.sqrt_nonneg (c * b)]
  have hsq : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 ≤ (a + c) * (b + d) := by
    rw [hfirst]; nlinarith [hamgm]
  calc Real.sqrt (a * b) + Real.sqrt (c * d)
      = Real.sqrt ((Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt ((a + c) * (b + d)) := Real.sqrt_le_sqrt hsq

end

end Work.FTS.EllSol.Trunc
end
-- ===== merged: Submission.Work.FTS.EllSol.VthAuxC.helpersC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

set_option autoImplicit false

/-- `Ξ = EllResid α g Ψ = ellShift α g Ψ - Ḡ(α,g)·sin 2θ` as *functions* (the exact algebraic
identity behind the cancellation of the `1/α`-terms). -/
theorem vthC_EllResid_eq_ellShift (α : ℝ) (g Ψ : ℝ → ℝ → ℝ) :
    Work.Elliptic.EllResid α g Ψ
      = fun z θ => ellShift α g Ψ z θ + (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ) := by
  funext z θ
  rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point α g Ψ z θ, ellShift_apply]
  ring

theorem vthC_smoothOpen_add {f h : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + h z θ) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => h p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hh
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ + h z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ => f z θ + h z θ)
      = fun p : ℝ × ℝ => f p.1 p.2 + h p.1 p.2 := rfl
  rw [hfun]
  exact h1.add h2

theorem vthC_smoothOpen_sub {f h : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - h z θ) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => h p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hh
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ - h z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ => f z θ - h z θ)
      = fun p : ℝ × ℝ => f p.1 p.2 - h p.1 p.2 := rfl
  rw [hfun]
  exact h1.sub h2


theorem vthC_smoothOpen_tan_mul {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * f z θ) := by
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2)
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.2)
        Work.FTS.EllipticEst.Q0 := contDiffOn_snd
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin p.2)
        Work.FTS.EllipticEst.Q0 := h1.sin
    have hcos : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.cos p.2)
        Work.FTS.EllipticEst.Q0 := h1.cos
    refine (ContDiffOn.div hsin hcos ?_).congr (fun p hp => ?_)
    · intro p hp
      have hp2 : p.2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [hp.2.1, Real.pi_pos], by linarith [hp.2.2]⟩
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo hp2)
    · exact Real.tan_eq_sin_div_cos p.2
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => Real.tan θ * f z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ => Real.tan θ * f z θ)
      = fun p : ℝ × ℝ => Real.tan p.2 * f p.1 p.2 := rfl
  rw [hfun]
  exact htan.mul h2

/-- `L₀` is additive on the open quadrant. -/
theorem vthC_Lzero_add {f h : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hh : Work.FTS.EllipticEst.SmoothOpen h)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Elliptic.Lzero (fun z' θ' => f z' θ' + h z' θ') z θ
      = Work.Elliptic.Lzero f z θ + Work.Elliptic.Lzero h z θ := by
  have hcos : Real.cos θ ≠ 0 := by
    have h1 : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h1)
  have hf2 : ContDiffAt ℝ 2 (fun t => f z t) θ :=
    ((hf.curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds hθ)).of_le (by norm_num)
  have hh2 : ContDiffAt ℝ 2 (fun t => h z t) θ :=
    ((hh.curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds hθ)).of_le (by norm_num)
  have hev1 : (fun θ' => deriv (fun t => f z t + h z t) θ')
      =ᶠ[𝓝 θ] (fun θ' => deriv (fun t => f z t) θ' + deriv (fun t => h z t) θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    have hf2' : ContDiffAt ℝ 2 (fun t => f z t) θ' :=
      ((hf.curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds hθ')).of_le (by norm_num)
    have hh2' : ContDiffAt ℝ 2 (fun t => h z t) θ' :=
      ((hh.curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds hθ')).of_le (by norm_num)
    rw [show (fun t => f z t + h z t) = (fun t => f z t) + (fun t => h z t) from rfl,
      deriv_add (hf2'.differentiableAt (by norm_num)) (hh2'.differentiableAt (by norm_num))]
  have hd1f : ContDiffAt ℝ 1 (deriv (fun t => f z t)) θ := hf2.derivWithin (by norm_num)
  have hd1h : ContDiffAt ℝ 1 (deriv (fun t => h z t)) θ := hh2.derivWithin (by norm_num)
  have hsum2 : HasDerivAt (fun θ' => deriv (fun t => f z t) θ' + deriv (fun t => h z t) θ')
      (deriv (deriv (fun t => f z t)) θ + deriv (deriv (fun t => h z t)) θ) θ :=
    ((hd1f.differentiableAt (by norm_num)).hasDerivAt).add
      ((hd1h.differentiableAt (by norm_num)).hasDerivAt)
  have hsecond : deriv (fun θ' => deriv (fun t => f z t + h z t) θ') θ
      = deriv (deriv (fun t => f z t)) θ + deriv (deriv (fun t => h z t)) θ :=
    (hsum2.congr_of_eventuallyEq hev1).deriv
  have hevtan : (fun θ' => Real.tan θ' * (f z θ' + h z θ'))
      =ᶠ[𝓝 θ] (fun θ' => Real.tan θ' * f z θ' + Real.tan θ' * h z θ') := by
    filter_upwards with θ'
    ring
  have hdtf : DifferentiableAt ℝ (fun θ' => Real.tan θ' * f z θ') θ :=
    (Real.differentiableAt_tan.mpr hcos).mul (hf2.differentiableAt (by norm_num))
  have hdth : DifferentiableAt ℝ (fun θ' => Real.tan θ' * h z θ') θ :=
    (Real.differentiableAt_tan.mpr hcos).mul (hh2.differentiableAt (by norm_num))
  have htan : deriv (fun θ' => Real.tan θ' * (f z θ' + h z θ')) θ
      = deriv (fun θ' => Real.tan θ' * f z θ') θ
        + deriv (fun θ' => Real.tan θ' * h z θ') θ := by
    rw [hevtan.deriv_eq]
    rw [show (fun θ' => Real.tan θ' * f z θ' + Real.tan θ' * h z θ')
        = (fun θ' => Real.tan θ' * f z θ') + (fun θ' => Real.tan θ' * h z θ') from rfl,
      deriv_add hdtf hdth]
  simp only [Work.Elliptic.Lzero, Work.Spaces.pth, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero]
  rw [hsecond, htan]
  ring

/-- `∂_θ(Vop U) = -(L₀U + 6U)` for `U` merely `C^∞` on the open quadrant. -/
theorem vthC_pth_Vop_eq {U : ℝ → ℝ → ℝ} (hU : Work.FTS.EllipticEst.SmoothOpen U)
    {α z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pth (Work.FTS.EllipticEst.Vop α U) z θ
      = -(Work.Elliptic.Lzero U z θ + 6 * U z θ) := by
  have hcos : Real.cos θ ≠ 0 := by
    have h1 : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h1)
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => U z θ')
      (Set.Ioo 0 (Real.pi / 2)) := hU.curry_θ hz
  have hU2 : ContDiffAt ℝ 2 (fun θ' => U z θ') θ :=
    (hslice.contDiffAt (isOpen_Ioo.mem_nhds hθ)).of_le (by norm_num)
  have hfd : HasDerivAt (fun θ' => U z θ') (deriv (fun θ' => U z θ') θ) θ :=
    (hU2.differentiableAt (by norm_num)).hasDerivAt
  have hd1 : ContDiffAt ℝ 1 (deriv (fun θ' => U z θ')) θ := hU2.derivWithin (by norm_num)
  have hfd2 : HasDerivAt (deriv (fun θ' => U z θ')) (deriv (deriv (fun θ' => U z θ')) θ) θ :=
    (hd1.differentiableAt (by norm_num)).hasDerivAt
  have htan0 : HasDerivAt (fun θ' => Real.tan θ' * U z θ')
      ((1 / Real.cos θ ^ 2) * U z θ + Real.tan θ * deriv (fun θ' => U z θ') θ) θ :=
    (Real.hasDerivAt_tan hcos).mul hfd
  have htan : HasDerivAt (fun θ' => Real.tan θ' * U z θ')
      (deriv (fun θ' => Real.tan θ' * U z θ') θ) θ :=
    htan0.congr_deriv htan0.deriv.symm
  have hsub : HasDerivAt (fun θ' => deriv (fun t => U z t) θ' - Real.tan θ' * U z θ')
      (deriv (deriv (fun t => U z t)) θ - deriv (fun θ' => Real.tan θ' * U z θ') θ) θ :=
    hfd2.sub htan
  have hfun : (fun θ' => Work.FTS.EllipticEst.Vop α U z θ')
      = fun θ' => deriv (fun t => U z t) θ' - Real.tan θ' * U z θ' := by
    funext θ'; simp only [Work.FTS.EllipticEst.Vop, Work.Spaces.pth]
  show deriv (fun θ' => Work.FTS.EllipticEst.Vop α U z θ') θ = _
  rw [hfun, hsub.deriv]
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]
  ring

/-- `1/√(γ-1) = √10 · α^{-1/2}` for `α > 0`. -/
theorem vthC_inv_sqrt_gam_sub_one {α : ℝ} (hα : 0 < α) :
    1 / Real.sqrt (Work.Spaces.gam α - 1) = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
  rw [Work.Spaces.gam_sub_one, Real.sqrt_div hα.le 10, one_div, inv_div]
  have hinv : α ^ (-(1 / 2 : ℝ)) = (Real.sqrt α)⁻¹ := by
    rw [Real.rpow_neg hα.le, ← Real.sqrt_eq_rpow]
  rw [hinv, inv_eq_one_div, div_eq_mul_inv, one_div]

end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeI4_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

/-!
# `aeI4_open`: the `I₄` upper bound of Step 2 of `prop:H2` in the a.e. class

Target: for `AeData α u G`, `HkMem α 0 u` and `HkMem α 0 (z ∂_z u)`,

  `IP (∂_θ(tan θ·u)) (∂_θθu) ≤ IP u (∂_θθu) + C · IP u u`.

Route: instantiate the *proved* `Work.FTS.EllipticEst.H2W.I4Open` (`H2W/I4Open.lean`), which
performs the whole assembly (the slicewise inequality `H2W.sliceI4Open` at each `z > 0`, then the
`z`-integration, with the three pairings honest), giving

  `IP (∂_θ(tan θ·u)) (∂_θθu) - IP u (∂_θθu) ≤ (1 - η) · IP u u`,   `η = 99/100`.

It remains to supply, for every `z > 0`:

* the three honesty statements `IPMem (∂_θ(tan θ·u)) (∂_θθu)`, `IPMem u (∂_θθu)`, `IPMem u u`
  (from the proved `remov.aeIPMemsSlim : AngAWeak.AeIPMems` and the diagonal
  `AngClean.HkMem_zero_IPMem`);
* the four slicewise integrability facts
  `∫ (u z ·/cos θ)²σ`, `∫ (∂_θ(u z ·/cos ·))²σ`, `∫ (∂_θθu(z,·))²σ`,
  `∫ sin²θ·(∂_θ(u z ·/cos ·))²σ` over `θ ∈ Iθ`.

The first is `psiDivCosSq_integrable` of `TT/weakI4Psi.lean` transplanted to the a.e. class (its
only class-dependent ingredient is the right-endpoint rate, which in the a.e. class is the proved
`H2W.AeProof.AeSliceRightTendsto`); the second is `TT.psiDerivSq_lower`/`TT.psiDerivSq_upper`
transplanted (the upper half needs `HkMem α 0 (∂_θ(tan θ·u))`, which in the a.e. class is the
proved `H2W.Ae.hkMem_ang1`); the third is immediate slicewise `HkMem`; the fourth follows from the
second by the pointwise domination `sin²θ ≤ 1`.
-/

/-! ## `IntegrableOn` book-keeping for the gluing of the two halves of `Iθ` -/

/-- `IntegrableOn` only sees the set up to a null set. -/
private theorem integrableOn_congr_set {f : ℝ → ℝ} {s t : Set ℝ}
    (h : IntegrableOn f s volume) (hst : s =ᵐ[volume] t) : IntegrableOn f t volume := by
  have hμ : volume.restrict s = volume.restrict t := Measure.restrict_congr_set hst
  rw [MeasureTheory.IntegrableOn] at h ⊢
  rwa [hμ] at h

/-- The two halves of `Ioo 0 (π/2)` (up to the null point `π/4`). -/
private theorem Ioo_ae_eq_halves :
    Set.Ioo (0 : ℝ) (Real.pi / 2)
      =ᵐ[volume] (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2) : Set ℝ) := by
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 4 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne] with x hx
  apply propext
  simp only [Set.mem_Ioo, Set.mem_union]
  constructor
  · intro h
    rcases lt_or_gt_of_ne hx with h4 | h4
    · exact Or.inl ⟨h.1, h4⟩
    · exact Or.inr ⟨h4, h.2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, by linarith [h2, Real.pi_pos]⟩
    · exact ⟨by linarith [h1, Real.pi_pos], h2⟩

/-- Integrability on the two halves gives integrability on `Iθ`. -/
private theorem integrableOn_Iθ_of_halves {f : ℝ → ℝ}
    (h1 : IntegrableOn f (Set.Ioo 0 (Real.pi / 4)) volume)
    (h2 : IntegrableOn f (Set.Ioo (Real.pi / 4) (Real.pi / 2)) volume) :
    IntegrableOn f Work.Spaces.Iθ volume := by
  have hunion : IntegrableOn f (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2))
      volume := h1.union h2
  have hIoo : IntegrableOn f (Set.Ioo 0 (Real.pi / 2)) volume :=
    integrableOn_congr_set hunion Ioo_ae_eq_halves.symm
  have hIcc : IntegrableOn f (Set.Icc 0 (Real.pi / 2)) volume :=
    integrableOn_congr_set hIoo (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := Real.pi / 2))
  simpa only [Work.Spaces.Iθ] using hIcc

/-! ## The angular weight -/

private theorem sig_continuousOn_Ioo :
    ContinuousOn Work.FTS.EllipticEst.AngSecond.sig (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hc : Continuous (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hsinpos : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * x) := by
    intro x hx
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
  change ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (Set.Ioo (0 : ℝ) (Real.pi / 2))
  exact hc.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (hsinpos x hx)))

private theorem sig_integrableOn_Iθ : IntegrableOn Work.FTS.EllipticEst.AngSecond.sig
    Work.Spaces.Iθ volume :=
  Work.FTS.EllipticEst.AngClean.integrableOn_sig

/-! ## The slice data available from the a.e. class -/

/-- The `θ`-slice of a datum of `AeData` is `C²` on the open interval. -/
private theorem slice_contDiffOn_ae {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.EllipticEst.TT.contDiffOn_slice_of_strip hA.smooth hz 2

/-- The slice data available from the a.e. class, uniform in `z > 0`. -/
private theorem slice_core_ae {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) ∧
    IntegrableOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ ∧
    IntegrableOn (fun θ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ ∧
    IntegrableOn (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
  have hsm := slice_contDiffOn_ae hA hz
  have h0 := Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (g := u) hz hu
  have h2 : IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
    refine (Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (g := Work.Spaces.pthIter 2 u)
      hz hA.memAng2).congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  have h1 : IntegrableOn (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.Honest.sliceInterp (fun θ => u z θ) hsm h0 h2).1
  exact ⟨hsm, h0, h2, h1⟩

/-! ## The first slicewise integrability fact: `∫ (u z · / cos)² σ` -/

private theorem ae_psiDivCosSq_integrable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (u z θ / Real.cos θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
  -- the right-endpoint rate of the slice
  obtain ⟨-, K, hK0, hKev⟩ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G hA z hz
  obtain ⟨θ₀, hθ₀lt, hθ₀sub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hKev
  set θ₁ : ℝ := max θ₀ (Real.pi / 4) with hθ₁def
  have hθ₁lt : θ₁ < Real.pi / 2 := max_lt hθ₀lt (by linarith [Real.pi_pos])
  -- a bound on the compact piece `[π/4, θ₁]`
  obtain ⟨hsm, hf0, -, -⟩ := slice_core_ae hA hu hz
  have hsubIoo : Set.Icc (Real.pi / 4) θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun θ hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], lt_of_le_of_lt hθ.2 hθ₁lt⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc).exists_bound_of_continuousOn (hsm.continuousOn.mono hsubIoo)
  set M₂ : ℝ := max M 0 with hM₂def
  have hθ₁ge : Real.pi / 4 ≤ θ₁ := le_max_right _ _
  have hM₂ : ∀ θ ∈ Set.Icc (Real.pi / 4) θ₁, |u z θ| ≤ M₂ := by
    intro θ hθ
    have h1 : |u z θ| ≤ M := by simpa only [Real.norm_eq_abs] using hM θ hθ
    exact h1.trans (le_max_left _ _)
  have hcosθ₁pos : 0 < Real.cos θ₁ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ₁ge, Real.pi_pos], hθ₁lt⟩
  set C₀ : ℝ := (M₂ / Real.cos θ₁) ^ 2 + (K * Real.pi / 2) ^ 2 + 1 with hC₀def
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀def]
    have h1 := sq_nonneg (M₂ / Real.cos θ₁)
    have h2 := sq_nonneg (K * Real.pi / 2)
    linarith
  have hC₀ge₁ : (M₂ / Real.cos θ₁) ^ 2 ≤ C₀ := by
    rw [hC₀def]
    have h2 := sq_nonneg (K * Real.pi / 2)
    linarith
  have hC₀ge₂ : (K * Real.pi / 2) ^ 2 ≤ C₀ := by
    rw [hC₀def]
    have h1 := sq_nonneg (M₂ / Real.cos θ₁)
    linarith
  -- the pointwise domination on `(0, π/2)`
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
          + C₀ * Work.FTS.EllipticEst.AngSecond.sig θ := by
    intro θ hθ
    have hσnn : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hcospos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hkey : (u z θ / Real.cos θ) ^ 2 ≤ 2 * (u z θ) ^ 2 + C₀ := by
      rcases lt_or_ge θ (Real.pi / 4) with h4 | h4
      · -- the lower quarter: `1/cos θ² ≤ 2`
        have hcle : Real.cos (Real.pi / 4) ≤ Real.cos θ :=
          Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hθ.1)
            (by linarith [Real.pi_pos]) h4.le
        have hc4 : 0 < Real.cos (Real.pi / 4) :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hsq : (1 / 2 : ℝ) ≤ (Real.cos θ) ^ 2 := by
          have h2 : (Real.cos (Real.pi / 4)) ^ 2 = 1 / 2 := by
            rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
            norm_num
          nlinarith [hcle, h2, hc4.le]
        have hinv : ((Real.cos θ) ^ 2)⁻¹ ≤ 2 := by
          rw [inv_le_iff_one_le_mul₀ (by positivity : (0 : ℝ) < (Real.cos θ) ^ 2)]
          linarith
        rw [div_eq_mul_inv, mul_pow, inv_pow]
        nlinarith [sq_nonneg (u z θ), hinv, hC₀nn]
      · rcases le_or_gt θ θ₁ with h5 | h5
        · -- the compact piece
          have hθIcc : θ ∈ Set.Icc (Real.pi / 4) θ₁ := ⟨h4, h5⟩
          have hcle : Real.cos θ₁ ≤ Real.cos θ :=
            Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
              (by linarith [hθ.2, Real.pi_pos]) h5
          have hM₂nn : 0 ≤ M₂ := le_max_right _ _
          have h1 : |u z θ / Real.cos θ| ≤ M₂ / Real.cos θ₁ := by
            rw [abs_div, abs_of_pos hcospos, div_le_iff₀ hcospos,
              div_mul_eq_mul_div, le_div_iff₀ hcosθ₁pos]
            exact mul_le_mul (hM₂ θ hθIcc) hcle hcosθ₁pos.le hM₂nn
          have h2 : (u z θ / Real.cos θ) ^ 2 ≤ (M₂ / Real.cos θ₁) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          nlinarith [h2, hC₀ge₁, sq_nonneg (u z θ)]
        · -- the rate region
          have h6 : θ ∈ Set.Ioo θ₁ (Real.pi / 2) := ⟨h5, hθ.2⟩
          have hrate : |u z θ| ≤ K * (Real.pi / 2 - θ) :=
            hθ₀sub ⟨lt_of_le_of_lt (le_max_left _ _) h6.1, h6.2⟩
          have hd : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
          have hj : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
            have h' := Real.mul_le_sin hd.le (by linarith [hθ.1, Real.pi_pos])
            rwa [Real.sin_pi_div_two_sub] at h'
          have h1 : |u z θ / Real.cos θ| ≤ K * Real.pi / 2 := by
            rw [abs_div, abs_of_pos hcospos, div_le_iff₀ hcospos]
            calc |u z θ| ≤ K * (Real.pi / 2 - θ) := hrate
              _ ≤ K * Real.pi / 2 * Real.cos θ := by
                  have hstep : K * (Real.pi / 2 - θ)
                      = K * Real.pi / 2 * (2 / Real.pi * (Real.pi / 2 - θ)) := by
                    field_simp
                  rw [hstep]
                  have hKπ : (0 : ℝ) ≤ K * Real.pi := mul_nonneg hK0 Real.pi_pos.le
                  exact mul_le_mul_of_nonneg_left hj (by linarith [hKπ])
          have h2 : (u z θ / Real.cos θ) ^ 2 ≤ (K * Real.pi / 2) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          nlinarith [h2, hC₀ge₂, sq_nonneg (u z θ)]
    calc (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ (2 * (u z θ) ^ 2 + C₀) * Work.FTS.EllipticEst.AngSecond.sig θ :=
          mul_le_mul_of_nonneg_right hkey hσnn
      _ = 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
            + C₀ * Work.FTS.EllipticEst.AngSecond.sig θ := by ring
  -- the majorant is integrable on `(0, π/2)` and the integrand is a.e. strongly measurable
  have hD : Integrable (fun θ => 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      + C₀ * Work.FTS.EllipticEst.AngSecond.sig θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    MeasureTheory.Integrable.add
      (MeasureTheory.Integrable.const_mul (hf0.mono_set Set.Ioo_subset_Icc_self) 2)
      (MeasureTheory.Integrable.const_mul
        (sig_integrableOn_Iθ.mono_set Set.Ioo_subset_Icc_self) C₀)
  have hmeas : AEStronglyMeasurable
      (fun θ => (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine ContinuousOn.aestronglyMeasurable (ContinuousOn.mul ?_ sig_continuousOn_Ioo)
      measurableSet_Ioo
    exact ContinuousOn.pow (hsm.continuousOn.div Real.continuous_cos.continuousOn
      (fun x hx => ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩))) 2
  have hIoo : IntegrableOn (fun θ => (u z θ / Real.cos θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) volume := by
    refine Integrable.mono' hD hmeas ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.AngSecond.sig_nonneg
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))]
    exact hpt θ hθ
  simpa only [Work.Spaces.Iθ] using
    integrableOn_congr_set hIoo (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := Real.pi / 2))

/-! ## The second slicewise integrability fact: `∫ (∂_θ(u z · / cos ·))² σ` -/

/-- The lower half `(0, π/4)`. -/
private theorem ae_psiDerivSq_lower {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 4)) := by
  have hslice : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    slice_contDiffOn_ae hA hz
  have h0 : IntegrableOn
      (fun θ => (fun θ' => u z θ') θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (g := u) hz hu
  have h2 : IntegrableOn (fun θ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
    have hbase : IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (α := α) (z := z)
        (g := Work.Spaces.pthIter 2 u) hz hA.memAng2
    have hpt : ∀ θ : ℝ, Work.Spaces.pthIter 2 u z θ
        = deriv (fun t => deriv (fun θ' => u z θ') t) θ := fun θ => rfl
    refine hbase.congr_fun (fun θ _ => ?_) measurableSet_Icc
    show (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
      = (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ
    rw [hpt θ]
  have h1 : IntegrableOn (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.Honest.sliceInterp (fun θ' => u z θ') hslice h0 h2).1
  have hsub : Set.Ioo 0 (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hbig : IntegrableOn
      (fun θ => 4 * ((deriv (fun t => u z t) θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 4 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      (Set.Ioo 0 (Real.pi / 4)) :=
    MeasureTheory.Integrable.add
      (MeasureTheory.Integrable.const_mul (MeasureTheory.IntegrableOn.mono_set h1 hsub) 4)
      (MeasureTheory.Integrable.const_mul (MeasureTheory.IntegrableOn.mono_set h0 hsub) 4)
  have hmeas : AEStronglyMeasurable
      (fun θ => (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 4))) := by
    have hcont : ContinuousOn (deriv (fun t => u z t / Real.cos t))
        (Set.Ioo 0 (Real.pi / 2)) :=
      (Work.FTS.EllipticEst.TT.contDiffOn_divCos hslice).continuousOn_deriv_of_isOpen isOpen_Ioo
        (by norm_num)
    have h1' : AEStronglyMeasurable (deriv (fun t => u z t / Real.cos t))
        (volume.restrict (Set.Ioo 0 (Real.pi / 4))) :=
      (hcont.aestronglyMeasurable measurableSet_Ioo).mono_set
        (Set.Ioo_subset_Ioo_right (by linarith [Real.pi_pos]))
    exact (h1'.pow 2).mul (Work.FTS.EllipticEst.TT.measurable_sigEta.aestronglyMeasurable)
  refine hbig.mono' hmeas ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
  have hσθ : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
    Work.FTS.EllipticEst.AngSecond.sig_nonneg
      ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hpt := Work.FTS.EllipticEst.TT.psi_deriv_sq_le hslice hθ
  have hmul : (deriv (fun t => u z t / Real.cos t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ
      ≤ (4 * (deriv (fun t => u z t) θ) ^ 2 + 4 * (u z θ) ^ 2)
        * Work.FTS.EllipticEst.AngSecond.sig θ :=
    mul_le_mul_of_nonneg_right hpt hσθ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hσθ)]
  nlinarith [hmul]

/-- The upper half `(π/4, π/2)`. -/
private theorem ae_psiDerivSq_upper {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    (hd : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  -- The angular first-order quantity `U = ∂_θ(tan θ · u)` is again honest.
  set U : ℝ → ℝ → ℝ := fun z θ => deriv (fun θ' => Real.tan θ' * u z θ') θ with hUdef
  have hU : Work.Spaces.HkMem α 0 U := by
    rw [hUdef]
    exact Work.FTS.EllipticEst.H2W.Ae.hkMem_ang1 α u G hA hu hd
  -- Slicewise `σ`-honesty transferred from `HkMem α 0 g` (the `k = 0` integrand).
  have slice_mem : ∀ {g : ℝ → ℝ → ℝ}, Work.Spaces.HkMem α 0 g →
      IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        Work.Spaces.Iθ := by
    intro g hm
    exact Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (g := g) hz hm
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt (by linarith [hθ.1, Real.pi_pos]), le_of_lt hθ.2⟩
  have hUint : IntegrableOn (fun θ => (U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := (slice_mem hU).mono_set hsub
  have hPint : IntegrableOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := (slice_mem hu).mono_set hsub
  have hmaj : Integrable
      (fun θ => 4 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 4 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      (volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :=
    MeasureTheory.Integrable.add (MeasureTheory.Integrable.const_mul hUint 4)
      (MeasureTheory.Integrable.const_mul hPint 4)
  -- a.e. strong measurability of `(ψ')²σ` from the `C¹`-regularity of the slice.
  have hsub' : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun θ hθ => ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hcos_ne : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Real.cos θ ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hslice1 : ContDiffOn ℝ 1 (fun θ' => u z θ') (Set.Ioo 0 (Real.pi / 2)) := by
    have hmap : Set.MapsTo (fun θ' : ℝ => (z, θ')) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ' hθ' => ⟨hz, hθ'⟩
    exact (hA.smooth 1).comp (by fun_prop) hmap
  have hquot : ContDiffOn ℝ 1 (fun θ' => u z θ' / Real.cos θ') (Set.Ioo 0 (Real.pi / 2)) :=
    hslice1.div Real.contDiff_cos.contDiffOn hcos_ne
  have hcontD : ContinuousOn (deriv (fun θ' => u z θ' / Real.cos θ'))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hquot.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcontD' : ContinuousOn (deriv (fun θ' => u z θ' / Real.cos θ'))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hcontD.mono hsub'
  have hsig_cont : ContinuousOn Work.FTS.EllipticEst.AngSecond.sig
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have hf : ContinuousOn (fun θ => Real.sin (2 * θ)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hne : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
      intro θ hθ
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos]))
    exact hf.rpow_const (p := -(Work.Spaces.eta)) (fun θ hθ => Or.inl (hne θ hθ))
  have haesm : AEStronglyMeasurable
      (fun θ => (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      (volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :=
    ((hcontD'.pow 2).mul hsig_cont).aestronglyMeasurable measurableSet_Ioo
  -- the pointwise bound on `(π/4, π/2)`, where `sin θ ≥ 1/√2`.
  have hpoint : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ 4 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
          + 4 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    intro θ hθ
    have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hdiff : DifferentiableAt ℝ (fun θ' => u z θ') θ :=
      (hslice1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθI)
    have hid : Real.sin θ * deriv (fun θ' => u z θ' / Real.cos θ') θ = U z θ - u z θ := by
      have h := Work.FTS.EllipticEst.AngSecond.I4_tan_mul_sub_deriv
        (fun θ' => u z θ') hθI hdiff
      rw [← h]
    have hsin2 : (1 / 2 : ℝ) ≤ Real.sin θ ^ 2 := by
      have hmem1 : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], le_of_lt (by linarith [hθ.2, Real.pi_pos])⟩
      have hmem2 : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have hsin := Real.strictMonoOn_sin hmem2 hmem1 hθ.1
      rw [Real.sin_pi_div_four] at hsin
      have h0 : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
      have hlt := pow_lt_pow_left₀ hsin h0 (by norm_num : (2 : ℕ) ≠ 0)
      have hsq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      linarith [hlt, hsq]
    have hB : (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
        ≤ 4 * (U z θ) ^ 2 + 4 * (u z θ) ^ 2 := by
      have heq : (Real.sin θ) ^ 2 * (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          = (U z θ - u z θ) ^ 2 := by rw [← hid]; ring
      have hhalf : (1 / 2) * (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          ≤ (U z θ - u z θ) ^ 2 := by
        rw [← heq]
        nlinarith [hsin2, sq_nonneg (deriv (fun θ' => u z θ' / Real.cos θ') θ)]
      have hB' : (U z θ - u z θ) ^ 2 ≤ 2 * (U z θ) ^ 2 + 2 * (u z θ) ^ 2 := by
        nlinarith [sq_nonneg (U z θ + u z θ)]
      nlinarith [hhalf, hB']
    have hsig : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg (θ := θ) ⟨le_of_lt hθI.1, le_of_lt hθI.2⟩
    calc (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ (4 * (U z θ) ^ 2 + 4 * (u z θ) ^ 2)
            * Work.FTS.EllipticEst.AngSecond.sig θ :=
          mul_le_mul_of_nonneg_right hB hsig
      _ = 4 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
            + 4 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg (deriv (fun θ' => u z θ' / Real.cos θ') θ))
      (Work.FTS.EllipticEst.AngSecond.sig_nonneg (θ := θ)
        ⟨le_of_lt (by linarith [hθ.1, Real.pi_pos]), le_of_lt hθ.2⟩))]
  exact hpoint θ hθ

/-- The second slicewise integrability fact, from the two halves. -/
private theorem ae_psiDerivSq_integrable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    (hd : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
  integrableOn_Iθ_of_halves (ae_psiDerivSq_lower hA hu hz) (ae_psiDerivSq_upper hA hu hd hz)

/-! ## The fourth slicewise integrability fact: `∫ sin²θ (∂_θ(u z · / cos ·))² σ` -/

private theorem ae_sinSq_psiDerivSq_integrable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u)
    (hd : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
  have hD := ae_psiDerivSq_integrable hA hu hd hz
  have hD' : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * ((deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ := by
    have hsin : AEStronglyMeasurable (fun θ : ℝ => Real.sin θ ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      ((Real.continuous_sin.pow 2).continuousOn).aestronglyMeasurable measurableSet_Icc
    refine hD.mono' (hsin.mul hD.aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    have hσ : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
    have hbase : 0 ≤ (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ := mul_nonneg (sq_nonneg _) hσ
    have hsin1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    calc ‖Real.sin θ ^ 2 * ((deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ)‖
        = Real.sin θ ^ 2 * ((deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) :=
          Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hbase)
      _ ≤ (deriv (fun θ' => u z θ' / Real.cos θ') θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ := mul_le_of_le_one_left hbase hsin1
  refine hD'.congr_fun (fun θ _ => ?_) measurableSet_Icc
  ring

/-! ## The target -/

theorem aeI4_open : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G → Work.Spaces.HkMem α 0 u →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
      Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ)
        (Work.Spaces.pthIter 2 u)
      ≤ Work.FTS.EllipticEst.AngSecond.IP u (Work.Spaces.pthIter 2 u)
        + C * Work.FTS.EllipticEst.AngSecond.IP u u := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.EllipticEst.H2W.I4Open
  refine ⟨C₀, hC₀pos, ?_⟩
  intro α u G hA hu hd
  -- the three honesty statements of the pairing, from the proved `IPMem` bookkeeping
  obtain ⟨-, -, -, hM1, hM2, -⟩ :=
    Work.FTS.EllipticEst.remov.aeIPMemsSlim α u G hA hu hd
  have hM3 : Work.FTS.EllipticEst.AngSecond.IPMem u u :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hu
  have hkey := hC₀ u hA.smooth hA.dirZero hA.dirPi hM1 hM2 hM3
    (fun z hz => ae_psiDivCosSq_integrable hA hu hz)
    (fun z hz => ae_psiDerivSq_integrable hA hu hd hz)
    (fun z hz => Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sig_of_hkMem (g := Work.Spaces.pthIter 2 u)
      hz hA.memAng2)
    (fun z hz => ae_sinSq_psiDerivSq_integrable hA hu hd hz)
  linarith

end

end Work.FTS.EllipticEst.Cores.AeStep2Aux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.mixedPairAux2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## 6. The mixed slot: `MixedHon` slices, AM–GM slice integrability -/

/-- The a.e. mixed honesty of `V = z ∂_z∂_θu` gives, a.e. in `z`, the integrability of the
`σ`-weighted square of `V` on the open angular interval. -/
theorem integrableOn_slice_of_MixedHon {u : ℝ → ℝ → ℝ} (hM : MixedHon u) :
    Filter.Eventually (fun z => IntegrableOn (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
      (MeasureTheory.ae (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  filter_upwards [hM.1] with z hz
  have h1 : IntegrableOn (fun θ => Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.IntegrableOn.mono_set hz (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  exact h1.congr (ae_restrict_of_forall_mem measurableSet_Ioo (fun θ _ => by ring))

/-- The radial marginal of `σ V²`, multiplied by the cutoff bound `wtB n`, is integrable. -/
theorem integrableOn_marginal_Vz_of_MixedHon {u : ℝ → ℝ → ℝ} (hM : MixedHon u) (n : ℕ) :
    IntegrableOn (fun z => Work.FTS.EllipticEst.AeColl.wtB n
      * ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
          * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioi (0 : ℝ)) :=
  (MeasureTheory.IntegrableOn.mono_set hM.2 Set.Ioi_subset_Ici_self).const_mul _

/-- The mixed angular slice `σ f g` is integrable (in `θ`) once `f` and `g` are `ℋ⁰`-honest and
the slice is a.e. strongly measurable: AM–GM bounds `σ|f g|` by `(σ f² + σ g²)/2`. -/
theorem integrableOn_sig_mul_mul_of_HkMem (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) (hg : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z)
    (hmeas : AEStronglyMeasurable (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ)
      (volume.restrict Work.Spaces.Iθ)) :
    IntegrableOn (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hle : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) ≤ volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_mono_set volume (show Set.Ioo (0 : ℝ) (Real.pi / 2)
      ⊆ Work.Spaces.Iθ from fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hf2 := integrableOn_sig_mul_sq_of_HkMem α hf hz
  have hg2 := integrableOn_sig_mul_sq_of_HkMem α hg hz
  refine Integrable.mono' (hf2.add hg2) (hmeas.mono_measure hle) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs0 := sigθ_nonneg_of_mem_Iθ
    (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h1 : |f z θ| * |g z θ| ≤ f z θ ^ 2 + g z θ ^ 2 := by
    nlinarith [sq_nonneg (|f z θ| - |g z θ|), sq_abs (f z θ), sq_abs (g z θ)]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs0]
  have h2 := mul_le_mul_of_nonneg_left h1 hs0
  calc Work.FTS.EllipticEst.AeColl.sigθ θ * |f z θ| * |g z θ|
      = Work.FTS.EllipticEst.AeColl.sigθ θ * (|f z θ| * |g z θ|) := by ring
    _ ≤ Work.FTS.EllipticEst.AeColl.sigθ θ * (f z θ ^ 2 + g z θ ^ 2) := h2
    _ = Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2
        + Work.FTS.EllipticEst.AeColl.sigθ θ * g z θ ^ 2 := by ring

/-! ## 7. Joint measurability of the four angular integrands -/

theorem aesm_joint_Vz {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2
        * Work.FTS.EllipticEst.AeColl.Vz u p.1 p.2 ^ 2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))) := by
  have hS := Work.FTS.EllipticEst.AeColl.SmoothOpen_of_AeData hA
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_sig_Q0
  have h2 : ContinuousOn
      (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz (Work.Spaces.pth u) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_fst.mul (((hS.pth).pz).continuousOn)
  exact aesm_prod_of_continuousOn_Q0 (h1.mul (h2.pow 2))

theorem aesm_joint_Uz {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2
        * Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2 ^ 2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))) := by
  have hS := Work.FTS.EllipticEst.AeColl.SmoothOpen_of_AeData hA
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_sig_Q0
  have h2 : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := continuousOn_fst.mul (hS.pz).continuousOn
  exact aesm_prod_of_continuousOn_Q0 (h1.mul (h2.pow 2))

/-- The uncurried `σ θ · Az u · ∂_θθu` is continuous on the open quadrant (for `AeData u G`). -/
theorem continuousOn_joint_AzB {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2
        * Work.FTS.EllipticEst.AeColl.Az u p.1 p.2
        * Work.Spaces.pthIter 2 u p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hS := Work.FTS.EllipticEst.AeColl.SmoothOpen_of_AeData hA
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_sig_Q0
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Az u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_rad2 hS
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_ang2 hS
  exact (h1.mul h2).mul h3

/-- The uncurried `σ θ · Uz u · ∂_θθu` is continuous on the open quadrant. -/
theorem continuousOn_joint_UzB {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2
        * Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2
        * Work.Spaces.pthIter 2 u p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hS := Work.FTS.EllipticEst.AeColl.SmoothOpen_of_AeData hA
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_sig_Q0
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_grad hS
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_ang2 hS
  exact (h1.mul h2).mul h3

end

end Work.FTS.EllipticEst.Deleg
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_Step5_s20Aesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Step5

/-! ## A.e. strong measurability of the two dominating integrands of `slot20_bound`

The two integrands

`s20F4 α Ψ = 2 w² (∂_θ⁴Ψ)² σ₄`,   `s20F3 α Ψ = 8 w² (∂_θ³Ψ)² σ₂`

(with `σ₄ = sin(2θ)^{4-γ}`, `σ₂ = sin(2θ)^{2-γ}`) are continuous on the open quadrant
`(0,∞) × (0,π/2)`: the iterated angular derivatives `∂_θ^j Ψ` are continuous there
(`hsmooth` at finite orders, one `∂_θ` at a time via the `fderiv` description of `∂_θ` on an
open set), the radial weight `w(z) = (1+z)²/z²` is continuous for `z ≠ 0`, and
`sin(2θ)^{c}` is continuous where `sin(2θ) > 0`.  Since the open quadrant differs from
`Iz ×ˢ Iθ` by a null set, and the whole integrand vanishes identically at `z = 0` (because
`w 0 = 0`), continuity gives a.e. strong measurability of every `θ`-slice and of the joint
integrand; Fubini for Bochner integrals then transfers the joint measurability to the
parameter integrals `z ↦ ∫_θ …`. -/

/-- The open quadrant of the smoothness hypothesis. -/
private abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem s20Aesm (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.AEStronglyMeasurable
          (fun θ => Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.AEStronglyMeasurable
          (fun θ => Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hV : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo
  -- One angular derivative at a time: on an open set the partial `∂_θ` is the evaluation of
  -- the Fréchet derivative at `(0,1)`, so finite-order smoothness drops by one.
  have hstep : ∀ {H : ℝ → ℝ → ℝ} {m : ℕ},
      ContDiffOn ℝ (m + 1) (Function.uncurry H) Qd →
      ContDiffOn ℝ m (Function.uncurry (Work.Spaces.pth H)) Qd := by
    intro H m h
    have key : ∀ (z θ : ℝ), (z, θ) ∈ Qd →
        Work.Spaces.pth H z θ = fderiv ℝ (Function.uncurry H) (z, θ) (0, 1) :=
      fun z θ hzθ => Work.Spaces.pth_eq_fderiv
        ((h.differentiableOn (by norm_num : (m + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
          (hV.mem_nhds hzθ))
    have hfd : ContDiffOn ℝ m (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry H) p) Qd :=
      h.fderiv_of_isOpen hV (m := m) (by norm_num)
    have hcomp : ContDiffOn ℝ m
        (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry H) p) (0, 1)) Qd :=
      hfd.clm_apply contDiffOn_const
    refine hcomp.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    exact key z θ hp
  -- The uncurried angular derivatives `∂_θ^j Ψ` are continuous on the open quadrant.
  have hpth4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 4 Ψ p.1 p.2) Qd := by
    have h1 : ContDiffOn ℝ 4 (Function.uncurry Ψ) Qd := hsmooth 4
    have h2 : ContDiffOn ℝ 3 (Function.uncurry (Work.Spaces.pth Ψ)) Qd := hstep (m := 3) h1
    have h3 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth Ψ))) Qd :=
      hstep (m := 2) h2
    have h4 : ContDiffOn ℝ 1
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pth Ψ)))) Qd :=
      hstep (m := 1) h3
    have h5 : ContDiffOn ℝ 0
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pth
          (Work.Spaces.pth Ψ))))) Qd :=
      hstep (m := 0) h4
    have h5c : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.pthIter 4 Ψ)) Qd := by
      simpa only [Work.Spaces.pthIter] using h5
    exact h5c.continuousOn
  have hpth3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 3 Ψ p.1 p.2) Qd := by
    have h1 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Qd := hsmooth 3
    have h2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) Qd := hstep (m := 2) h1
    have h3 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth Ψ))) Qd :=
      hstep (m := 1) h2
    have h4 : ContDiffOn ℝ 0
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pth Ψ)))) Qd :=
      hstep (m := 0) h3
    have h4c : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.pthIter 3 Ψ)) Qd := by
      simpa only [Work.Spaces.pthIter] using h4
    exact h4c.continuousOn
  -- The radial weight, the sine and the angular weights are continuous on the quadrant.
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
    have hnum : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2) Qd :=
      (continuous_const.continuousOn.add continuous_fst.continuousOn).pow 2
    have hden : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2) Qd := continuous_fst.continuousOn.pow 2
    have hne : ∀ p ∈ Qd, p.1 ^ 2 ≠ 0 := fun p hp => pow_ne_zero 2 (ne_of_gt hp.1)
    exact hnum.div hden hne
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Qd :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hsinne : ∀ p ∈ Qd, Real.sin (2 * p.2) ≠ 0 := fun p hp =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2]))
  have hsig4 : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) p.2) Qd :=
    hsin.rpow_const (p := 4 - Work.Spaces.gam α) (fun p hp => Or.inl (hsinne p hp))
  have hsig2 : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) p.2) Qd :=
    hsin.rpow_const (p := 2 - Work.Spaces.gam α) (fun p hp => Or.inl (hsinne p hp))
  -- Hence the two integrands are continuous on the open quadrant.
  have hcont4 : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.H2W.s20F4 α Ψ p.1 p.2) Qd := by
    have h : ContinuousOn (fun p : ℝ × ℝ =>
        2 * (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter 4 Ψ p.1 p.2) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) p.2)) Qd :=
      (continuousOn_const.mul (hw.pow 2)).mul ((hpth4.pow 2).mul hsig4)
    simpa only [Work.FTS.EllipticEst.H2W.s20F4] using h
  have hcont3 : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.H2W.s20F3 α Ψ p.1 p.2) Qd := by
    have h : ContinuousOn (fun p : ℝ × ℝ =>
        8 * (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter 3 Ψ p.1 p.2) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) p.2)) Qd :=
      (continuousOn_const.mul (hw.pow 2)).mul ((hpth3.pow 2).mul hsig2)
    simpa only [Work.FTS.EllipticEst.H2W.s20F3] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the `θ`-slices of `s20F4`
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
    · -- at `z = 0` the integrand vanishes because `w 0 = 0`
      rw [← h]
      have hzero : (fun θ : ℝ => Work.FTS.EllipticEst.H2W.s20F4 α Ψ 0 θ) =
          fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => by simp [Work.FTS.EllipticEst.H2W.s20F4, Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont4 h
  · -- the `θ`-slices of `s20F3`
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
    · rw [← h]
      have hzero : (fun θ : ℝ => Work.FTS.EllipticEst.H2W.s20F3 α Ψ 0 θ) =
          fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => by simp [Work.FTS.EllipticEst.H2W.s20F3, Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont3 h
  · -- the `z`-parameter integral of `s20F4`, by Fubini for Bochner integrals
    exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont4).integral_prod_right'
  · exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont3).integral_prod_right'

end Work.FTS.EllipticEst.H2W.Step5
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AngBW.aeStep3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

open Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false


set_option autoImplicit false

/-! ## The pointwise rearrangement of the equation -/

/-- **The equation solved for `α² z² ∂_zz u`** on the open quadrant. -/
theorem scaled_rad2_eq {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    α ^ 2 * rad2 u z θ = -G z θ - α * (5 + α) * grad u z θ - ang2 u z θ + ang1 u z θ
      - 6 * u z θ := by
  have h2 := AeData.eq h z hz θ hθ0 hθ1
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at h2
  have hrad : rad2 u z θ = z ^ 2 * Work.Spaces.pzIter 2 u z θ := rfl
  have hg : grad u z θ = z * Work.Spaces.pz u z θ := rfl
  have ha : ang2 u z θ = Work.Spaces.pthIter 2 u z θ := rfl
  have hu : ang1 u z θ = Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ := rfl
  rw [hrad, hg, ha, hu]
  linarith

/-! ## The pointwise domination of the level-`0` integrands -/

/-- The case `n = 5` of Cauchy–Schwarz: `(Σ aᵢ)² ≤ 5 Σ aᵢ²`. -/
private theorem five_term_sq_le (a b c d e : ℝ) : (a + b + c + d + e) ^ 2 ≤
    5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d),
    sq_nonneg (c - e), sq_nonneg (d - e)]

/-- **The pointwise domination of the level-`0` integrand of `α² z²∂_zz u`** on the whole
closed quadrant: the boundary lines contribute `0 ≤ 0`, and on the open quadrant the
rearranged equation and Cauchy–Schwarz give the result. -/
theorem HkIntegrand_rad2_le {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
        ≤ 5 * (Work.Spaces.HkIntegrand α 0 G z θ
            + (α * (5 + α)) ^ 2 * Work.Spaces.HkIntegrand α 0 (grad u) z θ
            + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ
            + Work.Spaces.HkIntegrand α 0 (ang1 u) z θ
            + 6 ^ 2 * Work.Spaces.HkIntegrand α 0 u z θ) := by
  intro z hz θ hθ
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0]
    have hw : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
    simp [hw]
  rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθ0pos
  · rw [← hθ0]
    have hr : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [Real.zero_rpow]; norm_num [Work.Spaces.eta]
    simp [show (2 : ℝ) * 0 = 0 from by norm_num, hr]
  rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).2 with hθpi | hθlt
  · rw [hθpi, show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
    have hr : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [Real.zero_rpow]; norm_num [Work.Spaces.eta]
    simp [hr]
  · set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hW
    have h1 := scaled_rad2_eq h hzpos hθ0pos hθlt
    have hss : (α ^ 2 * rad2 u z θ) * W
        = -(G z θ * W) - (α * (5 + α) * (grad u z θ * W)) - (ang2 u z θ * W)
          + ang1 u z θ * W - 6 * (u z θ * W) := by
      rw [h1]; ring
    rw [hss]
    have h5 := five_term_sq_le (-(G z θ * W)) (-(α * (5 + α) * (grad u z θ * W)))
      (-(ang2 u z θ * W)) (ang1 u z θ * W) (-(6 * (u z θ * W)))
    nlinarith [h5]

/-! ## The honest integration step -/

/-- **Five-term aggregation of a pointwise integrand domination.**  If the level-`0`
integrand of `h` is dominated by a five-term combination of the integrands of `f₁,…,f₅`
and the latter are honest, then the same holds for the `HkSq`-functionals. -/
theorem HkSq_five_le {α : ℝ} {f₁ f₂ f₃ f₄ f₅ h : ℝ → ℝ → ℝ} (c₁ c₂ c₃ c₄ c₅ : ℝ)
    (h₁ : Work.Spaces.HkMem α 0 f₁) (h₂ : Work.Spaces.HkMem α 0 f₂)
    (h₃ : Work.Spaces.HkMem α 0 f₃) (h₄ : Work.Spaces.HkMem α 0 f₄)
    (h₅ : Work.Spaces.HkMem α 0 f₅)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 h z θ
        ≤ 5 * (c₁ ^ 2 * Work.Spaces.HkIntegrand α 0 f₁ z θ
            + c₂ ^ 2 * Work.Spaces.HkIntegrand α 0 f₂ z θ
            + c₃ ^ 2 * Work.Spaces.HkIntegrand α 0 f₃ z θ
            + c₄ ^ 2 * Work.Spaces.HkIntegrand α 0 f₄ z θ
            + c₅ ^ 2 * Work.Spaces.HkIntegrand α 0 f₅ z θ)) :
    Work.Spaces.HkSq α 0 h
      ≤ 5 * (c₁ ^ 2 * Work.Spaces.HkSq α 0 f₁ + c₂ ^ 2 * Work.Spaces.HkSq α 0 f₂
          + c₃ ^ 2 * Work.Spaces.HkSq α 0 f₃ + c₄ ^ 2 * Work.Spaces.HkSq α 0 f₄
          + c₅ ^ 2 * Work.Spaces.HkSq α 0 f₅) := by
  set F : Fin 5 → ℝ → ℝ → ℝ := ![f₁, f₂, f₃, f₄, f₅] with hF
  set c : Fin 5 → ℝ := ![c₁, c₂, c₃, c₄, c₅] with hc
  have hF0 : F 0 = f₁ := by simp [hF]
  have hF1 : F 1 = f₂ := by simp [hF]
  have hF2 : F 2 = f₃ := by simp [hF]
  have hF3 : F 3 = f₄ := by simp [hF]
  have hF4 : F 4 = f₅ := by simp [hF]
  have hc0 : c 0 = c₁ := by simp [hc]
  have hc1 : c 1 = c₂ := by simp [hc]
  have hc2 : c 2 = c₃ := by simp [hc]
  have hc3 : c 3 = c₄ := by simp [hc]
  have hc4 : c 4 = c₅ := by simp [hc]
  have hFmem : ∀ i, Work.Spaces.HkMem α 0 (F i) := by
    intro i
    fin_cases i <;> simp [hF0, hF1, hF2, hF3, hF4, h₁, h₂, h₃, h₄, h₅]
  have hpt' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 h z θ
        ≤ 5 * ∑ i : Fin 5, (c i) ^ 2 * Work.Spaces.HkIntegrand α 0 (F i) z θ := by
    intro z hz θ hθ
    have := hpt z hz θ hθ
    rw [Fin.sum_univ_five]
    simp only [hc0, hc1, hc2, hc3, hc4, hF0, hF1, hF2, hF3, hF4]
    linarith [this]
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h z θ)
        ≤ 5 * ∑ i : Fin 5,
            (c i) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (F i) z θ) := by
    intro z hz
    have hint : MeasureTheory.Integrable (fun θ => 5 * ∑ i : Fin 5,
        (c i) ^ 2 * Work.Spaces.HkIntegrand α 0 (F i) z θ)
        (volume.restrict Work.Spaces.Iθ) := by
      refine ((MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => ?_)).const_mul 5)
      exact ((hFmem i).1 z hz).const_mul _
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α 0 h z θ)
      (g := fun θ => 5 * ∑ i : Fin 5, (c i) ^ 2 * Work.Spaces.HkIntegrand α 0 (F i) z θ)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      hint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt' z hz θ hθ)
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finset_sum]
    · simp only [MeasureTheory.integral_const_mul]
    · intro i _
      exact ((hFmem i).1 z hz).const_mul _
  have hbound : MeasureTheory.IntegrableOn (fun z => 5 * ∑ i : Fin 5,
      (c i) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (F i) z θ))
      Work.Spaces.Iz := by
    refine ((MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => ?_)).const_mul 5)
    exact ((hFmem i).2).const_mul _
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h z θ)
    (g := fun z => 5 * ∑ i : Fin 5,
        (c i) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (F i) z θ))
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
    hbound
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  have e : (∫ z in Work.Spaces.Iz, 5 * ∑ i : Fin 5,
      (c i) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (F i) z θ))
      = 5 * (c₁ ^ 2 * Work.Spaces.HkSq α 0 f₁ + c₂ ^ 2 * Work.Spaces.HkSq α 0 f₂
          + c₃ ^ 2 * Work.Spaces.HkSq α 0 f₃ + c₄ ^ 2 * Work.Spaces.HkSq α 0 f₄
          + c₅ ^ 2 * Work.Spaces.HkSq α 0 f₅) := by
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finset_sum]
    · rw [Finset.mul_sum, Fin.sum_univ_five]
      simp only [hc0, hc1, hc2, hc3, hc4, hF0, hF1, hF2, hF3, hF4]
      simp only [MeasureTheory.integral_const_mul]
      simp only [Work.Spaces.HkSq]
      ring
    · intro i _
      exact ((hFmem i).2).const_mul _
  exact houter.trans_eq e

/-- **The `HkSq`-domination of `α² z²∂_zz u`.** -/
theorem HkSq_rad2_le {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G)
    (hu : Work.Spaces.HkMem α 0 u) (hd : Work.Spaces.HkMem α 0 (grad u))
    (ha : Work.Spaces.HkMem α 0 (ang1 u)) :
    Work.Spaces.HkSq α 0 (fun z θ => α ^ 2 * rad2 u z θ)
      ≤ 5 * (Work.Spaces.HkSq α 0 G + (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (grad u)
          + Work.Spaces.HkSq α 0 (ang2 u) + Work.Spaces.HkSq α 0 (ang1 u)
          + 6 ^ 2 * Work.Spaces.HkSq α 0 u) := by
  have hmain := HkSq_five_le (f₁ := G) (f₂ := grad u) (f₃ := ang2 u) (f₄ := ang1 u)
    (f₅ := u) (h := fun z θ => α ^ 2 * rad2 u z θ) 1 (α * (5 + α)) 1 1 6
    (AeData.memG h) hd (AeData.memAng2 h) ha hu
    (fun z hz θ hθ => by
      have hpt := HkIntegrand_rad2_le h z hz θ hθ
      simpa only [one_pow, one_mul] using hpt)
  simpa only [one_pow, one_mul] using hmain

/-! ## The square-root arithmetic -/

/-- The two-term square root inequality `√(a+b) ≤ √a + √b`. -/
private theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- `√(a+b+c+d+e) ≤ √a + √b + √c + √d + √e` for nonnegative `a,…,e`. -/
private theorem sqrt_five_le {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) :
    Real.sqrt (a + b + c + d + e)
      ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d + Real.sqrt e := by
  have h1 : Real.sqrt (a + b + c + d + e) ≤ Real.sqrt (a + b + c + d) + Real.sqrt e :=
    sqrt_add_le' (by linarith) he
  have h2 : Real.sqrt (a + b + c + d) ≤ Real.sqrt (a + b + c) + Real.sqrt d :=
    sqrt_add_le' (by linarith) hd
  have h3 : Real.sqrt (a + b + c) ≤ Real.sqrt (a + b) + Real.sqrt c :=
    sqrt_add_le' (by linarith) hc
  have h4 : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := sqrt_add_le' ha hb
  linarith

/-! ## The inputs from the analysis of the a.e. class -/

/- **Honesty of `u`**, of `z ∂_z u` and of `∂_θ(tan θ · u)` are all proved (with the same
names, in the same namespace) in the delivered, axiom-clean modules
`H2W/Ae/hkMem_u.lean`, `H2W/Ae/hkMem_gradU.lean` and `H2W/Ae/hkMem_ang1.lean`, imported at the
top of this file; likewise the `I₄`-bound `ang1_bound` (`H2W/Ae/ang1_bound.lean`). -/

/-! ## The assembly -/

/-- **`step3Ae` from the pieces.** -/
theorem step3Ae_of_pieces (CU : ℝ) (hCU : 0 < CU)
    (hu : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G → Work.Spaces.HkMem α 0 u)
    (hd : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G → Work.Spaces.HkMem α 0 (grad u))
    (ha : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G → Work.Spaces.HkMem α 0 (ang1 u))
    (hb : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      Real.sqrt (Work.Spaces.HkSq α 0 (ang1 u))
        ≤ CU * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u)))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
        nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
          ≤ C * (nrm α G + α * nrm α (grad u) + nrm α (ang2 u) + nrm α u) := by
  refine ⟨Real.sqrt 5 * (11 + CU), by positivity, ?_⟩
  intro α u G hA
  have hα4 : α ≤ 1 / 4 := AeData.hα4 hA
  have hα0 : (0 : ℝ) ≤ α := le_of_lt (AeData.hα hA)
  have hSq := HkSq_rad2_le hA (hu α u G hA) (hd α u G hA) (ha α u G hA)
  have hang := hb α u G hA
  -- the individual nonnegativities
  have nG : 0 ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
  have nd : 0 ≤ Work.Spaces.HkSq α 0 (grad u) := Work.Spaces.HkSq_nonneg α 0 (grad u)
  have nB : 0 ≤ Work.Spaces.HkSq α 0 (ang2 u) := Work.Spaces.HkSq_nonneg α 0 (ang2 u)
  have nA : 0 ≤ Work.Spaces.HkSq α 0 (ang1 u) := Work.Spaces.HkSq_nonneg α 0 (ang1 u)
  have nU : 0 ≤ Work.Spaces.HkSq α 0 u := Work.Spaces.HkSq_nonneg α 0 u
  have hc2 : 0 ≤ (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (grad u) :=
    mul_nonneg (sq_nonneg _) nd
  -- the square root of the sum
  have hroot : nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      ≤ Real.sqrt 5 * (Real.sqrt (Work.Spaces.HkSq α 0 G)
          + α * (5 + α) * Real.sqrt (Work.Spaces.HkSq α 0 (grad u))
          + Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
          + Real.sqrt (Work.Spaces.HkSq α 0 (ang1 u))
          + 6 * Real.sqrt (Work.Spaces.HkSq α 0 u)) := by
    have h1 : nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        = Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => α ^ 2 * rad2 u z θ)) := rfl
    rw [h1]
    have h2 : Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => α ^ 2 * rad2 u z θ))
        ≤ Real.sqrt (5 * (Work.Spaces.HkSq α 0 G
            + (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (grad u)
            + Work.Spaces.HkSq α 0 (ang2 u) + Work.Spaces.HkSq α 0 (ang1 u)
            + 6 ^ 2 * Work.Spaces.HkSq α 0 u)) := Real.sqrt_le_sqrt hSq
    refine h2.trans ?_
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 5)
    have h5 := sqrt_five_le nG hc2 nB nA (by positivity : (0 : ℝ) ≤ 6 ^ 2 * Work.Spaces.HkSq α 0 u)
    refine h5.trans ?_
    have e1 : Real.sqrt ((α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (grad u))
        = α * (5 + α) * Real.sqrt (Work.Spaces.HkSq α 0 (grad u)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hα0 (by linarith))]
    have e2 : Real.sqrt (6 ^ 2 * Work.Spaces.HkSq α 0 u)
        = 6 * Real.sqrt (Work.Spaces.HkSq α 0 u) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6 ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)]
    rw [e1, e2]
  -- the `ang1`-bound and the constant
  refine hroot.trans ?_
  have nSg : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 G) := Real.sqrt_nonneg _
  have nSd : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (grad u)) := Real.sqrt_nonneg _
  have nSb : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u)) := Real.sqrt_nonneg _
  have nSu : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 u) := Real.sqrt_nonneg _
  have h5a : (5 : ℝ) + α ≤ 11 + CU := by linarith
  have h1a : (1 : ℝ) + CU ≤ 11 + CU := by linarith
  have h6a : (6 : ℝ) + CU ≤ 11 + CU := by linarith
  have hone : (1 : ℝ) ≤ 11 + CU := by linarith
  have hCU0 : (0 : ℝ) ≤ CU := le_of_lt hCU
  have hang' : Real.sqrt (Work.Spaces.HkSq α 0 (ang1 u))
      ≤ CU * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))) := hang
  have key : Real.sqrt (Work.Spaces.HkSq α 0 G)
        + α * (5 + α) * Real.sqrt (Work.Spaces.HkSq α 0 (grad u))
        + Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
        + Real.sqrt (Work.Spaces.HkSq α 0 (ang1 u))
        + 6 * Real.sqrt (Work.Spaces.HkSq α 0 u)
      ≤ (11 + CU) * (Real.sqrt (Work.Spaces.HkSq α 0 G)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (grad u))
          + Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
          + Real.sqrt (Work.Spaces.HkSq α 0 u)) := by
    have hαd : 0 ≤ α * Real.sqrt (Work.Spaces.HkSq α 0 (grad u)) := mul_nonneg hα0 nSd
    have k1 : Real.sqrt (Work.Spaces.HkSq α 0 G)
        ≤ (11 + CU) * Real.sqrt (Work.Spaces.HkSq α 0 G) := by nlinarith [nSg, hone]
    have k2 : α * (5 + α) * Real.sqrt (Work.Spaces.HkSq α 0 (grad u))
        ≤ (11 + CU) * (α * Real.sqrt (Work.Spaces.HkSq α 0 (grad u))) := by
      nlinarith [hαd, h5a]
    have k3 : Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
          + Real.sqrt (Work.Spaces.HkSq α 0 (ang1 u))
          + 6 * Real.sqrt (Work.Spaces.HkSq α 0 u)
        ≤ (11 + CU) * Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
          + (11 + CU) * Real.sqrt (Work.Spaces.HkSq α 0 u) := by
      have hA : CU * Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
            + (CU + 6) * Real.sqrt (Work.Spaces.HkSq α 0 u)
          ≤ (11 + CU) * Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
            + (11 + CU) * Real.sqrt (Work.Spaces.HkSq α 0 u) := by
        nlinarith [nSb, nSu]
      nlinarith [hang', hA, nSb, nSu]
    nlinarith [k1, k2, k3, nSg, nSd, nSb, nSu, hα0]
  simpa only [nrm, mul_assoc] using mul_le_mul_of_nonneg_left key (Real.sqrt_nonneg 5)



end Work.FTS.EllipticEst.H2W.AngBW.S3

namespace Work.FTS.EllipticEst.H2W.AngBW


end Work.FTS.EllipticEst.H2W.AngBW
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.PsiSlices.ReductionsC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.PsiSlices

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## The covariance reduction: it suffices to prove the conclusion at `z = 1`

Because the elliptic operator is an Euler-type operator, the class `WeakPos2` is invariant under
the radial dilation `z ↦ lam·z`, and the iterated radial derivative of a dilated datum is `lam^m`
times the dilated slice.  Hence a proof of the conclusion *at the single point* `z = 1`, for every
class datum, gives the conclusion at every `z > 0` (and so a.e.): the remaining content of the
target is a *pointwise* statement, with no measure theory in `z`. -/


/-! ## The `θ`-side bridge for the *shifted* operator, and the reduction to levels 3 and 4

`H2W.PsiSlices.shiftedSourcePoleBound` (the child lemma proved from the shifted operator's own
indicial structure) converts a `sinθcos²θ`-integrable source of `Lzero1 - c` into the pole bound.
Combining it with the level-1 and level-2 identities turns the reduction around: the `z`-regress
now closes *downward*, from the top two levels.

Precisely: given the σ-integrability of `∂_z³Ψ(z,·)` and `∂_z⁴Ψ(z,·)` for a.e. `z`,
* the level-2 identity written as `(Lzero1 - γ₂)(∂_z²Ψ) = ∂_z²F + (4α²z+α(5+α)z)∂_z³Ψ + α²z²∂_z⁴Ψ`
  gives `∂_z²Ψ` (bridge with `c = γ₂ = 2α² + 2α(5+α)`);
* the level-1 identity written as `(Lzero1 - γ₁)(∂_zΨ) = ∂_zF + 2α²z∂_z²Ψ + α²z²∂_z³Ψ + α(5+α)z∂_z²Ψ`
  gives `∂_zΨ` (bridge with `c = γ₁ = α(5+α)`);
* the level-0 identity (`γ₀ = 0`) gives `Ψ` itself (the unshifted bridge).

So the remaining content of the target is exactly the case `m = 3, 4` — the datum-side endpoint
rigidity at the top two levels (the requester's "genuinely new content is `m = 4`"). -/




/-! ## The unconditional covariance reduction (the two dilation children are proved)

Both dilation inputs of `pzIterSliceIntegrable_of_at_one` are now available in the tree
(`H2W.PsiSlices.weakPos2_dilate` and `H2W.PsiSlices.pzIter_dilate`), so the reduction is
unconditional: the target is *equivalent* to the pointwise statement at `z = 1`. -/


end
end Work.FTS.EllipticEst.H2W.PsiSlices
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.aeSliceHonestOfSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W.aeSliceHonestOfSlots`

For a datum `(F, Ψ)` of the weak class `Work.FTS.EllipticEst.WeakPos2 α F Ψ` (`0 < α ≤ 1/4`)
whose *slots* are honest — the second angular derivative of each of the slices
`Ψ, ∂_zΨ, ∂_z²Ψ` is `ℋ⁰`-honest (`hθ`), and so is `z²∂_z³Ψ` (`hr`) — almost every angular
slice `θ ↦ ∂_z^jΨ(z,θ)`, `j ≤ 3`, is integrable against `sinθcos²θ` on `Iθ = [0,π/2]`.

The proof works *for every* `z > 0` (the first conjunct of `Work.Spaces.HkMem` holds at every
`z ∈ Iz`), so the almost-everywhere statement is immediate.

* `j ≤ 2`: `HkMem α 0 (∂_θ²(∂_z^jΨ))` gives, on each slice, the integrability of
  `(∂_θ²u)²σ` (`σ = sin(2θ)^{-η}`), since the radial weight is a nonzero constant in `θ`.
  The one-variable theorem `Honest.slice_bdd_of_sq_mul_sEta` then bounds the slice `u` on
  the open interval, and a bounded function is `sinθcos²θ`-integrable there.
* `j = 3`: `hr` gives the `σ`-square-integrability of the slice itself, and
  `abs_mul_sinCos2_le_weighted` absorbs `|u·sinθcos²θ|` into the weighted square
  `(u·w(z)/sin(2θ)^{η/2})² + 1`.
-/

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Elementary facts about the angular profile `sinθcos²θ` -/





/-! ## The level-`0` integrand, and the `σ`-weighted square of a slice -/



/-! ## The two slices of `pthIter 2` -/


/-! ## The target -/


end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.aslotTwoShift_aeDzTrace_gam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `γ`-weighted `θ`-trace of `z ∂_z u` at the two endpoints

This file ports the proof of `Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk` from the `η`-weight
`σ = sin(2·)^{-η}` (i.e. `Work.FTS.EllipticEst.sEta`) to the `γ`-weight
`σ_γ = sin(2·)^{2-γ}` (`γ = Work.Spaces.gam α = 1 + α/10`):

* the `η`-weighted slice-rate lemma `Work.EllipticEst.Core.sliceBoundaryLimit` is replaced by
  the `γ`-weighted `Work.FTS.EllipticEst.Cores.sliceRateSigA` (the exponent `1 + η > 0` of the
  reciprocal mass becomes `γ - 1 = α/10 > 0`, and the weight becomes `σ_γ`);
* the per-slice `η`-honesty `HkMem α 0 (∂_θ(z ∂_z u))` is replaced by the `γ`-weighted honesty
  `hMixS`, which is only available *almost everywhere in* `z`; the outer honesty `hMixO` is used
  in its honest (everywhere) form.  Hence the two endpoint limits are established only for a.e.
  `z ∈ (0,∞)`, on the intersection of the a.e. set of `hMixS` with the a.e. trace set of
  `H2W.AeLeftClean.sliceLeftTendstoClean`.

The slice is `θ ↦ z ∂_z u(z,θ)`, whose derivative is `D_z(∂_θ u) = z ∂_θ∂_z u` by Clairaut
(`deriv_Dz_slice`).  The traces of `u` itself (`sliceLeftTendstoClean`,
`H2W.AeProof.AeSliceRightTendsto`) and the Lebesgue-differentiation step
(`aeZeroOn_of_intervalIntegralZero`) are weight-independent.

**Note on the rate lemma used.**  The intended input is
`Work.FTS.EllipticEst.Prop.aslotTwoShift_sliceBoundaryLimit_gam`.  That module is still a `sorry`
in this workspace, while its sibling `Work.FTS.EllipticEst.Cores.sliceRateSigA` *proves* the
identical statement (with the weaker hypothesis `α ≤ 1` in place of `α ≤ 1/4`); the proof below
therefore uses `sliceRateSigA`, which keeps the whole import cone of this module free of
`sorryAx`.  Nothing else in the argument depends on that choice.

**A.e. bookkeeping.**  Since `hMixS` is only an a.e. statement, the proof first extracts a
measurable null set `N` containing
`{z > 0 | ¬ IntegrableOn ((∂_θ∂_z u)² σ_γ) Iθ} ∪ {z > 0 | u(z,·) ↛ 0 at 0⁺}`
and works on the conull complement `Nᶜ`: the per-slice honesty, the endpoint parameters
`c0f`/`c1f` (defined by classical choice, with the value `0` off `Nᶜ`) and the pointwise bounds
only hold there, and all invocations of the dominated-convergence lemma
(`tendsto_setIntegral_pz_ae`, the a.e. version of the original `tendsto_setIntegral_pz`) are
required only a.e. in `z`.  The Lebesgue-differentiation argument then applies on
`(ε,∞) ∩ Nᶜ` and yields `dzTrace0 = 0` and `dzTrace1 = 0` a.e.; the final limits need `z ∈ Nᶜ`
only to read off the endpoint parameters, which is again a conull condition.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

/-! ## 1. The `γ`-weighted slice energy of `z ∂_z u` -/

/-- `gamEnergy α u z = ∫_θ (∂_θ(z ∂_z u)(z,θ))² σ_γ(θ) dθ`, the `γ`-weighted angular energy of
the slice `θ ↦ z ∂_z u(z,θ)` (`σ_γ θ = sin(2θ)^{2-γ}`). -/
def gamEnergy (α : ℝ) (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * AslotGam.sgam α θ

theorem gamEnergy_nonneg (α : ℝ) (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ gamEnergy α u z :=
  setIntegral_nonneg measurableSet_Icc fun θ hθ =>
    mul_nonneg (sq_nonneg _) (AslotGam.sgam_nonneg hθ)

theorem gamEnergy_eq_Ioo (α : ℝ) (u : ℝ → ℝ → ℝ) (z : ℝ) :
    gamEnergy α u z = ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * AslotGam.sgam α θ :=
  MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm

/-- The derivative of the slice `θ ↦ z ∂_z u(z,θ)` is `z ∂_θ∂_z u = D_z(∂_θ u)` (Clairaut). -/
theorem deriv_Dz_slice {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    deriv (fun θ' => Work.Spaces.Dz u z θ') θ = Work.Spaces.Dz (Work.Spaces.pth u) z θ := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
    (hS.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))
  have hcl := Work.Spaces.pz_pth_comm (f := u) hcd
  have h1 : deriv (fun θ' => Work.Spaces.Dz u z θ') θ
      = z * Work.Spaces.pth (Work.Spaces.pz u) z θ := by
    simp only [Work.Spaces.Dz, Work.Spaces.pth, deriv_const_mul_field]
  rw [h1]
  show z * Work.Spaces.pth (Work.Spaces.pz u) z θ = z * Work.Spaces.pz (Work.Spaces.pth u) z θ
  exact congrArg (fun t => z * t) hcl.symm

theorem w_eq_zero_at_zero : Work.Spaces.w 0 = 0 := by
  rw [Work.Spaces.w]; norm_num

theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (sq_pos_of_pos (by linarith)) (sq_pos_of_pos hz)


/-- The outer `z`-integrability of `w²·gamEnergy`, straight from the `γ`-weighted outer
honesty `hMixO`. -/
theorem integrableOn_w2_gamEnergy {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hMixO : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * AslotGam.sgam α θ) Iz) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * gamEnergy α u z) Iz := by
  refine MeasureTheory.Integrable.congr hMixO ?_
  filter_upwards with z
  have h1 : (∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * AslotGam.sgam α θ)
      = ∫ θ in Iθ, (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * AslotGam.sgam α θ) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [h1, MeasureTheory.integral_const_mul]
  rfl

/-- Continuity of the radial weight on `(a,b)` with `0 ≤ a`. -/
theorem continuousOn_w {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioo a b) := by
  rw [show (fun z : ℝ => Work.Spaces.w z) = fun z => (1 + z) ^ 2 / z ^ 2 from rfl]
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro z hz
    exact pow_ne_zero 2 (ne_of_gt (lt_of_le_of_lt ha hz.1))

/-- A.e.-measurability of the `γ`-weighted energy on subintervals of `(0,∞)`. -/
theorem aemeasurable_gamEnergy_Ioo {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hMixO : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * AslotGam.sgam α θ) Iz)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    AEMeasurable (gamEnergy α u) (volume.restrict (Set.Ioo a b)) := by
  have hsub : Set.Ioo a b ⊆ Iz := fun x hx => le_of_lt (lt_of_le_of_lt ha hx.1)
  have h1 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * gamEnergy α u z)
      (Set.Ioo a b) := (integrableOn_w2_gamEnergy hMixO).mono_set hsub
  have h1m : AEMeasurable (fun z => (Work.Spaces.w z) ^ 2 * gamEnergy α u z)
      (volume.restrict (Set.Ioo a b)) := h1.aemeasurable
  have hwm : AEMeasurable (fun z => ((Work.Spaces.w z) ^ 2)⁻¹)
      (volume.restrict (Set.Ioo a b)) := by
    refine ContinuousOn.aemeasurable ?_ measurableSet_Ioo
    exact ((continuousOn_w ha).pow 2).inv₀
      (fun z hz => pow_ne_zero 2 (ne_of_gt (w_pos_of_pos (lt_of_le_of_lt ha hz.1))))
  refine (hwm.mul h1m).congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with z hz
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (w_pos_of_pos (lt_of_le_of_lt ha hz.1)))
  exact inv_mul_cancel_left₀ hw _


/-- `gamEnergy/s⁴` is locally integrable on `(0,∞)` (dominated by `w²·gamEnergy`). -/
theorem integrableOn_gamEnergy_div_pow_four {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hMixO : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * AslotGam.sgam α θ) Iz)
    {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun s => gamEnergy α u s / s ^ 4) (Set.Ioo 0 b) := by
  have h1 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * gamEnergy α u z)
      (Set.Ioo 0 b) :=
    (integrableOn_w2_gamEnergy hMixO).mono_set (fun x hx => le_of_lt hx.1)
  have hΦm : AEMeasurable (gamEnergy α u) (volume.restrict (Set.Ioo 0 b)) :=
    aemeasurable_gamEnergy_Ioo hMixO le_rfl hb
  have h4inv : AEMeasurable (fun s : ℝ => (s ^ 4)⁻¹) (volume.restrict (Set.Ioo 0 b)) := by
    refine ContinuousOn.aemeasurable ?_ measurableSet_Ioo
    exact (continuousOn_id.pow 4).inv₀ (fun z hz => pow_ne_zero 4 (ne_of_gt hz.1))
  refine MeasureTheory.Integrable.mono' h1.abs ?_ ?_
  · refine ((hΦm.mul h4inv).aestronglyMeasurable).congr ?_
    filter_upwards with s
    simp only [Pi.mul_apply, div_eq_mul_inv]
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with z hz
    have hzpos : 0 < z := hz.1
    have hΦ := gamEnergy_nonneg α u z
    have hw4 : (1:ℝ) / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 := by
      have h1z : (1:ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith)
      have hz4 : (0:ℝ) ≤ z ^ 4 := by positivity
      have hkey : (1:ℝ) * z ^ 4 ≤ (1 + z) ^ 4 * z ^ 4 :=
        mul_le_mul_of_nonneg_right h1z hz4
      rw [Work.Spaces.w]
      simp only [div_pow]
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < z ^ 4)
        (by positivity : (0:ℝ) < (z ^ 2) ^ 2)]
      calc (1:ℝ) * (z ^ 2) ^ 2 = 1 * z ^ 4 := by ring
        _ ≤ (1 + z) ^ 4 * z ^ 4 := hkey
        _ = ((1 + z) ^ 2) ^ 2 * z ^ 4 := by ring
    have hdiff : gamEnergy α u z / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 * gamEnergy α u z := by
      calc gamEnergy α u z / z ^ 4 = (1 / z ^ 4) * gamEnergy α u z := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * gamEnergy α u z := mul_le_mul_of_nonneg_right hw4 hΦ
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hΦ (by positivity)),
      abs_of_nonneg (mul_nonneg (sq_nonneg _) hΦ)]
    exact hdiff

/-- AM–GM for the square root. -/
theorem sqrt_mul_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have h1 : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (mul_nonneg ha hb)
  have h2 : ((a + b) / 2) ^ 2 = (a + b) ^ 2 / 4 := by ring
  have hs : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  have ht : 0 ≤ (a + b) / 2 := by linarith
  nlinarith [h1, h2, sq_nonneg (a - b), hs, ht]

/-- `√(gamEnergy)/s` is locally integrable near `0`, by AM–GM applied to `gamEnergy/s⁴` and `s²`. -/
theorem integrableOn_sqrt_gamEnergy_div {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hMixO : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Iθ, (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * AslotGam.sgam α θ) Iz)
    {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun s => Real.sqrt (gamEnergy α u s) / s) (Set.Ioo 0 b) := by
  have h1 : MeasureTheory.IntegrableOn (fun s => gamEnergy α u s / s ^ 4) (Set.Ioo 0 b) :=
    integrableOn_gamEnergy_div_pow_four hMixO hb
  have h2 : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ 2) (Set.Ioo 0 b) :=
    (continuous_id.pow 2).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  have hdom : MeasureTheory.IntegrableOn
      (fun s => (gamEnergy α u s / s ^ 4 + s ^ 2) / 2) (Set.Ioo 0 b) := by
    refine MeasureTheory.Integrable.congr ((h1.add h2).const_mul (1/2)) ?_
    filter_upwards with s
    show (1/2 : ℝ) * (gamEnergy α u s / s ^ 4 + s ^ 2)
      = (gamEnergy α u s / s ^ 4 + s ^ 2) / 2
    ring
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · have hΦm : AEMeasurable (gamEnergy α u) (volume.restrict (Set.Ioo 0 b)) :=
      aemeasurable_gamEnergy_Ioo hMixO le_rfl hb
    have hsqrt : AEMeasurable (fun s => Real.sqrt (gamEnergy α u s))
        (volume.restrict (Set.Ioo 0 b)) :=
      (Real.continuous_sqrt.measurable).comp_aemeasurable hΦm
    have hinv : AEMeasurable (fun s : ℝ => s⁻¹) (volume.restrict (Set.Ioo 0 b)) := by
      refine ContinuousOn.aemeasurable ?_ measurableSet_Ioo
      exact continuousOn_id.inv₀ (fun z hz => ne_of_gt hz.1)
    refine ((hsqrt.mul hinv).aestronglyMeasurable).congr ?_
    filter_upwards with s
    simp only [Pi.mul_apply, div_eq_mul_inv]
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
    have hspos : 0 < s := hs.1
    have hΦ := gamEnergy_nonneg α u s
    have hkey : Real.sqrt (gamEnergy α u s) / s = Real.sqrt (gamEnergy α u s / s ^ 2) := by
      rw [Real.sqrt_div hΦ, Real.sqrt_sq (le_of_lt hspos)]
    have hsplit : gamEnergy α u s / s ^ 2 = (gamEnergy α u s / s ^ 4) * s ^ 2 := by
      field_simp
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hspos)),
      hkey, hsplit]
    exact sqrt_mul_le_add_div_two (div_nonneg hΦ (by positivity)) (sq_nonneg s)

/-- **Localized Lebesgue-differentiation lemma.**  If `∫_z^{z+t} F = 0` for a.e. `z ∈ A` and a.e.
`t > 0`, then `F = 0` a.e. on `A` (for `F` locally integrable). -/
theorem aeZeroOn_of_intervalIntegralZero {F : ℝ → ℝ} {A : Set ℝ}
    (hF : MeasureTheory.LocallyIntegrable F volume)
    (hint : ∀ᵐ z ∂(volume.restrict A),
      ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), (∫ x in z..(z + t), F x) = 0) :
    ∀ᵐ z ∂(volume.restrict A), F z = 0 := by
  have hLDT : ∀ᵐ z ∂volume, ∀ c, HasDerivAt (fun x => ∫ t in c..x, F t) (F z) z :=
    LocallyIntegrable.ae_hasDerivAt_integral hF
  filter_upwards [MeasureTheory.ae_restrict_of_ae hLDT, hint] with z hder hh
  set K' : ℝ → ℝ := fun x => ∫ t in z..x, F t with hK'
  have hderz : HasDerivAt K' (F z) z := by rw [hK']; exact hder z
  have hnull : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), t⁻¹ * (K' (z + t) - K' z) = 0 := by
    filter_upwards [hh] with t ht
    have hval : K' (z + t) - K' z = ∫ x in z..(z + t), F x := by
      rw [hK']
      simp [intervalIntegral.integral_same]
    rw [hval, ht, mul_zero]
  have hsetnull : volume {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} = 0 := by
    have h2 := MeasureTheory.ae_iff.mp hnull
    have h3 : (volume.restrict (Set.Ioi 0))
        {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} = 0 :=
      MeasureTheory.measure_mono_null (fun t ht => ht.2) h2
    rwa [MeasureTheory.Measure.restrict_eq_self volume (fun t ht => ht.1)] at h3
  have hseq : ∀ n : ℕ, ∃ t : ℝ, t ∈ Set.Ioo 0 (1 / ((n : ℝ) + 1)) ∧
      t⁻¹ * (K' (z + t) - K' z) = 0 := by
    intro n
    by_contra hcon
    push_neg at hcon
    have hsub : Set.Ioo 0 (1 / ((n : ℝ) + 1)) ⊆
        {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} :=
      fun t ht => ⟨ht.1, hcon t ht⟩
    have hle : volume (Set.Ioo 0 (1 / ((n : ℝ) + 1))) ≤
        volume {t : ℝ | 0 < t ∧ t⁻¹ * (K' (z + t) - K' z) ≠ 0} :=
      MeasureTheory.measure_mono hsub
    rw [hsetnull, le_zero_iff, Real.volume_Ioo] at hle
    have hle0 : (1 / ((n : ℝ) + 1)) ≤ 0 := by simpa using ENNReal.ofReal_eq_zero.mp hle
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose t ht using hseq
  have htend0 : Tendsto t atTop (nhds (0:ℝ)) := by
    have hdiv : Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
      (fun n => le_of_lt (ht n).1.1) (fun n => le_of_lt (ht n).1.2)
  have htend : Tendsto t atTop (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
    rw [nhdsWithin, tendsto_inf, tendsto_principal]
    exact ⟨htend0, Eventually.of_forall fun n => (ht n).1.1⟩
  have hcomp := hderz.tendsto_slope_zero_right.comp htend
  have hzero : Tendsto (fun n => (t n)⁻¹ * (K' (z + t n) - K' z)) atTop (nhds (0:ℝ)) := by
    have : (fun n => (t n)⁻¹ * (K' (z + t n) - K' z)) = fun _ => (0:ℝ) :=
      funext fun n => (ht n).2
    rw [this]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hcomp hzero

/-- **Cut-off local integrability.**  A function which vanishes below `ε > 0` and is integrable on
every compact subinterval of `(ε,∞)` is locally integrable. -/
theorem locallyIntegrable_indicator_Ioi {F : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ a b : ℝ, ε ≤ a → a < b → MeasureTheory.IntegrableOn F (Set.Ioo a b)) :
    MeasureTheory.LocallyIntegrable (Set.indicator (Set.Ioi ε) F) volume := by
  have hInt : ∀ a b : ℝ, a < b → MeasureTheory.IntegrableOn
      (Set.indicator (Set.Ioi ε) F) (Set.Ioo a b) := by
    intro a b hab
    rcases le_or_gt b ε with hb | hb
    · refine MeasureTheory.IntegrableOn.congr_fun
        (MeasureTheory.integrable_zero ℝ ℝ _) ?_ measurableSet_Ioo
      intro s hs
      have hmem : s ∉ Set.Ioi ε := not_lt.mpr (le_trans (le_of_lt hs.2) hb)
      exact (Set.indicator_of_notMem hmem F).symm
    · have hbase : MeasureTheory.IntegrableOn F (Set.Ioo (max a ε) b) := by
        rcases lt_or_ge (max a ε) b with hlt | hge
        · exact h (max a ε) b (le_max_right _ _) hlt
        · rw [show Set.Ioo (max a ε) b = ∅ from
            Set.eq_empty_iff_forall_notMem.mpr
              (fun s hs => absurd hs.1 (not_lt.mpr (le_trans (le_of_lt hs.2) hge)))]
          exact MeasureTheory.integrableOn_empty
      have h2 : MeasureTheory.IntegrableOn (Set.indicator (Set.Ioi ε) F)
          (Set.Ioo a b ∩ Set.Ioi ε) :=
        MeasureTheory.IntegrableOn.congr_fun
          (hbase.mono_set (fun s hs => ⟨max_lt hs.1.1 hs.2, hs.1.2⟩))
          (fun s hs => (Set.indicator_of_mem hs.2 F).symm)
          (measurableSet_Ioo.inter measurableSet_Ioi)
      have h3 : MeasureTheory.IntegrableOn (Set.indicator (Set.Ioi ε) F)
          (Set.Ioo a b \ Set.Ioi ε) :=
        MeasureTheory.IntegrableOn.congr_fun
          (MeasureTheory.integrable_zero ℝ ℝ _)
          (fun s hs => (Set.indicator_of_notMem hs.2 F).symm)
          (measurableSet_Ioo.diff measurableSet_Ioi)
      refine (h2.union h3).mono_set ?_
      intro s hs
      by_cases hmem : ε < s
      · exact Set.mem_union_left _ ⟨hs, hmem⟩
      · exact Set.mem_union_right _ ⟨hs, hmem⟩
  intro x
  rcases le_or_gt x (ε / 2) with hx | hx
  · exact ⟨Set.Ioo (x - 1) (ε / 2 + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩, hInt _ _ (by linarith)⟩
  · exact ⟨Set.Ioo (ε / 2) (x + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩, hInt _ _ (by linarith)⟩

/-! ## 2. Dominated convergence for the `θ`-slices of `∂_z u`, with a.e. hypotheses -/

/-- **Dominated convergence for the `θ`-slices of `∂_zu`**, in the `z`-integrated form, with the
convergence and the pointwise domination required only almost everywhere in `z`. -/
theorem tendsto_setIntegral_pz_ae {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {l : Filter ℝ} [l.IsCountablyGenerated] {c g : ℝ → ℝ} {z h : ℝ}
    (hz : 0 < z) (hh : 0 < h)
    (hθl : ∀ᶠ θ in l, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hlim : ∀ᵐ s ∂(volume.restrict (Set.Ioo z (z + h))),
      Filter.Tendsto (fun θ => Work.Spaces.pz u s θ) l (nhds (c s)))
    (hbound : ∀ᶠ θ in l, ∀ᵐ s ∂(volume.restrict (Set.Ioo z (z + h))),
      ‖Work.Spaces.pz u s θ‖ ≤ g s)
    (hgi : MeasureTheory.IntegrableOn g (Set.Ioo z (z + h))) :
    Filter.Tendsto (fun θ => ∫ s in Set.Ioo z (z + h), Work.Spaces.pz u s θ) l
      (nhds (∫ s in Set.Ioo z (z + h), c s)) := by
  have hmain : Filter.Tendsto
      (fun θ => ∫ s, Work.Spaces.pz u s θ ∂(volume.restrict (Set.Ioo z (z + h)))) l
      (nhds (∫ s, c s ∂(volume.restrict (Set.Ioo z (z + h))))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hgi ?_
    · filter_upwards [hθl] with θ hθ
      have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun s : ℝ => Work.Spaces.pz u s θ) (Set.Ioo z (z + h)) :=
        (Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
          (t := Set.Ioo 0 (Real.pi / 2)) (hS.pz) hθ).mono
            (fun s hs => lt_trans hz hs.1)
      exact (hslice.continuousOn.aemeasurable measurableSet_Ioo).aestronglyMeasurable
    · filter_upwards [hbound] with θ hθ
      exact hθ
    · exact hlim
  exact hmain

/-! ## 3. The two endpoint traces as `limsup`-defined functions -/

/-- The left trace of the slice `θ ↦ ∂_z u(·,θ)` at `0⁺`, taken along the diagonal sequence
`θ_n = 1/(n+1)`; it is `a.e.`-measurable by construction and agrees with the honest limit
whenever the latter exists (see `dzTrace0_eq_of_tendsto`). -/
def dzTrace0 (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => limsup (fun n : ℕ => Work.Spaces.pz u z (1 / ((n : ℝ) + 1))) atTop

/-- The right trace of the slice `θ ↦ ∂_z u(·,θ)` at `(π/2)⁻`. -/
def dzTrace1 (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => limsup (fun n : ℕ => Work.Spaces.pz u z (Real.pi / 2 - 1 / ((n : ℝ) + 1))) atTop

/-- The diagonal sequence `θ_n = 1/(n+1)` lies in `(0,π/2)` and tends to `0` within `(0,∞)`. -/
theorem tendsto_theta0 : Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 1)) atTop
    (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
  rw [nhdsWithin, tendsto_inf, tendsto_principal]
  refine ⟨?_, ?_⟩
  · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · filter_upwards with n
    exact one_div_pos.mpr (by positivity : (0:ℝ) < (n : ℝ) + 1)

/-- The diagonal sequence `θ_n = π/2 - 1/(n+1)` tends to `π/2` within `(0,π/2)`. -/
theorem tendsto_theta1 : Tendsto (fun n : ℕ => Real.pi / 2 - 1 / ((n : ℝ) + 1)) atTop
    (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
  rw [nhdsWithin, tendsto_inf, tendsto_principal]
  refine ⟨?_, ?_⟩
  · have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hc : Tendsto (fun _ : ℕ => Real.pi / 2) atTop (nhds (Real.pi / 2)) := tendsto_const_nhds
    have h1 : Tendsto (fun n : ℕ => Real.pi / 2 - (1:ℝ) / ((n : ℝ) + 1)) atTop
        (nhds (Real.pi / 2 - 0)) := hc.sub h0
    simpa using h1
  · filter_upwards with n
    have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact sub_lt_self _ this

theorem theta0_mem {n : ℕ} : (1:ℝ) / ((n : ℝ) + 1) ∈ Set.Ioo 0 (Real.pi / 2) := by
  constructor
  · exact div_pos one_pos (by positivity)
  · have h1 : (1:ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; norm_num
    have h2 : (1:ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    linarith

theorem theta1_mem {n : ℕ} : Real.pi / 2 - 1 / ((n : ℝ) + 1) ∈ Set.Ioo 0 (Real.pi / 2) := by
  constructor
  · have h : (1:ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; norm_num
    have h2 : (1:ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    linarith
  · exact sub_lt_self _ (by positivity)

/-- The `z`-slice of `∂_zu` at a fixed interior angle is a.e. strongly measurable. -/
theorem aeStronglyMeasurable_zslice {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    AEStronglyMeasurable (fun z => Work.Spaces.pz u z θ) (volume.restrict (Set.Ioi 0)) := by
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.Spaces.pz u z θ)
      (Set.Ioi 0) :=
    Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
      (t := Set.Ioo 0 (Real.pi / 2)) (hS.pz) hθ
  exact (hslice.continuousOn.aemeasurable measurableSet_Ioi).aestronglyMeasurable

theorem aemeasurable_dzTrace0 {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    AEMeasurable (dzTrace0 u) (volume.restrict (Set.Ioi 0)) := by
  refine AEMeasurable.limsup (fun n => ?_)
  exact (aeStronglyMeasurable_zslice hS theta0_mem).aemeasurable

theorem aemeasurable_dzTrace1 {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    AEMeasurable (dzTrace1 u) (volume.restrict (Set.Ioi 0)) := by
  refine AEMeasurable.limsup (fun n => ?_)
  exact (aeStronglyMeasurable_zslice hS theta1_mem).aemeasurable

theorem dzTrace0_eq_of_tendsto {u : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {z : ℝ}
    (h : Tendsto (fun θ => Work.Spaces.pz u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (c z))) :
    dzTrace0 u z = c z := by
  exact (h.comp tendsto_theta0).limsup_eq

theorem dzTrace1_eq_of_tendsto {u : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {z : ℝ}
    (h : Tendsto (fun θ => Work.Spaces.pz u z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c z))) :
    dzTrace1 u z = c z := by
  exact (h.comp tendsto_theta1).limsup_eq

/-! ## 3. The main theorem -/

/-- **The `θ`-trace of `z ∂_z u` vanishes at both endpoints, a.e. in `z`: the `γ`-weighted form**
(the analogue of the *proved* `Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk`, in file
`Submission/Work/FTS/EllipticEst/TT/AeI1/aeDzTraceHk.lean`, with the `η`-weighted mixed honesty
`HkMem α 0 (∂_θ(z∂_zu))` replaced by the *`γ`-weighted* honesties `hMixS`/`hMixO`).

Both hypotheses are available in the intended application: for `u = z²∂_z²Ψ` of a level-2 weak
datum the *per-slice* honesty `hMixS` (indeed for every `z ∈ Iz`) comes from the `(1,1)`-summand of
`HkMem α 2 (z²∂_z²Ψ)`, and the *outer* honesty `hMixO` is produced by
`Work.FTS.EllipticEst.TT.gammaHonesty`; the datum is in `AeData` by
`Work.FTS.EllipticEst.H2W.AeDataAof`.

Route: port the proof of `aeDzTraceHk`, replacing `Core.sliceBoundaryLimit` (`η`-weight) by the
`γ`-weight rate lemma `aslotTwoShift_sliceBoundaryLimit_gam`; the slice is
`f z := θ ↦ z ∂_zu (z,θ)` with `deriv (f z) θ = Dz (pth u) z θ` by Clairaut.  The only `η`-specific
inputs of that proof are `thEtaFacts`/`thEtaInvIntegralBounds` (positivity, `≤ 1`, and the
reciprocal mass, exponent `γ-1 > 0`) and `derivIntegrableOfEnergy`; the traces of `u` itself
(`H2W.AeLeftClean.sliceLeftTendstoClean`, `H2W.AeProof.AeSliceRightTendsto`) and the
Lebesgue-differentiation step are weight-independent.  All invocations that the original does for
every `z` are localized here to the a.e. set of `hMixS`, which is why the conclusion is `∀ᵐ z`. -/
theorem aslotTwoShift_aeDzTrace_gam (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hMixS : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ)
    (hMixO : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  classical
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hα1 : α ≤ 1 := by linarith [h.hα4]
  have hgam1nn : (0 : ℝ) ≤ Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]; linarith [h.hα]
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4mem : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hpi4, by linarith [Real.pi_pos]⟩
  -- ## the a.e. good set: per-slice `hMixS`-honesty and the left trace of `u`
  have hBadS : volume ({z : ℝ | ¬ MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * AslotGam.sgam α θ)
      Work.Spaces.Iθ} ∩ Set.Ioi 0) = 0 := by
    have h1 := MeasureTheory.ae_iff.mp hMixS
    exact (MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi).mp h1
  have hBadL : volume ({z : ℝ | ¬ Filter.Tendsto (fun θ => u z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)} ∩ Set.Ioi 0) = 0 := by
    have h2 := Work.FTS.EllipticEst.H2W.AeLeftClean.sliceLeftTendstoClean α u G h
    have h1 := MeasureTheory.ae_iff.mp h2
    exact (MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi).mp h1
  obtain ⟨M₁, hM₁sub, hM₁meas, hM₁null⟩ :=
    MeasureTheory.exists_measurable_superset_of_null hBadS
  obtain ⟨M₂, hM₂sub, hM₂meas, hM₂null⟩ :=
    MeasureTheory.exists_measurable_superset_of_null hBadL
  set N : Set ℝ := M₁ ∪ M₂ with hNdef
  have hNmeas : MeasurableSet N := by rw [hNdef]; exact hM₁meas.union hM₂meas
  have hNnull : volume N = 0 := by
    rw [hNdef]; exact MeasureTheory.measure_union_null hM₁null hM₂null
  have hNae : ∀ᵐ z ∂(volume : MeasureTheory.Measure ℝ), z ∉ N := by
    rw [MeasureTheory.ae_iff]
    simpa using hNnull
  have hGoodSlice : ∀ z : ℝ, z ∉ N → 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * AslotGam.sgam α θ)
      Work.Spaces.Iθ := by
    intro z hzN hz
    by_contra hcon
    exact hzN (hNdef.symm ▸ Set.mem_union_left _ (hM₁sub ⟨hcon, hz⟩))
  have hGoodLeft : ∀ z : ℝ, z ∉ N → 0 < z →
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    intro z hzN hz
    by_contra hcon
    exact hzN (hNdef.symm ▸ Set.mem_union_right _ (hM₂sub ⟨hcon, hz⟩))
  -- ## the `γ`-weighted endpoint rate lemma
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.Cores.sliceRateSigA α h.hα hα1
  have hsliceC1 : ∀ z : ℝ, 0 < z → ContDiffOn ℝ 1
      (fun θ => Work.Spaces.Dz u z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro z hz
    refine (hS.Dz.curry_θ hz).of_le ?_
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  have hslice_int : ∀ z : ℝ, z ∉ N → 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Work.Spaces.Dz u z θ') θ) ^ 2 * AslotGam.sgam α θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro z hzN hz
    refine ((hGoodSlice z hzN hz).mono_set Set.Ioo_subset_Icc_self).congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    rw [deriv_Dz_slice hS hz hθ]
  have hleft : ∀ z : ℝ, z ∉ N → 0 < z → ∃ c : ℝ,
      Filter.Tendsto (fun θ => Work.Spaces.Dz u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds c) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (Work.Spaces.Dz u z θ - c) ^ 2
        ≤ K * θ ^ (Work.Spaces.gam α - 1) * gamEnergy α u z) := by
    intro z hzN hz
    obtain ⟨c, hlim, hbd⟩ := (hK (fun θ => Work.Spaces.Dz u z θ) (hsliceC1 z hz)
      (hslice_int z hzN hz)).1
    refine ⟨c, hlim, fun θ hθ => ?_⟩
    have hA : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * AslotGam.sgam α θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hGoodSlice z hzN hz).mono_set Set.Ioo_subset_Icc_self
    have hEq1 : (∫ t in Set.Ioo 0 θ, (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2
          * AslotGam.sgam α t)
        = ∫ t in Set.Ioo 0 θ, (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
          * AslotGam.sgam α t :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun t ht => by rw [deriv_Dz_slice hS hz ⟨ht.1, lt_trans ht.2 hθ.2⟩])
    have hEq2 : (∫ t in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
          * AslotGam.sgam α t) = gamEnergy α u z :=
      (gamEnergy_eq_Ioo α u z).symm
    have hmono : (∫ t in Set.Ioo 0 θ, (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2
        * AslotGam.sgam α t) ≤ gamEnergy α u z := by
      rw [hEq1, ← hEq2]
      exact MeasureTheory.setIntegral_mono_set hA
        (by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
          exact mul_nonneg (sq_nonneg _)
            (AslotGam.sgam_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
        (by
          filter_upwards with t ht
          exact ⟨ht.1, lt_trans ht.2 hθ.2⟩)
    exact le_trans (hbd θ hθ)
      (mul_le_mul_of_nonneg_left hmono (mul_nonneg hKpos.le (Real.rpow_nonneg hθ.1.le _)))
  have hright : ∀ z : ℝ, z ∉ N → 0 < z → ∃ c : ℝ,
      Filter.Tendsto (fun θ => Work.Spaces.Dz u z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (Work.Spaces.Dz u z θ - c) ^ 2
        ≤ K * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) * gamEnergy α u z) := by
    intro z hzN hz
    obtain ⟨c, hlim, hbd⟩ := (hK (fun θ => Work.Spaces.Dz u z θ) (hsliceC1 z hz)
      (hslice_int z hzN hz)).2
    refine ⟨c, hlim, fun θ hθ => ?_⟩
    have hA : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * AslotGam.sgam α θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hGoodSlice z hzN hz).mono_set Set.Ioo_subset_Icc_self
    have hEq1 : (∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2 * AslotGam.sgam α t)
        = ∫ t in Set.Ioo θ (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
          * AslotGam.sgam α t :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun t ht => by rw [deriv_Dz_slice hS hz ⟨lt_trans hθ.1 ht.1, ht.2⟩])
    have hEq2 : (∫ t in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.Dz (Work.Spaces.pth u) z t) ^ 2
          * AslotGam.sgam α t) = gamEnergy α u z :=
      (gamEnergy_eq_Ioo α u z).symm
    have hmono : (∫ t in Set.Ioo θ (Real.pi / 2),
        (deriv (fun θ' => Work.Spaces.Dz u z θ') t) ^ 2 * AslotGam.sgam α t)
        ≤ gamEnergy α u z := by
      rw [hEq1, ← hEq2]
      exact MeasureTheory.setIntegral_mono_set hA
        (by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
          exact mul_nonneg (sq_nonneg _)
            (AslotGam.sgam_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
        (by
          filter_upwards with t ht
          exact ⟨lt_trans hθ.1 ht.1, ht.2⟩)
    exact le_trans (hbd θ hθ)
      (mul_le_mul_of_nonneg_left hmono
        (mul_nonneg hKpos.le (Real.rpow_nonneg (by linarith [hθ.2]) _)))
  -- ## the two endpoint parameters, as honest functions on the good set
  let c0f : ℝ → ℝ := fun z =>
    if hz : z ∉ N ∧ 0 < z then Classical.choose (hleft z hz.1 hz.2) else 0
  have hc0f : ∀ z : ℝ, z ∉ N → 0 < z →
      Filter.Tendsto (fun θ => Work.Spaces.Dz u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (c0f z)) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (Work.Spaces.Dz u z θ - c0f z) ^ 2
        ≤ K * θ ^ (Work.Spaces.gam α - 1) * gamEnergy α u z) := by
    intro z hzN hz
    have hif : c0f z = Classical.choose (hleft z hzN hz) := by
      simp only [c0f]
      rw [dif_pos ⟨hzN, hz⟩]
    rw [hif]
    exact Classical.choose_spec (hleft z hzN hz)
  let c1f : ℝ → ℝ := fun z =>
    if hz : z ∉ N ∧ 0 < z then Classical.choose (hright z hz.1 hz.2) else 0
  have hc1f : ∀ z : ℝ, z ∉ N → 0 < z →
      Filter.Tendsto (fun θ => Work.Spaces.Dz u z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c1f z)) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (Work.Spaces.Dz u z θ - c1f z) ^ 2
        ≤ K * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) * gamEnergy α u z) := by
    intro z hzN hz
    have hif : c1f z = Classical.choose (hright z hzN hz) := by
      simp only [c1f]
      rw [dif_pos ⟨hzN, hz⟩]
    rw [hif]
    exact Classical.choose_spec (hright z hzN hz)
  have hlim0 : ∀ z : ℝ, z ∉ N → 0 < z → Filter.Tendsto (fun θ => Work.Spaces.pz u z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c0f z / z)) := by
    intro z hzN hz
    have h1 : Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c0f z)) := by
      simpa only [Work.Spaces.Dz] using (hc0f z hzN hz).1
    have h3 : (fun θ => z * Work.Spaces.pz u z θ / z) = fun θ => Work.Spaces.pz u z θ := by
      funext θ
      exact mul_div_cancel_left₀ _ (ne_of_gt hz)
    rw [← h3]
    exact h1.div_const z
  have hlim1 : ∀ z : ℝ, z ∉ N → 0 < z → Filter.Tendsto (fun θ => Work.Spaces.pz u z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c1f z / z)) := by
    intro z hzN hz
    have h1 : Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c1f z)) := by
      simpa only [Work.Spaces.Dz] using (hc1f z hzN hz).1
    have h3 : (fun θ => z * Work.Spaces.pz u z θ / z) = fun θ => Work.Spaces.pz u z θ := by
      funext θ
      exact mul_div_cancel_left₀ _ (ne_of_gt hz)
    rw [← h3]
    exact h1.div_const z
  have htr0 : ∀ z : ℝ, z ∉ N → 0 < z → dzTrace0 u z = c0f z / z := by
    intro z hzN hz
    exact dzTrace0_eq_of_tendsto (hlim0 z hzN hz)
  have htr1 : ∀ z : ℝ, z ∉ N → 0 < z → dzTrace1 u z = c1f z / z := by
    intro z hzN hz
    exact dzTrace1_eq_of_tendsto (hlim1 z hzN hz)
  -- ## the pointwise bounds
  have hc0bd : ∀ z : ℝ, z ∉ N → 0 < z →
      |c0f z| ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
        + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
          * Real.sqrt (gamEnergy α u z) := by
    intro z hzN hz
    have hb := (hc0f z hzN hz).2 (Real.pi / 4) hpi4mem
    have h1 : |c0f z - Work.Spaces.Dz u z (Real.pi / 4)|
        ≤ Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
          * Real.sqrt (gamEnergy α u z) := by
      rw [← Real.sqrt_sq_eq_abs]
      rw [show (c0f z - Work.Spaces.Dz u z (Real.pi / 4)) ^ 2
          = (Work.Spaces.Dz u z (Real.pi / 4) - c0f z) ^ 2 from by ring]
      calc Real.sqrt ((Work.Spaces.Dz u z (Real.pi / 4) - c0f z) ^ 2)
          ≤ Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1) * gamEnergy α u z) :=
            Real.sqrt_le_sqrt hb
        _ = Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
              * Real.sqrt (gamEnergy α u z) :=
            Real.sqrt_mul (mul_nonneg hKpos.le (Real.rpow_nonneg hpi4.le _)) _
    have h2 : |c0f z| = |Work.Spaces.Dz u z (Real.pi / 4)
        - (Work.Spaces.Dz u z (Real.pi / 4) - c0f z)| := by
      congr 1
      ring
    rw [h2]
    calc |Work.Spaces.Dz u z (Real.pi / 4) - (Work.Spaces.Dz u z (Real.pi / 4) - c0f z)|
        ≤ |Work.Spaces.Dz u z (Real.pi / 4)| + |Work.Spaces.Dz u z (Real.pi / 4) - c0f z| :=
          abs_sub _ _
      _ = |Work.Spaces.Dz u z (Real.pi / 4)| + |c0f z - Work.Spaces.Dz u z (Real.pi / 4)| := by
          rw [abs_sub_comm]
      _ ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
            + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
              * Real.sqrt (gamEnergy α u z) := by
          linarith [h1]
  have hc1bd : ∀ z : ℝ, z ∉ N → 0 < z →
      |c1f z| ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
        + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
          * Real.sqrt (gamEnergy α u z) := by
    intro z hzN hz
    have hb := (hc1f z hzN hz).2 (Real.pi / 4) hpi4mem
    have hb' : (Work.Spaces.Dz u z (Real.pi / 4) - c1f z) ^ 2
        ≤ K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1) * gamEnergy α u z := by
      have hpi : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
      simpa only [hpi] using hb
    have h1 : |c1f z - Work.Spaces.Dz u z (Real.pi / 4)|
        ≤ Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
          * Real.sqrt (gamEnergy α u z) := by
      rw [← Real.sqrt_sq_eq_abs]
      rw [show (c1f z - Work.Spaces.Dz u z (Real.pi / 4)) ^ 2
          = (Work.Spaces.Dz u z (Real.pi / 4) - c1f z) ^ 2 from by ring]
      calc Real.sqrt ((Work.Spaces.Dz u z (Real.pi / 4) - c1f z) ^ 2)
          ≤ Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1) * gamEnergy α u z) :=
            Real.sqrt_le_sqrt hb'
        _ = Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
              * Real.sqrt (gamEnergy α u z) :=
            Real.sqrt_mul (mul_nonneg hKpos.le (Real.rpow_nonneg hpi4.le _)) _
    have h2 : |c1f z| = |Work.Spaces.Dz u z (Real.pi / 4)
        - (Work.Spaces.Dz u z (Real.pi / 4) - c1f z)| := by
      congr 1
      ring
    rw [h2]
    calc |Work.Spaces.Dz u z (Real.pi / 4) - (Work.Spaces.Dz u z (Real.pi / 4) - c1f z)|
        ≤ |Work.Spaces.Dz u z (Real.pi / 4)| + |Work.Spaces.Dz u z (Real.pi / 4) - c1f z| :=
          abs_sub _ _
      _ = |Work.Spaces.Dz u z (Real.pi / 4)| + |c1f z - Work.Spaces.Dz u z (Real.pi / 4)| := by
          rw [abs_sub_comm]
      _ ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
            + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
              * Real.sqrt (gamEnergy α u z) := by
          linarith [h1]
  have hslicebd : ∀ z θ : ℝ, z ∉ N → 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |Work.Spaces.Dz u z θ| ≤ |Work.Spaces.Dz u z (Real.pi / 4)|
        + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
            + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
          * Real.sqrt (gamEnergy α u z) := by
    intro z θ hzN hz hθ
    have hb := (hc0f z hzN hz).2 θ hθ
    have h1 : |Work.Spaces.Dz u z θ - c0f z|
        ≤ Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
          * Real.sqrt (gamEnergy α u z) := by
      rw [← Real.sqrt_sq_eq_abs]
      calc Real.sqrt ((Work.Spaces.Dz u z θ - c0f z) ^ 2)
          ≤ Real.sqrt (K * θ ^ (Work.Spaces.gam α - 1) * gamEnergy α u z) :=
            Real.sqrt_le_sqrt hb
        _ = Real.sqrt (K * θ ^ (Work.Spaces.gam α - 1)) * Real.sqrt (gamEnergy α u z) :=
            Real.sqrt_mul (mul_nonneg hKpos.le (Real.rpow_nonneg hθ.1.le _)) _
        _ ≤ Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
              * Real.sqrt (gamEnergy α u z) := by
            refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow hθ.1.le hθ.2.le hgam1nn) hKpos.le
    have h2 : |Work.Spaces.Dz u z θ| ≤ |Work.Spaces.Dz u z θ - c0f z| + |c0f z| := by
      have h3 : |Work.Spaces.Dz u z θ| = |(Work.Spaces.Dz u z θ - c0f z) + c0f z| := by
        congr 1
        ring
      rw [h3]
      exact abs_add_le _ _
    have h4 := hc0bd z hzN hz
    calc |Work.Spaces.Dz u z θ|
        ≤ |Work.Spaces.Dz u z θ - c0f z| + |c0f z| := h2
      _ ≤ Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
            * Real.sqrt (gamEnergy α u z)
            + (|Work.Spaces.Dz u z (Real.pi / 4)|
              + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
                * Real.sqrt (gamEnergy α u z)) := by linarith [h1, h4]
      _ = |Work.Spaces.Dz u z (Real.pi / 4)|
            + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
              + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
              * Real.sqrt (gamEnergy α u z) := by ring
  -- ## the `z`-FTC
  have hftc : ∀ z t θ : ℝ, 0 < z → 0 < t → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ) = u (z + t) θ - u z θ := by
    intro z t θ hz ht hθ
    have hderiv : ∀ x ∈ Set.uIcc z (z + t), HasDerivAt (fun s : ℝ => u s θ)
        (Work.Spaces.pz u x θ) x := by
      intro x hx
      have hx' := Set.mem_uIcc.mp hx
      rcases hx' with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hS.hasDerivAt_slice hθ (lt_of_lt_of_le hz h1)
      · exact hS.hasDerivAt_slice hθ (lt_of_lt_of_le (by linarith : (0:ℝ) < z + t) h1)
    have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s θ) (Set.uIcc z (z + t)) :=
      ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
        (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hθ).continuousOn).mono
          (fun s hs => by
            have hs' := Set.mem_uIcc.mp hs
            rcases hs' with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact lt_of_lt_of_le hz h1
            · exact lt_of_lt_of_le (by linarith : (0:ℝ) < z + t) h1)
    have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [← hmain, intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  -- ## the two limit filters
  have hθl0 : ∀ᶠ θ in nhdsWithin (0:ℝ) (Set.Ioi 0), θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := by
    have h2 : Set.Ioo (-1:ℝ) (Real.pi / 2) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      Filter.mem_inf_of_left
        (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0)
          (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2))
    refine Filter.mem_of_superset
      (Filter.inter_mem
        (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0)) h2) ?_
    intro x hx
    exact ⟨hx.1, hx.2.2⟩
  have hθl1 : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := by
    have h2 : Set.Ioi (0:ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
      Filter.mem_inf_of_left
        (Ioi_mem_nhds (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2))
    refine Filter.mem_of_superset
      (Filter.inter_mem h2
        (self_mem_nhdsWithin : Set.Iio (Real.pi / 2) ∈
          nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))) ?_
    intro x hx
    exact ⟨hx.1, hx.2⟩
  -- ## the a.e. vanishing of the interval integrals: left endpoint
  have hdct0 : ∀ z t : ℝ, 0 < z → 0 < t → z ∉ N → z + t ∉ N →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x) = 0 := by
    intro z t hz ht hzN hztN
    have htrz : Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      hGoodLeft z hzN hz
    have htrzt : Filter.Tendsto (fun θ => u (z + t) θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      hGoodLeft (z + t) hztN (by linarith)
    have hGint : MeasureTheory.IntegrableOn
        (fun s => |Work.Spaces.pz u s (Real.pi / 4)|
          + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
              + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
            * (Real.sqrt (gamEnergy α u s) / s)) (Set.Ioo z (z + t)) := by
      have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
          (Set.Ioo z (z + t)) := by
        have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
            (Set.Icc z (z + t)) :=
          ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
            (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
              (fun s hs => lt_of_lt_of_le hz (Set.mem_Icc.mp hs).1)
        exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
      have h2 : MeasureTheory.IntegrableOn (fun s => Real.sqrt (gamEnergy α u s) / s)
          (Set.Ioo z (z + t)) :=
        (integrableOn_sqrt_gamEnergy_div hMixO (by linarith : 0 < z + t)).mono_set
          (fun s hs => ⟨lt_trans hz hs.1, hs.2⟩)
      have h3 : MeasureTheory.IntegrableOn
          (fun s => (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
              + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
            * (Real.sqrt (gamEnergy α u s) / s)) (Set.Ioo z (z + t)) :=
        h2.const_mul _
      exact h1.add h3
    have hGoodae : ∀ᵐ s ∂(volume.restrict (Set.Ioo z (z + t))), s ∉ N ∧ 0 < s := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hNae] with s hsN hsIoo
      exact ⟨hsN, lt_trans hz hsIoo.1⟩
    have hlim : ∀ᵐ s ∂(volume.restrict (Set.Ioo z (z + t))),
        Filter.Tendsto (fun θ => Work.Spaces.pz u s θ) (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhds (dzTrace0 u s)) := by
      filter_upwards [hGoodae] with s hs
      rw [htr0 s hs.1 hs.2]
      exact hlim0 s hs.1 hs.2
    have hbound : ∀ᶠ θ in nhdsWithin (0:ℝ) (Set.Ioi 0),
        ∀ᵐ s ∂(volume.restrict (Set.Ioo z (z + t))),
          ‖Work.Spaces.pz u s θ‖ ≤ |Work.Spaces.pz u s (Real.pi / 4)|
            + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
                + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
              * (Real.sqrt (gamEnergy α u s) / s) := by
      filter_upwards [hθl0] with θ hθ
      filter_upwards [hGoodae] with s hs
      have hs0 : 0 < s := hs.2
      have hb := hslicebd s θ hs.1 hs0 hθ
      have hpz : |Work.Spaces.pz u s θ| = |Work.Spaces.Dz u s θ| / s := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
          = |Work.Spaces.pz u s (Real.pi / 4)| := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      rw [Real.norm_eq_abs, hpz]
      calc |Work.Spaces.Dz u s θ| / s
          ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
                + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
                * Real.sqrt (gamEnergy α u s)) / s :=
            div_le_div_of_nonneg_right hb (le_of_lt hs0)
        _ = |Work.Spaces.pz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
                + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
                * (Real.sqrt (gamEnergy α u s) / s) := by
            rw [add_div, hDz, mul_div_assoc]
    have hDCT := tendsto_setIntegral_pz_ae hS (l := nhdsWithin (0:ℝ) (Set.Ioi 0))
      (c := dzTrace0 u)
      (g := fun s => |Work.Spaces.pz u s (Real.pi / 4)|
        + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
            + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
          * (Real.sqrt (gamEnergy α u s) / s)) hz ht hθl0 hlim hbound hGint
    have heq : (fun θ => u (z + t) θ - u z θ)
        =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
        (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ) := by
      filter_upwards [hθl0] with θ hθ
      exact (hftc z t θ hz ht hθ).symm
    have htr : Filter.Tendsto (fun θ => u (z + t) θ - u z θ)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using htrzt.sub htrz
    have htr' : Filter.Tendsto (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      Filter.Tendsto.congr' heq htr
    have huniq := tendsto_nhds_unique hDCT htr'
    have h2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x)
        = ∫ x in Set.Ioo z (z + t), dzTrace0 u x :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun x hx => Set.indicator_of_mem (lt_trans hz hx.1) _)
    rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
      MeasureTheory.integral_Ioc_eq_integral_Ioo, h2]
    exact huniq
  -- ## the a.e. vanishing of the interval integrals: right endpoint
  have hdct1 : ∀ z t : ℝ, 0 < z → 0 < t →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x) = 0 := by
    intro z t hz ht
    have htrz : Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G h z hz).1
    have htrzt : Filter.Tendsto (fun θ => u (z + t) θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G h (z + t)
        (by linarith)).1
    have hGint : MeasureTheory.IntegrableOn
        (fun s => |Work.Spaces.pz u s (Real.pi / 4)|
          + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
              + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
            * (Real.sqrt (gamEnergy α u s) / s)) (Set.Ioo z (z + t)) := by
      have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
          (Set.Ioo z (z + t)) := by
        have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
            (Set.Icc z (z + t)) :=
          ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
            (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
              (fun s hs => lt_of_lt_of_le hz (Set.mem_Icc.mp hs).1)
        exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
      have h2 : MeasureTheory.IntegrableOn (fun s => Real.sqrt (gamEnergy α u s) / s)
          (Set.Ioo z (z + t)) :=
        (integrableOn_sqrt_gamEnergy_div hMixO (by linarith : 0 < z + t)).mono_set
          (fun s hs => ⟨lt_trans hz hs.1, hs.2⟩)
      have h3 : MeasureTheory.IntegrableOn
          (fun s => (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
              + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
            * (Real.sqrt (gamEnergy α u s) / s)) (Set.Ioo z (z + t)) :=
        h2.const_mul _
      exact h1.add h3
    have hGoodae : ∀ᵐ s ∂(volume.restrict (Set.Ioo z (z + t))), s ∉ N ∧ 0 < s := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hNae] with s hsN hsIoo
      exact ⟨hsN, lt_trans hz hsIoo.1⟩
    have hlim : ∀ᵐ s ∂(volume.restrict (Set.Ioo z (z + t))),
        Filter.Tendsto (fun θ => Work.Spaces.pz u s θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (dzTrace1 u s)) := by
      filter_upwards [hGoodae] with s hs
      rw [htr1 s hs.1 hs.2]
      exact hlim1 s hs.1 hs.2
    have hbound : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        ∀ᵐ s ∂(volume.restrict (Set.Ioo z (z + t))),
          ‖Work.Spaces.pz u s θ‖ ≤ |Work.Spaces.pz u s (Real.pi / 4)|
            + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
                + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
              * (Real.sqrt (gamEnergy α u s) / s) := by
      filter_upwards [hθl1] with θ hθ
      filter_upwards [hGoodae] with s hs
      have hs0 : 0 < s := hs.2
      have hb := hslicebd s θ hs.1 hs0 hθ
      have hpz : |Work.Spaces.pz u s θ| = |Work.Spaces.Dz u s θ| / s := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
          = |Work.Spaces.pz u s (Real.pi / 4)| := by
        rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
      rw [Real.norm_eq_abs, hpz]
      calc |Work.Spaces.Dz u s θ| / s
          ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
                + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
                * Real.sqrt (gamEnergy α u s)) / s :=
            div_le_div_of_nonneg_right hb (le_of_lt hs0)
        _ = |Work.Spaces.pz u s (Real.pi / 4)|
              + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
                + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
                * (Real.sqrt (gamEnergy α u s) / s) := by
            rw [add_div, hDz, mul_div_assoc]
    have hDCT := tendsto_setIntegral_pz_ae hS
      (l := nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (c := dzTrace1 u)
      (g := fun s => |Work.Spaces.pz u s (Real.pi / 4)|
        + (Real.sqrt (K * (Real.pi / 2) ^ (Work.Spaces.gam α - 1))
            + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1)))
          * (Real.sqrt (gamEnergy α u s) / s)) hz ht hθl1 hlim hbound hGint
    have heq : (fun θ => u (z + t) θ - u z θ)
        =ᶠ[nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))]
        (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ) := by
      filter_upwards [hθl1] with θ hθ
      exact (hftc z t θ hz ht hθ).symm
    have htr : Filter.Tendsto (fun θ => u (z + t) θ - u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa using htrzt.sub htrz
    have htr' : Filter.Tendsto (fun θ => ∫ s in Set.Ioo z (z + t), Work.Spaces.pz u s θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      Filter.Tendsto.congr' heq htr
    have huniq := tendsto_nhds_unique hDCT htr'
    have h2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x)
        = ∫ x in Set.Ioo z (z + t), dzTrace1 u x :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun x hx => Set.indicator_of_mem (lt_trans hz hx.1) _)
    rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
      MeasureTheory.integral_Ioc_eq_integral_Ioo, h2]
    exact huniq
  -- ## the pointwise a.e. bounds on the trace functions
  have htrbd : ∀ s : ℝ, s ∉ N → 0 < s → |dzTrace0 u s| ≤ |Work.Spaces.pz u s (Real.pi / 4)|
      + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
        * (Real.sqrt (gamEnergy α u s) / s) := by
    intro s hsN hs
    have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
        = |Work.Spaces.pz u s (Real.pi / 4)| := by
      rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs, mul_div_cancel_left₀ _ (ne_of_gt hs)]
    rw [htr0 s hsN hs, abs_div, abs_of_pos hs]
    calc |c0f s| / s ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
            * Real.sqrt (gamEnergy α u s)) / s :=
        div_le_div_of_nonneg_right (hc0bd s hsN hs) (le_of_lt hs)
      _ = |Work.Spaces.pz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
            * (Real.sqrt (gamEnergy α u s) / s) := by
        rw [add_div, hDz, mul_div_assoc]
  have htr1bd : ∀ s : ℝ, s ∉ N → 0 < s → |dzTrace1 u s| ≤ |Work.Spaces.pz u s (Real.pi / 4)|
      + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
        * (Real.sqrt (gamEnergy α u s) / s) := by
    intro s hsN hs
    have hDz : |Work.Spaces.Dz u s (Real.pi / 4)| / s
        = |Work.Spaces.pz u s (Real.pi / 4)| := by
      rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs, mul_div_cancel_left₀ _ (ne_of_gt hs)]
    rw [htr1 s hsN hs, abs_div, abs_of_pos hs]
    calc |c1f s| / s ≤ (|Work.Spaces.Dz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
            * Real.sqrt (gamEnergy α u s)) / s :=
        div_le_div_of_nonneg_right (hc1bd s hsN hs) (le_of_lt hs)
      _ = |Work.Spaces.pz u s (Real.pi / 4)|
          + Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
            * (Real.sqrt (gamEnergy α u s) / s) := by
        rw [add_div, hDz, mul_div_assoc]
  -- ## the trace functions are locally integrable
  have hTrInt : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (dzTrace0 u) (Set.Ioo a b) := by
    intro a b ha hab
    have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
        (Set.Ioo a b) := by
      have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
          (Set.Icc a b) :=
        ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
          (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
            (fun s hs => lt_of_lt_of_le ha (Set.mem_Icc.mp hs).1)
      exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have h2 : MeasureTheory.IntegrableOn (fun s : ℝ =>
        Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
          * (Real.sqrt (gamEnergy α u s) / s)) (Set.Ioo a b) :=
      ((integrableOn_sqrt_gamEnergy_div hMixO (lt_trans ha hab)).mono_set
        (fun s hs => ⟨lt_trans ha hs.1, hs.2⟩)).const_mul _
    refine MeasureTheory.Integrable.mono' (h1.add h2) ?_ ?_
    · have hle : volume.restrict (Set.Ioo a b) ≤ volume.restrict (Set.Ioi (0:ℝ)) :=
        MeasureTheory.Measure.restrict_mono_set volume (fun s hs => lt_trans ha hs.1)
      exact ((aemeasurable_dzTrace0 (u := u) hS).aestronglyMeasurable).mono_measure hle
    · have hGoodae : ∀ᵐ s ∂(volume.restrict (Set.Ioo a b)), s ∉ N := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        filter_upwards [hNae] with s hsN _
        exact hsN
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo, hGoodae]
        with s hs hsN
      rw [Real.norm_eq_abs]
      exact htrbd s hsN (lt_trans ha hs.1)
  have hTr1Int : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (dzTrace1 u) (Set.Ioo a b) := by
    intro a b ha hab
    have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => |Work.Spaces.pz u s (Real.pi / 4)|)
        (Set.Ioo a b) := by
      have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz u s (Real.pi / 4))
          (Set.Icc a b) :=
        ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.pz u) (s := Set.Ioi 0)
          (t := Set.Ioo (0:ℝ) (Real.pi / 2)) (hS.pz) hpi4mem).continuousOn).mono
            (fun s hs => lt_of_lt_of_le ha (Set.mem_Icc.mp hs).1)
      exact ((hcont.abs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have h2 : MeasureTheory.IntegrableOn (fun s : ℝ =>
        Real.sqrt (K * (Real.pi / 4) ^ (Work.Spaces.gam α - 1))
          * (Real.sqrt (gamEnergy α u s) / s)) (Set.Ioo a b) :=
      ((integrableOn_sqrt_gamEnergy_div hMixO (lt_trans ha hab)).mono_set
        (fun s hs => ⟨lt_trans ha hs.1, hs.2⟩)).const_mul _
    refine MeasureTheory.Integrable.mono' (h1.add h2) ?_ ?_
    · have hle : volume.restrict (Set.Ioo a b) ≤ volume.restrict (Set.Ioi (0:ℝ)) :=
        MeasureTheory.Measure.restrict_mono_set volume (fun s hs => lt_trans ha hs.1)
      exact ((aemeasurable_dzTrace1 (u := u) hS).aestronglyMeasurable).mono_measure hle
    · have hGoodae : ∀ᵐ s ∂(volume.restrict (Set.Ioo a b)), s ∉ N := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        filter_upwards [hNae] with s hsN _
        exact hsN
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo, hGoodae]
        with s hs hsN
      rw [Real.norm_eq_abs]
      exact htr1bd s hsN (lt_trans ha hs.1)
  -- ## the cut-off functions have vanishing interval integrals
  have hcut0 : ∀ (ε : ℝ), 0 < ε → ∀ z t : ℝ, 0 < z → 0 < t → ε < z → z ∉ N → z + t ∉ N →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x) = 0 := by
    intro ε hε z t hz ht hεz hzN hztN
    have hII : (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hII2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x)
        = ∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hmid : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace0 u) x :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun x hx => by
          have h1 : Set.indicator (Set.Ioi ε) (dzTrace0 u) x = dzTrace0 u x :=
            Set.indicator_of_mem (lt_trans hεz hx.1) (dzTrace0 u)
          have h2 : Set.indicator (Set.Ioi 0) (dzTrace0 u) x = dzTrace0 u x :=
            Set.indicator_of_mem (lt_trans hε (lt_trans hεz hx.1)) (dzTrace0 u)
          rw [h1, h2])
    rw [hII, hmid, hII2]
    exact hdct0 z t hz ht hzN hztN
  have hcut1 : ∀ (ε : ℝ), 0 < ε → ∀ z t : ℝ, 0 < z → 0 < t → ε < z →
      (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x) = 0 := by
    intro ε hε z t hz ht hεz
    have hII : (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hII2 : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x)
        = ∫ x in z..(z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x := by
      rw [intervalIntegral.integral_of_le (by linarith : z ≤ z + t),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hmid : (∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x)
        = ∫ x in Set.Ioo z (z + t), Set.indicator (Set.Ioi 0) (dzTrace1 u) x :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun x hx => by
          have h1 : Set.indicator (Set.Ioi ε) (dzTrace1 u) x = dzTrace1 u x :=
            Set.indicator_of_mem (lt_trans hεz hx.1) (dzTrace1 u)
          have h2 : Set.indicator (Set.Ioi 0) (dzTrace1 u) x = dzTrace1 u x :=
            Set.indicator_of_mem (lt_trans hε (lt_trans hεz hx.1)) (dzTrace1 u)
          rw [h1, h2])
    rw [hII, hmid, hII2]
    exact hdct1 z t hz ht
  -- ## the a.e. good set of `t`-translates
  have hNcc : volume (Nᶜ)ᶜ = 0 := by simpa using hNnull
  have hNaet : ∀ z : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), z + t ∈ Nᶜ := by
    intro z
    have hnull : volume ((fun t : ℝ => z + t) ⁻¹' (Nᶜ)ᶜ) = 0 := by
      rw [MeasureTheory.measure_preimage_add]
      exact hNcc
    rw [MeasureTheory.ae_iff]
    rw [MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi]
    refine MeasureTheory.measure_mono_null ?_ hnull
    intro t ht
    exact ht.1
  -- ## measurable conull set and the two Lebesgue-differentiation applications
  have hNcmeas : MeasurableSet Nᶜ := hNmeas.compl
  have hper0 : ∀ n : ℕ, ∀ᵐ z ∂(volume.restrict (Set.Ioi (1/((n:ℝ)+1)))),
      dzTrace0 u z = 0 := by
    intro n
    set ε : ℝ := 1 / ((n:ℝ) + 1) with hεdef
    have hεpos : 0 < ε := by positivity
    have hloc : MeasureTheory.LocallyIntegrable (Set.indicator (Set.Ioi ε) (dzTrace0 u)) volume :=
      locallyIntegrable_indicator_Ioi hεpos
        (fun a b ha hab => hTrInt a b (lt_of_lt_of_le hεpos ha) hab)
    have hint : ∀ᵐ z ∂(volume.restrict (Set.Ioi ε ∩ Nᶜ)),
        ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
          (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace0 u) x) = 0 := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi.inter hNcmeas)]
        with z hz
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hNaet z]
        with t ht hNt
      exact hcut0 ε hεpos z t (lt_trans hεpos hz.1) ht hz.1 hz.2 hNt
    have hmain := aeZeroOn_of_intervalIntegralZero hloc hint
    have hae : Set.Ioi ε ∩ Nᶜ =ᵐ[volume] Set.Ioi ε := by
      refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
      · rw [show (Set.Ioi ε ∩ Nᶜ) \ Set.Ioi ε = ∅ from
          Set.diff_eq_empty.mpr Set.inter_subset_left]
        simp
      · refine MeasureTheory.measure_mono_null ?_ hNnull
        intro z hz
        by_contra hzN
        exact hz.2 ⟨hz.1, hzN⟩
    rw [MeasureTheory.Measure.restrict_congr_set hae] at hmain
    filter_upwards [hmain,
      MeasureTheory.ae_restrict_mem (μ := volume) (s := Set.Ioi ε) measurableSet_Ioi]
      with z hz hzε
    rwa [Set.indicator_of_mem hzε (dzTrace0 u)] at hz
  have hper1 : ∀ n : ℕ, ∀ᵐ z ∂(volume.restrict (Set.Ioi (1/((n:ℝ)+1)))),
      dzTrace1 u z = 0 := by
    intro n
    set ε : ℝ := 1 / ((n:ℝ) + 1) with hεdef
    have hεpos : 0 < ε := by positivity
    have hloc : MeasureTheory.LocallyIntegrable (Set.indicator (Set.Ioi ε) (dzTrace1 u)) volume :=
      locallyIntegrable_indicator_Ioi hεpos
        (fun a b ha hab => hTr1Int a b (lt_of_lt_of_le hεpos ha) hab)
    have hint : ∀ᵐ z ∂(volume.restrict (Set.Ioi ε)),
        ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
          (∫ x in z..(z + t), Set.indicator (Set.Ioi ε) (dzTrace1 u) x) = 0 := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hcut1 ε hεpos z t (lt_trans hεpos hz) ht hz
    have hmain := aeZeroOn_of_intervalIntegralZero hloc hint
    filter_upwards [hmain,
      MeasureTheory.ae_restrict_mem (μ := volume) (s := Set.Ioi ε) measurableSet_Ioi]
      with z hz hzε
    rwa [Set.indicator_of_mem hzε (dzTrace1 u)] at hz
  have hzero0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), dzTrace0 u z = 0 := by
    rw [MeasureTheory.ae_iff]
    rw [MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi]
    have hcov : {z : ℝ | ¬ dzTrace0 u z = 0} ∩ Set.Ioi (0:ℝ) ⊆
        ⋃ n : ℕ, ({z : ℝ | ¬ dzTrace0 u z = 0} ∩ Set.Ioi (1/((n:ℝ)+1))) := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < z by simpa using hz.2)
      exact Set.mem_iUnion.mpr ⟨n, ⟨hz.1, hn⟩⟩
    refine MeasureTheory.measure_mono_null hcov ?_
    refine MeasureTheory.measure_iUnion_null ?_
    intro n
    exact MeasureTheory.Measure.measure_inter_eq_zero_of_restrict
      (MeasureTheory.ae_iff.mp (hper0 n))
  have hzero1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), dzTrace1 u z = 0 := by
    rw [MeasureTheory.ae_iff]
    rw [MeasureTheory.Measure.restrict_apply_eq_zero' measurableSet_Ioi]
    have hcov : {z : ℝ | ¬ dzTrace1 u z = 0} ∩ Set.Ioi (0:ℝ) ⊆
        ⋃ n : ℕ, ({z : ℝ | ¬ dzTrace1 u z = 0} ∩ Set.Ioi (1/((n:ℝ)+1))) := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < z by simpa using hz.2)
      exact Set.mem_iUnion.mpr ⟨n, ⟨hz.1, hn⟩⟩
    refine MeasureTheory.measure_mono_null hcov ?_
    refine MeasureTheory.measure_iUnion_null ?_
    intro n
    exact MeasureTheory.Measure.measure_inter_eq_zero_of_restrict
      (MeasureTheory.ae_iff.mp (hper1 n))
  -- ## conclusion
  have hGoodOn : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), z ∉ N :=
    MeasureTheory.ae_restrict_of_ae hNae
  have hconv0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [hzero0, hGoodOn, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with z hz hzN hzpos
    have h1 : Filter.Tendsto (fun θ => Work.Spaces.pz u z θ)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := hlim0 z hzN hzpos
      rw [← htr0 z hzN hzpos, hz] at h
      exact h
    simpa using h1.const_mul z
  have hconv1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    filter_upwards [hzero1, hGoodOn, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with z hz hzN hzpos
    have h1 : Filter.Tendsto (fun θ => Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h := hlim1 z hzN hzpos
      rw [← htr1 z hzN hzpos, hz] at h
      exact h
    simpa using h1.const_mul z
  filter_upwards [hconv0, hconv1] with z h0 h1
  exact ⟨h0, h1⟩

end Work.FTS.EllipticEst.Prop
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.thetaInterpCoreOfTraceBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted angular interpolation `thetaInterpCore` from the trace bounds

The hypothesis `hTB` is the one-sided trace bound of `Prop.traceBoundLeft` / `Prop.traceBoundRight`
(carried here as a hypothesis).  The conclusion is the one-dimensional weighted interpolation
inequality of `Core.i0Aux.thetaInterpCore`.

The proof does not use `hTB`.  It reduces the problem to the *trace-vanishing* case
(`Core.i0Aux.traceVanishingInterp`) by subtracting a *surrogate* `ℓ = surrFun ψ F₀ F₁ L`
(`Core.i0Aux.TVRed`) which reproduces the two endpoint traces of `f` and whose weighted energies
are controlled at the scale `L = sScale P E = (P/(16(P+E)))^{1/4}` (`Core.i0Aux.TVRed.Helpers`).
The estimates on the surrogate are `TIProp.surrBounds` (from `TVRed.surrIntegrals` together with
the endpoint value estimates `TVRed.endpointParamLeftW` / `endpointParamRightW`, which also control
the two endpoint traces), and the difference `g = f - ℓ` is handled by the trace-vanishing
inequality, using the derivative identities and weighted-square integrability lemmas of
`Core.i0Aux.TVRed.tvHypAux`.  The intermediate bounds are packaged in `TIProp.bounds`.
-/

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

local notation "σ" => Work.FTS.EllipticEst.thEta

end

end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EpsEngine.Rop_block_abs_le_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.EpsEngine

/-- `(1/4)·min z 1 + 1/(1+z) ≤ 1` for `z > 0`: the arithmetic core of the `Rop`-slot bound.
In the regime `z ≤ 1` it reads `z/4 ≤ z/(1+z)`, i.e. `1 + z ≤ 4`, i.e. `z ≤ 3`; in the regime
`z ≥ 1` (`min z 1 = 1`) it reads `1/4 + 1/(1+z) ≤ 1`, i.e. `1 ≤ 3z`. -/
private lemma quarter_min_add_inv_le_one {z : ℝ} (hz : 0 < z) :
    (1 / 4 : ℝ) * min z 1 + 1 / (1 + z) ≤ 1 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hkey : (1 / 4 : ℝ) * min z 1 ≤ z / (1 + z) := by
    rcases lt_or_ge z 1 with h | h
    · rw [min_eq_left (le_of_lt h), le_div_iff₀ h1z]
      nlinarith [hz, h]
    · rw [min_eq_right h, le_div_iff₀ h1z]
      nlinarith [hz, h]
  have h2 : z / (1 + z) + 1 / (1 + z) = 1 := by
    field_simp
    ring
  linarith [hkey, h2]

/-- The `Rop` slot of the `EpsDecay` clause of `EpsUniformMem`, in absolute value.  With the
decomposition `PhiTil α f (Φs + E f) = PhiTil α f (E f) + PhiTil α F_* Φs + Theta α F_*` (the
affineness of `PhiTil` in its second argument plus additivity of `Rop`, `Rop_Uop_Vop_add`), the
three pieces are bounded by

* the `EllPkgGo` piece: `|Rop α (PhiTil α f (E f))| ≤ Cpt · Ce · C₀α² · min z 1` (from `HQo α 4`
  and `hkMem_pointwise_min`; `Cpt` its constant),
* the star piece: `|Rop α (PhiTil α F_* Φs)| ≤ Cs α · z/(1+z)` (from `StarPkgo2.R`, whose `WDp 4`
  bound gives `|(z+1)/z · Rop α (PhiTil α F_* Φs)| ≤ Cs α`),
* the explicit piece: `Rop α (Theta α F_*) = 1/(1+z) − α sin²θ z/(1+z)² ∈ [0, 1/(1+z)]`
  (`Work.FTS.EpsEngine.Theta_Fstar_ops`).

The first two bounds are the two inputs here; the conclusion `|·| ≤ 1` holds as soon as
`Cpt·Ce·C₀α² + Cs α ≤ 1/4`: for `z ≥ 1` the three pieces are `≤ 1/4, 1/4, 1/2`; for `0 < z ≤ 1`
the sum is `≤ S·z + 1/(1+z)` with `S ≤ 1/4 ≤ 1/(1+z)`. -/
theorem Rop_block_abs_le_one {α Cpt Ce Cs C₀ : ℝ} {f Φs : ℝ → ℝ → ℝ} {E : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ}
    {z θ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hCpt : 0 ≤ Cpt) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) (hC₀ : 0 ≤ C₀)
    (hsmall : Cpt * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1 / 4)
    (hdec : Work.Construction.Rop α (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ
        = Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ
          + Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ)
    (hE : |Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ|
        ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1)
    (hS : |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ Cs * α * z / (1 + z)) :
    |Work.Construction.Rop α (Work.Construction.PhiTil α f
        (fun z θ => Φs z θ + E f z θ)) z θ| ≤ 1 := by
  -- The explicit piece: its closed form (`Theta_Fstar_ops`), at the given `(z,θ)`.
  have hCeq : Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
      = 1 / (1 + z) - α * (Real.sin θ) ^ 2 * z / (1 + z) ^ 2 :=
    (Theta_Fstar_ops hα hα1).1 z θ hz hθ.1 hθ.2
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hsin0 : (0 : ℝ) ≤ (Real.sin θ) ^ 2 := sq_nonneg _
  have hsin1 : (Real.sin θ) ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hαsin : α * (Real.sin θ) ^ 2 ≤ 1 := by
    calc α * (Real.sin θ) ^ 2 ≤ 1 * (Real.sin θ) ^ 2 := mul_le_mul_of_nonneg_right hα1 hsin0
      _ = (Real.sin θ) ^ 2 := one_mul _
      _ ≤ 1 := hsin1
  have hkey : α * (Real.sin θ) ^ 2 * z ≤ 1 + z := by nlinarith [hαsin, hz]
  have hfrac : α * (Real.sin θ) ^ 2 * z / (1 + z) ^ 2 ≤ 1 / (1 + z) := by
    rw [div_le_iff₀ (pow_pos h1z 2)]
    have hh : 1 / (1 + z) * (1 + z) ^ 2 = 1 + z := by
      rw [div_mul_eq_mul_div, one_mul, pow_two]
      exact mul_div_cancel_left₀ (1 + z) (ne_of_gt h1z)
    rw [hh]
    exact hkey
  -- the explicit piece lies in `[0, 1/(1+z)]`
  have hCnn : 0 ≤ Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
    rw [hCeq]
    linarith
  have hCle : Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
      ≤ 1 / (1 + z) := by
    rw [hCeq]
    have h0 : (0 : ℝ) ≤ α * (Real.sin θ) ^ 2 * z / (1 + z) ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hα.le hsin0) hz.le) (sq_nonneg _)
    linarith
  have hCabs : |Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ|
      ≤ 1 / (1 + z) :=
    abs_le.mpr ⟨by
      have h0 : (0 : ℝ) ≤ 1 / (1 + z) := div_nonneg zero_le_one h1z.le
      linarith, hCle⟩
  -- the star piece is bounded by a multiple of `min z 1`
  have hmin0 : (0 : ℝ) ≤ min z 1 := le_min hz.le zero_le_one
  have hzdiv : z / (1 + z) ≤ min z 1 := by
    rw [le_min_iff]
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ h1z]
      nlinarith [sq_nonneg z, hz]
    · rw [div_le_one h1z]
      linarith
  have hB2 : |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
      ≤ Cs * α * min z 1 := by
    have h := mul_le_mul_of_nonneg_left hzdiv (mul_nonneg hCs hα.le)
    rw [← mul_div_assoc] at h
    exact le_trans hS h
  -- assemble the three bounds
  rw [hdec]
  calc |Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ|
      ≤ |Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ|
        + |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ| :=
        abs_add_three _ _ _
    _ ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 + Cs * α * min z 1 + 1 / (1 + z) := by
        linarith [hE, hB2, hCabs]
    _ = (Cpt * (Ce * (C₀ * α ^ 2)) + Cs * α) * min z 1 + 1 / (1 + z) := by ring
    _ ≤ 1 / 4 * min z 1 + 1 / (1 + z) := by
        have hm := mul_le_mul_of_nonneg_right hsmall hmin0
        linarith
    _ ≤ 1 := quarter_min_add_inv_le_one hz

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.sliceAng_le8 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0)

/-- **The uniform angular slice bound, level `8`.**  The level-`8` instance of the family
`Work.FTS.OpenPkg.ProdOpen.sliceAng_le` (`a+b ≤ 3`, `ℋ⁴`) and
`Work.FTS.StrongPersist.N6.sliceAng_le6` (`a+b ≤ 5`, `ℋ⁶`): for `f` of class `C^∞` on the open
quadrant with `HkMem α 8 f`, the weighted angular slice integral of every mixed slot
`D_z^b D_θ^a f` with `1 ≤ a` and `a + b ≤ 7` is bounded uniformly in the radius by
`4 |f|²_{ℋ⁸}`.

Proof: the radial window inequality `Work.FTS.TransportS.half_line_window_bound` applied
slicewise in `θ` at the angle-dependent window `R₀ = max z 1`, which converts the missing
vanishing at infinity into an average over a window of length `R₀ ≥ 1`; the two resulting
radial terms are dominated by the `ℋ⁸`-integrand through the slots `(a, b+1)` (needs
`a + b + 1 ≤ 8`) and `(a, b)` (needs `a + b ≤ 8`, using `1 ≤ w`), and Tonelli
(`sda_HkSqSwap_open8`) turns the `θ`-integral of the radial integrand into `HkSq α 8 f`. -/
theorem sliceAng_le8 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 8 f →
    1 ≤ a → a + b ≤ 7 → ∀ z : ℝ, 0 < z →
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ C * Work.Spaces.HkSq α 8 f := by
  refine ⟨4, by norm_num, ?_⟩
  intro α f b a hα hα1 hF hmem ha hab z hz
  obtain ⟨hswap, hGint, hGslice⟩ := sda_HkSqSwap_open8 α f hF hmem
  have hHknn : 0 ≤ HkSq α 8 f := HkSq_nonneg α 8 f
  set R₀ : ℝ := max z 1 with hR₀def
  have hzR : z ≤ R₀ := le_max_left _ _
  have hR1 : (1 : ℝ) ≤ R₀ := le_max_right _ _
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hzR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  have hbound : ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      IntegrableOn (fun s => HkIntegrand α 8 f s θ) Iz →
      (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        ≤ (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 8 f s θ := by
    intro θ hθ hθint
    have hθIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hlamnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(gam α)) := Real.rpow_nonneg hsinpos.le _
    have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
        HasDerivAt (fun x' : ℝ => mixed b a f x' θ) (pz (mixed b a f) x θ) x :=
      fun x hx => (hF.mixed b a).hasDerivAt_slice hθ (lt_of_lt_of_le hz hx.1)
    have hcont : ContinuousOn (fun x : ℝ => mixed b a f x θ) (Set.Icc R₀ (2 * R₀)) :=
      ((hF.mixed b a).curry_z hθ).continuousOn.mono
        (fun x hx => lt_of_lt_of_le hRpos hx.1)
    have hcont' : ContinuousOn (fun x : ℝ => pz (mixed b a f) x θ) (Set.Icc z (2 * R₀)) :=
      (((hF.mixed b a).pz).curry_z hθ).continuousOn.mono
        (fun x hx => lt_of_lt_of_le hz hx.1)
    have hint : IntegrableOn (fun x : ℝ => (mixed b a f x θ) ^ 2)
        (Set.Icc R₀ (2 * R₀)) :=
      ContinuousOn.integrableOn_compact isCompact_Icc (hcont.pow 2)
    have hwin := Work.FTS.TransportS.half_line_window_bound
      (h := fun x : ℝ => mixed b a f x θ)
      (h' := fun x : ℝ => pz (mixed b a f) x θ) hz hzR hderiv hcont hcont' hint
    -- domination of the two summands by the `ℋ⁸`-integrand
    have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
        (Real.sin (2 * θ)) ^ (-(gam α)) * (x * pz (mixed b a f) x θ * w x) ^ 2
          ≤ HkIntegrand α 8 f x θ := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
      have heq : x * pz (mixed b a f) x θ = mixed (b + 1) a f x θ := rfl
      rw [heq, mul_pow]
      have hkey : (Real.sin (2 * θ)) ^ (-(gam α))
            * ((mixed (b + 1) a f x θ) ^ 2 * (w x) ^ 2)
          = (mixed (b + 1) a f x θ * Wt α x θ) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α x θ hsinpos]
        ring
      calc (Real.sin (2 * θ)) ^ (-(gam α)) * ((mixed (b + 1) a f x θ) ^ 2 * (w x) ^ 2)
          = (mixed (b + 1) a f x θ * Wt α x θ) ^ 2 := hkey
        _ ≤ HkIntegrand α 8 f x θ :=
            sq_le_HkIntegrand_mixed α 8 f x θ a (b + 1) ha (by omega)
    have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
        (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
          ≤ HkIntegrand α 8 f x θ := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hRpos hx.1
      have hw : (1 : ℝ) ≤ w x := Work.FTS.TransportS.one_le_w hxpos
      have hcmp : (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
          ≤ (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
        have hw2 : (1 : ℝ) ≤ (w x) ^ 2 := by nlinarith [hw]
        have h1 : (mixed b a f x θ) ^ 2 ≤ (mixed b a f x θ) ^ 2 * (w x) ^ 2 := by
          calc (mixed b a f x θ) ^ 2 = (mixed b a f x θ) ^ 2 * 1 := by ring
            _ ≤ (mixed b a f x θ) ^ 2 * (w x) ^ 2 :=
                mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
        have h2 : (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
            ≤ (Real.sin (2 * θ)) ^ (-(gam α)) * ((mixed b a f x θ) ^ 2 * (w x) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hlamnn
        calc (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
            ≤ (Real.sin (2 * θ)) ^ (-(gam α)) * ((mixed b a f x θ) ^ 2 * (w x) ^ 2) := h2
          _ = (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by ring
      refine le_trans hcmp ?_
      have hkey : (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
          = (mixed b a f x θ * Wt α x θ) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α x θ hsinpos]
        ring
      calc (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
          = (mixed b a f x θ * Wt α x θ) ^ 2 := hkey
        _ ≤ HkIntegrand α 8 f x θ :=
            sq_le_HkIntegrand_mixed α 8 f x θ a b ha (by omega)
    -- interval integrals
    have hIntA : IntervalIntegrable
        (fun x : ℝ => (x * pz (mixed b a f) x θ * w x) ^ 2) volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (x * pz (mixed b a f) x θ * w x) ^ 2)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      refine (ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_).pow 2
      unfold w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hIntAw : IntervalIntegrable
        (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α)) * (x * pz (mixed b a f) x θ * w x) ^ 2)
        volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α))
        * (x * pz (mixed b a f) x θ * w x) ^ 2) (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      refine ContinuousOn.mul continuousOn_const ?_
      refine (ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_).pow 2
      unfold w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hIntBw : IntervalIntegrable
        (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2)
        volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α))
        * (mixed b a f x θ) ^ 2) (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact ContinuousOn.mul continuousOn_const (hcont.pow 2)
    have hHkcont : ∀ {a' b' : ℝ}, 0 < a' →
        ContinuousOn (fun x : ℝ => HkIntegrand α 8 f x θ) (Set.Icc a' b') := by
      intro a' b' ha'
      have hmap : MapsTo (fun x : ℝ => (x, θ)) (Set.Icc a' b') Q0 := fun x hx =>
        mem_Q0.mpr ⟨lt_of_lt_of_le ha' hx.1, hθ.1, hθ.2⟩
      have hc := (hF.continuousOn_HkIntegrand α 8).comp
        (continuousOn_id.prodMk continuousOn_const) hmap
      simpa only [Function.comp_def, id_eq] using hc
    have hIntA' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 8 f x θ) volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 8 f x θ)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      exact hHkcont hz
    have hIntB' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 8 f x θ) volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 8 f x θ)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact hHkcont hRpos
    have hbigA : ∫ x in z..(2 * R₀), HkIntegrand α 8 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 8 f s θ := by
      rw [intervalIntegral.integral_of_le hz2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 8 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
    have hbigB : ∫ x in R₀..(2 * R₀), HkIntegrand α 8 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 8 f s θ := by
      rw [intervalIntegral.integral_of_le hR2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 8 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
    have hmA := intervalIntegral.integral_mono_on hz2R hIntAw hIntA' hptA
    have hmB := intervalIntegral.integral_mono_on hR2R hIntBw hIntB' hptB
    have hsplitA : (Real.sin (2 * θ)) ^ (-(gam α))
        * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2)
        = ∫ x in z..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
            * (x * pz (mixed b a f) x θ * w x) ^ 2 :=
      (intervalIntegral.integral_const_mul _ _).symm
    have hsplitB : (Real.sin (2 * θ)) ^ (-(gam α))
        * (∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2)
        = ∫ x in R₀..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
            * (mixed b a f x θ) ^ 2 :=
      (intervalIntegral.integral_const_mul _ _).symm
    calc (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        = (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f z θ) ^ 2 := by ring
      _ ≤ (Real.sin (2 * θ)) ^ (-(gam α))
            * (2 * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2)
              + (2 / R₀) * ∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hwin hlamnn
      _ = 2 * ((Real.sin (2 * θ)) ^ (-(gam α))
              * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2))
            + (2 / R₀) * ((Real.sin (2 * θ)) ^ (-(gam α))
              * (∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2)) := by ring
      _ = 2 * (∫ x in z..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
              * (x * pz (mixed b a f) x θ * w x) ^ 2)
            + (2 / R₀) * (∫ x in R₀..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
              * (mixed b a f x θ) ^ 2) := by rw [hsplitA, hsplitB]
      _ ≤ 2 * (∫ s in Iz, HkIntegrand α 8 f s θ)
            + (2 / R₀) * (∫ s in Iz, HkIntegrand α 8 f s θ) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left (le_trans hmA hbigA) (by norm_num)
          · exact mul_le_mul_of_nonneg_left (le_trans hmB hbigB) (by positivity)
      _ = (2 + 2 / R₀) * (∫ s in Iz, HkIntegrand α 8 f s θ) := by ring
  have hle : (fun θ : ℝ => (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)))
      ≤ᵐ[volume.restrict Iθ]
      fun θ : ℝ => (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 8 f s θ := by
    filter_upwards [hGslice, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθint hθ
    exact hbound θ hθ hθint
  have hfae : 0 ≤ᵐ[volume.restrict Iθ]
      (fun θ : ℝ => (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) :=
    ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
        (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _)
  calc ∫ θ in Iθ, (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
      ≤ ∫ θ in Iθ, (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 8 f s θ :=
        integral_mono_of_nonneg hfae (hGint.const_mul _) hle
    _ = (2 + 2 / R₀) * HkSq α 8 f := by
        rw [MeasureTheory.integral_const_mul, hswap]
    _ ≤ 4 * HkSq α 8 f := by
        refine mul_le_mul_of_nonneg_right ?_ hHknn
        have : 2 / R₀ ≤ 2 := by
          rw [div_le_iff₀ hRpos]; linarith
        linarith

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.ApproxCC.contDiffOn_plainMixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.GalBasis.ApproxCC

/-- The partial derivative in the first variable, as an operator on functions `ℝ × ℝ → ℝ`. -/
def partialZ (G : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => deriv (fun z' => G (z', p.2)) p.1

/-- The partial derivative in the second variable, as an operator on functions `ℝ × ℝ → ℝ`. -/
def partialT (G : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => deriv (fun θ' => G (p.1, θ')) p.2



/-- On an open set, the partial `z`-derivative is `fderiv G` evaluated at `(1, 0)`; hence it
loses exactly one order of differentiability. -/
lemma contDiffOn_partialZ {G : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) G U) : ContDiffOn ℝ (n : ℕ) (partialZ G) U := by
  have hfd : ContDiffOn ℝ (n : ℕ) (fderiv ℝ G) U := h.fderiv_of_isOpen hU (by norm_num)
  have hcomp : ContDiffOn ℝ (n : ℕ) (fun p => (fderiv ℝ G p) ((1:ℝ), (0:ℝ))) U :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ), (0:ℝ)))).comp_contDiffOn
      hfd
  refine hcomp.congr ?_
  intro p hp
  have hdOn : DifferentiableOn ℝ G U := h.differentiableOn (by norm_num)
  have hd : DifferentiableAt ℝ G p := (hdOn p hp).differentiableAt (hU.mem_nhds hp)
  have hfdp : HasFDerivAt G (fderiv ℝ G p) p := hd.hasFDerivAt
  have hc : HasDerivAt (fun z' : ℝ => ((z', p.2) : ℝ × ℝ)) ((1:ℝ), (0:ℝ)) p.1 := by
    have h1 := (hasFDerivAt_prodMk_left (𝕜:=ℝ) p.1 p.2).hasDerivAt
    simpa using h1
  have hkey := (hfdp.comp_hasDerivAt p.1 hc).deriv
  simpa only [partialZ, Function.comp_def] using hkey

/-- On an open set, the partial `θ`-derivative is `fderiv G` evaluated at `(0, 1)`; hence it
loses exactly one order of differentiability. -/
lemma contDiffOn_partialT {G : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) G U) : ContDiffOn ℝ (n : ℕ) (partialT G) U := by
  have hfd : ContDiffOn ℝ (n : ℕ) (fderiv ℝ G) U := h.fderiv_of_isOpen hU (by norm_num)
  have hcomp : ContDiffOn ℝ (n : ℕ) (fun p => (fderiv ℝ G p) ((0:ℝ), (1:ℝ))) U :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.apply ℝ ℝ ((0:ℝ), (1:ℝ)))).comp_contDiffOn
      hfd
  refine hcomp.congr ?_
  intro p hp
  have hdOn : DifferentiableOn ℝ G U := h.differentiableOn (by norm_num)
  have hd : DifferentiableAt ℝ G p := (hdOn p hp).differentiableAt (hU.mem_nhds hp)
  have hfdp : HasFDerivAt G (fderiv ℝ G p) p := hd.hasFDerivAt
  have hc : HasDerivAt (fun θ' : ℝ => ((p.1, θ') : ℝ × ℝ)) ((0:ℝ), (1:ℝ)) p.2 := by
    have h1 := (hasFDerivAt_prodMk_right (𝕜:=ℝ) p.1 p.2).hasDerivAt
    simpa using h1
  have hkey := (hfdp.comp_hasDerivAt p.2 hc).deriv
  simpa only [partialT, Function.comp_def] using hkey






end Work.FTS.GalBasis.ApproxCC
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.ApproxCC.mixedMul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Work.Spaces

namespace Work.FTS.GalBasis.ApproxCC

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Smoothness of the iterates `Zb^a Tb^b`

Each application of `Zb = z ∂_z` or `Tb = sin(2θ) ∂_θ` lowers the order of a *global*
`C^n`-regularity on `ℝ × ℝ` by one.  The statement is phrased with the "shifted" form
`k + M` so that no truncated subtraction of natural numbers is needed. -/






/-! ## The mixed derivatives of a `C^9` function and their slices -/




/-! ## Product rule and linearity for `D_z` and `D_θ` -/


private lemma Dz_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun z' => u z' θ) z)
    (hv : DifferentiableAt ℝ (fun z' => v z' θ) z) :
    Work.Spaces.Dz (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dz u z θ * v z θ + u z θ * Work.Spaces.Dz v z θ) := by
  show z * deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
      = cc * (z * deriv (fun z' : ℝ => u z' θ) z * v z θ
        + u z θ * (z * deriv (fun z' : ℝ => v z' θ) z))
  rw [show deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
        = deriv (fun y => cc * ((fun z' : ℝ => u z' θ) * (fun z' : ℝ => v z' θ)) y) z from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma Dz_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => A i z' θ) z) :
    Work.Spaces.Dz (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dz (A i) z θ := by
  have hfun : (fun z' : ℝ => ∑ i ∈ s, A i z' θ) = (∑ i ∈ s, fun z' : ℝ => A i z' θ) := by
    funext z'
    rw [Finset.sum_apply]
  show z * deriv (fun z' : ℝ => ∑ i ∈ s, A i z' θ) z
      = ∑ i ∈ s, z * deriv (fun z' : ℝ => A i z' θ) z
  rw [hfun, deriv_sum h, Finset.mul_sum]


private lemma Dth_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun θ' => u z θ') θ)
    (hv : DifferentiableAt ℝ (fun θ' => v z θ') θ) :
    Work.Spaces.Dth (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dth u z θ * v z θ + u z θ * Work.Spaces.Dth v z θ) := by
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
      = cc * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => u z θ') θ * v z θ
        + u z θ * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => v z θ') θ))
  rw [show deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
        = deriv (fun y => cc * ((fun θ' : ℝ => u z θ') * (fun θ' : ℝ => v z θ')) y) θ from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma Dth_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun θ' => A i z θ') θ) :
    Work.Spaces.Dth (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dth (A i) z θ := by
  have hfun : (fun θ' : ℝ => ∑ i ∈ s, A i z θ') = (∑ i ∈ s, fun θ' : ℝ => A i z θ') := by
    funext θ'
    rw [Finset.sum_apply]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => ∑ i ∈ s, A i z θ') θ
      = ∑ i ∈ s, Real.sin (2 * θ) * deriv (fun θ' : ℝ => A i z θ') θ
  rw [hfun, deriv_sum h, Finset.mul_sum]

private lemma differentiableAt_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {z : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) z) :
    DifferentiableAt ℝ (fun z' => ∑ i ∈ s, A i z') z := by
  have hfun : (fun z' => ∑ i ∈ s, A i z') = (∑ i ∈ s, A i) := by
    funext z'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

private lemma differentiableAt_sum_θ {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {θ : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) θ) :
    DifferentiableAt ℝ (fun θ' => ∑ i ∈ s, A i θ') θ := by
  have hfun : (fun θ' => ∑ i ∈ s, A i θ') = (∑ i ∈ s, A i) := by
    funext θ'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

/-! ## The Leibniz rule -/


end Work.FTS.GalBasis.ApproxCC
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.FamEAux.Ext =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)
open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The profile extended by zero off the open box -/

/-- The profile, extended by zero off the open box `(A,B) × (C,D)`. -/
def ext (g : ℝ → ℝ → ℝ) (A B C D : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => if (z, θ) ∈ Set.Ioo A B ×ˢ Set.Ioo C D then g z θ else 0










/-! ## Congruence of `D_z`- and `D_θ`-iterates, and of `mixed`, under eventual equality -/

theorem DzIter_congr_eqOn {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter i u))
      (Function.uncurry (Work.Spaces.DzIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro p hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter n u) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter n v) p.1 p.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

theorem DthIter_congr_eqOn {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i u))
      (Function.uncurry (Work.Spaces.DthIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro p hp
      show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n u) p.1 p.2
        = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n v) p.1 p.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hp]

/-- If two functions agree eventually at a point, all their mixed derivatives agree there. -/
theorem mixed_congr_of_eventuallyEq {f1 f2 : ℝ → ℝ → ℝ} {z θ : ℝ} (a b : ℕ)
    (h : Function.uncurry f1 =ᶠ[𝓝 (z, θ)] Function.uncurry f2) :
    Work.Spaces.mixed a b f1 z θ = Work.Spaces.mixed a b f2 z θ := by
  obtain ⟨s, hs, hssub⟩ := Filter.Eventually.exists_mem h
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hs
  have heqW : Set.EqOn (Function.uncurry f1) (Function.uncurry f2) W := by
    intro p hp
    exact hssub p (hWsub hp)
  have hDth : Set.EqOn (Function.uncurry (Work.Spaces.DthIter b f1))
      (Function.uncurry (Work.Spaces.DthIter b f2)) W := DthIter_congr_eqOn hWopen heqW b
  have hfinal := DzIter_congr_eqOn hWopen hDth a hWmem
  simpa only [Function.uncurry, Work.Spaces.mixed] using hfinal

end Work.FTS.GalBasis
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.GalApprox.contDiffAt_pzIter_pthIter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real ContDiff

namespace Work.FTS.GalBasis.GalApprox

set_option maxHeartbeats 1000000

/-! ## Iterated plain derivatives lose exactly as many orders as derivatives are taken

`Work.FTS.GalBasis.contDiffOn_uncurry_pzIter_le` / `..._pthIter_le` prove that the `i`-th
plain partial derivative of a `C^N` function is `C^{N-i}`, but only under the *strict*
hypothesis `i < N`.  The boundary case `i = N` (where the conclusion is merely `C^0`, i.e.
continuity) is needed here, because the target statement allows `k = 0` with `i + j = n`.
The two lemmas below are the versions with `i ≤ N`; the proofs are those of the existing
lemmas, with the strict inequality relaxed (in the induction step one always has
`N - n ≥ 1`, which is all the existing machinery needs). -/




end Work.FTS.GalBasis.GalApprox
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.Gfar_basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis

/-!
# The designated far bump `Gfar` is a test function

`Gfar = famRaw 0 0 3 40 80 1 5` is the family element with `p = q = 0` and `n = 3` on the box
`[40/4, 80/4] × [1/4, 5/4] = [10, 20] × [1/4, 5/4]`.  It is the function used to kill the
zero mode `L₁₂(·)(0)` in the adjustment `testFam`.  This file proves the three elementary
facts needed about it: it is `Ccφ` (globally `C^∞`, supported strictly inside a box), it is
everywhere nonnegative (there is no `z^p θ^q` factor), and it vanishes outside its box.

The proofs are direct from the factorization
`Gfar z θ = famZ 3 40 80 z * famTh 3 1 5 θ` (since `z^0 = θ^0 = 1`) together with the
support/plateau lemmas of `Defs.lean` for `famZ`/`famTh`.
-/





end Work.FTS.GalBasis
end
-- ===== merged: Submission.Work.FTS.NonlinRows.AuxAngRad.AngRadWeights =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.AuxAngRad

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The squared light weight, without a strict positivity hypothesis.**
`(A · w z / sin(2θ)^{η/2})² = A² w(z)² σ(θ)` for `0 ≤ sin(2θ)`.

The proof avoids `Real.rpow_add` (which needs `sin(2θ) > 0`) and uses only
`Real.rpow_mul` and `Real.rpow_neg`, both of which hold for `0 ≤ x`. -/
theorem light_sq_nn (A z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (A * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = A ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ := by
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) 2,
      ← Real.rpow_mul hs]
    congr 1
    push_cast
    ring
  rw [mul_pow, div_pow, h1, Work.FTS.Nonlinear.RadialProd.smE, div_eq_mul_inv,
    ← Real.rpow_neg hs]
  ring

/-- **The squared heavy weight, without a strict positivity hypothesis.**
`(A · Wt α z θ)² = A² w(z)² τ(α,θ)` for `0 ≤ sin(2θ)`. -/
theorem heavy_sq_nn (α A z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (A * Work.Spaces.Wt α z θ) ^ 2
      = A ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2,
      ← Real.rpow_mul hs]
    congr 1
    push_cast
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, Work.FTS.Nonlinear.RadialProd.smG, mul_pow,
    mul_pow, h1]
  ring

/-- The product of an angular and a radial `SmoothOpen` function is `SmoothOpen` on the open
quadrant.  (The uncurried product is the product of the two uncurried factors.) -/
theorem smoothOpen_ang_rad {a r : ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ))
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * r z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.2) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun _ (θ : ℝ) => a θ)).mp ha n
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => r p.1) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun z _ => r z)).mp hr n
  have hfun : Function.uncurry (fun z θ : ℝ => a θ * r z)
      = fun p : ℝ × ℝ => a p.2 * r p.1 := rfl
  rw [hfun]
  exact h1.mul h2

/-- The radial density `Rint r` of an honest `ℋ⁴`-function is integrable on `Iz`, because its
`θ`-integral is `∫_θ HkIntegrand α 4 r z θ = Rint r z · Kth` with `Kth ≥ 1`. -/
theorem integrableOn_Rint_of_HkMem {α : ℝ} {r : ℝ → ℝ}
    (hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z)) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.Nonlinear.RadialProd.Rint r z)
      Work.Spaces.Iz := by
  have hKth : Work.FTS.Nonlinear.RadialProd.Kth ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one Work.FTS.Nonlinear.RadialProd.one_le_Kth)
  have h : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.Nonlinear.RadialProd.Rint r z * Work.FTS.Nonlinear.RadialProd.Kth)
      Work.Spaces.Iz := by
    simpa only [Work.FTS.Nonlinear.RadialProd.integral_HkIntegrand_rad] using hrmem.2
  exact MeasureTheory.IntegrableOn.congr_fun (h.div_const Work.FTS.Nonlinear.RadialProd.Kth)
    (fun z _ => mul_div_cancel_right₀ _ hKth) measurableSet_Ici

end Work.FTS.NonlinRows.AuxAngRad
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.mixed_succ_expansion_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The angular multiplier `θ ↦ sin(2θ)`, as a function on `(z,θ)` (notation for the
`Sfun` of `Work.FTS.TransportS`). -/
local notation "Sfn" => Work.FTS.TransportS.Sfun


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row19Prep.row19_eta_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open.Row19Prep

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-! ## A `z`-independent factor passes through the radial derivatives

The two lemmas below isolate the factor `α·Γ(θ)` of the row-19 product (which does not depend on
`z`) from the Leibniz expansion of `∂_z^m (A·H₂)`.  They are the `pzIter`-counterpart of
`Work.FTS.H2.pzIter_const_mul`; the single `deriv`-step uses the *unconditional* field form
`deriv_const_mul_field`. -/



/-- `∂_z^k` of a function of `z` alone is the `k`-th iterate of `deriv`. -/
theorem pzIter_zOnly (r : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => r z) = fun z θ => deriv^[k] r z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.pzIter_succ, ih]
    funext z θ
    exact (congrFun (Function.iterate_succ_apply' deriv k r) z).symm

/-! ## Smoothness of the radial factor -/



/-! ## The `j = 0` case of the mixed Leibniz bound -/



end Work.FTS.Nonlinear.Open.Row19Prep
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false

/-! ## Elementary angular facts on `Iθ = [0, π/2]` -/

lemma sinTwo_mem_Icc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ θ := hθ.1
  have h1 : θ ≤ Real.pi / 2 := hθ.2
  constructor
  · exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  · exact Real.sin_le_one _

/-! ## Crude bounds for the `D_θ`-iterates of `qfun`

They are all that is needed for the Leibniz corrections `D_θ^i (α q)`, since the factor `α`
already supplies the smallness in `α`. -/

/-- `D_θ^i qfun` is `O(sin 2θ)`; the `sin 2θ` factor is what makes the induction close near
the two endpoints of `Iθ`. -/
lemma dthU_qfun_le_sin {i : ℕ} (hi : 1 ≤ i) (hi4 : i ≤ 4) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[i] Work.Spaces.qfun θ| ≤ 1000 * Real.sin (2 * θ) := by
  have hs := sinTwo_mem_Icc hθ
  have h := Work.FTS.Nonlinear.FstarPkg.DthAux.DthQfunBound hi hi4 θ hθ
  have h1 : (1000 : ℝ) * (Real.sin (2 * θ)) ^ 2 ≤ 1000 * Real.sin (2 * θ) := by
    nlinarith [hs.1, hs.2]
  linarith [h, h1]

/-- The crude bound `|D_θ^m qfun| ≤ 1000` on `Iθ`, for `m ≤ 4`. -/
lemma qfun_iter_abs_le {m : ℕ} (hm : m ≤ 4) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| ≤ 1000 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp only [Function.iterate_zero_apply]
    exact (Work.FTS.Nonlinear.FstarPkg.DthAux.abs_qfun_le θ).trans (by norm_num)
  · refine (dthU_qfun_le_sin h (by omega) hθ).trans ?_
    have hs := sinTwo_mem_Icc hθ
    linarith [hs.1, hs.2]

/-! ## The constant sequence and the induction hypothesis -/

/-- The geometric sequence of constants of the induction: `KB (j+1) = 20000 * KB j`, with
`KB j ≥ 2·10^7 · 20000^{j-1}` for `j ≥ 1`. -/
noncomputable def KB (j : ℕ) : ℝ := (20000 : ℝ) ^ j * 20000000

lemma KB_pos (j : ℕ) : 0 < KB j := by
  rw [KB]; positivity

lemma KB_succ (j : ℕ) : KB (j + 1) = 20000 * KB j := by
  rw [KB, KB, pow_succ]; ring

lemma KB_mono {j k : ℕ} (hjk : j ≤ k) : KB j ≤ KB k := by
  rw [KB, KB]
  have h1 : (20000 : ℝ) ^ j ≤ (20000 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hjk
  exact mul_le_mul_of_nonneg_right h1 (by norm_num)

/-- `KB 1` dominates the constant of the base case of the induction. -/
lemma KB_one_ge : (17001000 : ℝ) ≤ KB 1 := by
  rw [KB]; norm_num

/-- `Hyp j` controls the `D_θ`-iterates of `Tfun j α` up to order `4 - j` by
`KB j · (α + sin 2θ)`, uniformly for `0 < α ≤ 1` and `θ ∈ Iθ`. -/
def Hyp (j : ℕ) : Prop :=
  ∀ (α θ : ℝ), 0 < α → α ≤ 1 → θ ∈ Work.Spaces.Iθ → ∀ k : ℕ, k ≤ 4 - j →
    |Work.Spaces.dthU^[k] (Work.Spaces.Tfun j α) θ| ≤ KB j * (α + Real.sin (2 * θ))

/-! ## The pointwise Leibniz rule and the bound for the corrections -/

/-- Pointwise form of the iterated Leibniz rule for `dthU`. -/
lemma dthU_iter_mul_apply (m : ℕ) (f g : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (θ : ℝ) :
    Work.Spaces.dthU^[m] (f * g) θ
      = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)
          * (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m - i] g θ) := by
  have h := congrFun (Work.Spaces.dthU_iter_mul m f g hf hg) θ
  simp only [Finset.sum_apply, Work.Spaces.dthCoef_apply] at h
  exact h

/-- The `D_θ^k (α q · Q)` correction term of the Leibniz expansion is bounded by
`16000 · α · KX` whenever `|D_θ^m Q| ≤ KX` for `m ≤ k ≤ 4`. -/
lemma alpha_qfun_leibniz_abs_le (k : ℕ) (hk : k ≤ 4) {α : ℝ} (hα : 0 < α)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {Q : ℝ → ℝ} {KX : ℝ}
    (hQ : ∀ m : ℕ, m ≤ k → |Work.Spaces.dthU^[m] Q θ| ≤ KX) :
    |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
        * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
          * Work.Spaces.dthU^[k - i] Q θ)| ≤ 16000 * α * KX := by
  have hα0 : 0 ≤ α := le_of_lt hα
  have hKX : 0 ≤ KX := le_trans (abs_nonneg (Q θ)) (hQ 0 (Nat.zero_le k))
  have hbinom : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
    have h : ((∑ i ∈ Finset.range (k + 1), k.choose i : ℕ) : ℝ) = (2 : ℝ) ^ k := by
      rw [Nat.sum_range_choose]; push_cast; ring
    simpa using h
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(k.choose i : ℝ) * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
          * Work.Spaces.dthU^[k - i] Q θ)| ≤ (k.choose i : ℝ) * (1000 * α * KX) := by
    intro i hi
    have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
    have hcast : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
    have h1 : |Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ| ≤ 1000 * α := by
      have hrew : Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
          = α * Work.Spaces.dthU^[i] Work.Spaces.qfun θ :=
        congrFun (Work.Spaces.dthU_iter_const_mul i α Work.Spaces.qfun) θ
      rw [hrew, abs_mul, abs_of_pos hα]
      calc α * |Work.Spaces.dthU^[i] Work.Spaces.qfun θ| ≤ α * 1000 :=
            mul_le_mul_of_nonneg_left (qfun_iter_abs_le (by omega) hθ) hα0
        _ = 1000 * α := by ring
    have h2 : |Work.Spaces.dthU^[k - i] Q θ| ≤ KX := hQ (k - i) (Nat.sub_le k i)
    calc |(k.choose i : ℝ) * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
            * Work.Spaces.dthU^[k - i] Q θ)|
        = (k.choose i : ℝ) * (|Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ|
            * |Work.Spaces.dthU^[k - i] Q θ|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hcast]
      _ ≤ (k.choose i : ℝ) * (1000 * α * KX) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) hcast
  calc |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
        * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
          * Work.Spaces.dthU^[k - i] Q θ)|
      ≤ ∑ i ∈ Finset.range (k + 1),
          |(k.choose i : ℝ) * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
            * Work.Spaces.dthU^[k - i] Q θ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (1000 * α * KX) :=
        Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * (1000 * α * KX) := by
        rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ k * (1000 * α * KX) := by rw [hbinom]
    _ ≤ 16 * (1000 * α * KX) := by
        have h2k : (2 : ℝ) ^ k ≤ 16 := by
          calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hk
            _ = 16 := by norm_num
        exact mul_le_mul_of_nonneg_right h2k (by positivity)
    _ = 16000 * α * KX := by ring

end Work.FTS.Nonlinear.Pieces.RNP
end
end
