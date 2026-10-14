import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.BslZsq
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.QDefs
import Submission.Work.H2.WPQ.Dth_DzIter_comm_smoothQuad
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_deriv_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDzAux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.deprecated false
set_option linter.unusedVariables false

open Work.FTS.EllSol.PkgK5.K5c (Qext Qext_of_mem)

/-! ## Elementary facts about the kernel and the doubly odd extension -/

/-- Left of the origin the doubly odd extension is the negated reflected datum. -/
theorem Qext_of_neg (G : ℝ → ℝ → ℝ) (w s : ℝ) (hs : s < 0) : Qext G w s = -G w (-s) := by
  rw [Qext, if_neg (fun h => absurd h.1 (not_le.mpr hs)), if_pos hs]

/-- The reflection `t ↦ π - t` of the real line, as a homeomorphism. -/
private def piSubHomeo : ℝ ≃ₜ ℝ where
  toFun := fun t => Real.pi - t
  invFun := fun t => Real.pi - t
  left_inv := fun t => by ring
  right_inv := fun t => by ring
  continuous_toFun := continuous_const.sub continuous_id
  continuous_invFun := continuous_const.sub continuous_id

/-! ## The two reflected pieces

The two reflected pieces of the argument are proved as independent library lemmas about a bare
kernel `ρ` supported in `(-ε, ε)` and bounded by `M` (`piece_neg_le`, `piece_pi_le`); they are
imported above.  The remaining work here is the transport of the two reflected pieces back to
`Iθ` and the assembly.
-/

/-! ## The target estimate -/


end Work.FTS.EllSol.EllPkgAux.MollDzAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeColl.limitBoundAux.pieces2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeColl.limitBoundAux.pieces2` — shared ingredients for `AeColl.limitBound` (part 2)

The identifications of `Pcut u n`, `Vfull u`, `Dcut u n`, `Trcut u n` with `z`-integrals of
`z`-only slice functions, together with the integrability / measurability / monotonicity facts
about those marginals, and the nonnegativity of `Acut`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeColl

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 5. The `z`-marginal of `V = z∂_z∂_θu`, and `Pcut`/`Vfull` -/

/-- The angular slice energy of `V = z∂_z∂_θu`, as a function of `z` alone. -/
def Gcut (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, (Vz u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ



/-- The inner `θ`-integral of `Vfull` (over `(0,π/2)`) equals the `Iθ`-version. -/
theorem integral_Ioo_Vz_sq (u : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Vz u z θ) ^ 2) = Gcut u z := by
  rw [Gcut]
  rw [MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [sigθ_eq]
  ring

theorem Vfull_eq_integral (u : ℝ → ℝ → ℝ) :
    Vfull u = ∫ z in Set.Ioi 0, wt z * Gcut u z := by
  rw [Vfull]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [integral_Ioo_Vz_sq]

theorem Pcut_eq_integral (u : ℝ → ℝ → ℝ) (n : ℕ) :
    Pcut u n = ∫ z in Set.Ioi 0,
      Work.FTS.EllipticEst.cut n z * (wt z * Gcut u z) := by
  rw [Pcut]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [integral_Ioo_Vz_sq]
  ring

/-- On the support of `cut n` the squared weight `wt` is bounded by an explicit constant. -/
def wtB (n : ℕ) : ℝ := ((1 + 3 * ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) + 1) ^ 2) ^ 2

theorem wt_le_wtB {n : ℕ} {z : ℝ} (hc : Work.FTS.EllipticEst.cut n z ≠ 0) :
    wt z ≤ wtB n := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlo : 1 / ((n : ℝ) + 1) < z := by
    by_contra h
    push_neg at h
    exact hc (Work.FTS.EllipticEst.cut_apply_zero_of_le n h)
  have hhi : z < 3 * ((n : ℝ) + 1) := by
    by_contra h
    push_neg at h
    exact hc (Work.FTS.EllipticEst.cut_apply_zero_of_ge n h)
  have hzpos : 0 < z := lt_trans (div_pos one_pos hn) hlo
  have hzp : (1 : ℝ) < ((n : ℝ) + 1) ^ 2 * z ^ 2 := by
    have h1 : 1 < ((n : ℝ) + 1) * z := by
      rw [div_lt_iff₀ hn] at hlo
      linarith
    nlinarith [h1, hn, hzpos]
  have h1 : (1 + z) ^ 2 ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hw : Work.Spaces.w z ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
    rw [Work.Spaces.w, div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    have hB0 : (0 : ℝ) ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 := sq_nonneg _
    calc (1 + z) ^ 2 ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 := h1
      _ = (1 + 3 * ((n : ℝ) + 1)) ^ 2 * 1 := by ring
      _ ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 * (((n : ℝ) + 1) ^ 2 * z ^ 2) :=
          mul_le_mul_of_nonneg_left (le_of_lt hzp) hB0
      _ = (1 + 3 * ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) + 1) ^ 2 * z ^ 2 := by ring
  rw [wt, wtB]
  exact pow_le_pow_left₀ (Work.FTS.EllipticEst.AngSecond.w_nonneg z) hw 2

theorem cut_mul_wt_bdd (n : ℕ) (z : ℝ) :
    |Work.FTS.EllipticEst.cut n z * wt z| ≤ wtB n := by
  have hB0 : 0 ≤ wtB n := by rw [wtB]; positivity
  have hwt0 : 0 ≤ wt z := by rw [wt]; positivity
  rcases eq_or_ne (Work.FTS.EllipticEst.cut n z) 0 with h | h
  · rw [h, zero_mul, abs_zero]; exact hB0
  · have h1 := wt_le_wtB h
    have h2 : 0 ≤ Work.FTS.EllipticEst.cut n z := Work.FTS.EllipticEst.cut_nonneg n z
    have h3 : Work.FTS.EllipticEst.cut n z ≤ 1 := Work.FTS.EllipticEst.cut_le_one n z
    rw [abs_of_nonneg (mul_nonneg h2 hwt0)]
    calc Work.FTS.EllipticEst.cut n z * wt z ≤ 1 * wt z := mul_le_mul_of_nonneg_right h3 hwt0
      _ ≤ 1 * wtB n := mul_le_mul_of_nonneg_left h1 zero_le_one
      _ = wtB n := one_mul _




/-- `ofReal (∫ f) ≤ ∫⁻ ofReal f` for a nonnegative a.e.-strongly-measurable `f`. -/
theorem ofReal_integral_le_lintegral' (μ : MeasureTheory.Measure ℝ) (f : ℝ → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable f μ) (h0 : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  rcases eq_or_ne (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ⊤ with h | h
  · rw [h]; exact le_top
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hf
        (Filter.Eventually.of_forall h0)).mp h) (Filter.Eventually.of_forall h0)]

/-! ## 6. The `z`-marginals of the mixed bilinear slots `Dcut`, `Trcut` -/

/-- The `z`-marginal of the pairing of `Az = z²∂_z²u` with `∂_θθu`. -/
def ZI (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, Az u z θ * Work.Spaces.pthIter 2 u z θ
    * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ

/-- The `z`-marginal of the pairing of `Uz = z∂_zu` with `∂_θθu`. -/
def YI (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, Uz u z θ * Work.Spaces.pthIter 2 u z θ
    * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ



theorem ZI_integrable {u : ℝ → ℝ → ℝ}
    (hm : Work.FTS.EllipticEst.AngSecond.IPMem (Az u) (Work.Spaces.pthIter 2 u)) :
    MeasureTheory.IntegrableOn (ZI u) Work.Spaces.Iz := hm.2

theorem YI_integrable {u : ℝ → ℝ → ℝ}
    (hm : Work.FTS.EllipticEst.AngSecond.IPMem (Uz u) (Work.Spaces.pthIter 2 u)) :
    MeasureTheory.IntegrableOn (YI u) Work.Spaces.Iz := hm.2

/-- The `z`-integral of the marginal `ZI` is the pairing `IP (Az u) (∂_θθu)`. -/
theorem integral_ZI_eq_IP (u : ℝ → ℝ → ℝ) :
    (∫ z in Set.Ioi 0, ZI u z) = Work.FTS.EllipticEst.AngSecond.IP (Az u)
      (Work.Spaces.pthIter 2 u) := by
  rw [Work.FTS.EllipticEst.AngSecond.IP]
  exact MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))


/-- `Dcut u n` is the `z`-integral of `χ_n · ZI`. -/
theorem Dcut_eq_integral (u : ℝ → ℝ → ℝ) (n : ℕ) :
    Dcut u n = ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * ZI u z := by
  have h1 : ∀ z : ℝ, (∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.cut n z * wt z * sigθ θ * (Az u z θ)
          * (Work.Spaces.pthIter 2 u z θ))
      = Work.FTS.EllipticEst.cut n z * ZI u z := by
    intro z
    have h2 : (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.cut n z * wt z
          * sigθ θ * (Az u z θ) * (Work.Spaces.pthIter 2 u z θ))
        = Work.FTS.EllipticEst.cut n z
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), wt z * (sigθ θ * (Az u z θ)
              * (Work.Spaces.pthIter 2 u z θ))) := by
      rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.cut n z * wt z
            * sigθ θ * (Az u z θ) * (Work.Spaces.pthIter 2 u z θ))
          = ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.cut n z
              * (wt z * (sigθ θ * (Az u z θ) * (Work.Spaces.pthIter 2 u z θ))) from
        setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)]
      rw [MeasureTheory.integral_const_mul]
    have h3 : (∫ θ in Set.Ioo 0 (Real.pi / 2), wt z * (sigθ θ * (Az u z θ)
          * (Work.Spaces.pthIter 2 u z θ))) = ZI u z := by
      rw [MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2))]
      rw [ZI]
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [sigθ_eq, wt_eq]
      ring
    rw [h2, h3]
  rw [Dcut]
  exact setIntegral_congr_fun measurableSet_Ioi (fun z _ => h1 z)

/-- `Dcut u ·` converges to `IP (Az u) (∂_θθu)`. -/
theorem Dcut_tendsto_of_integrable {u : ℝ → ℝ → ℝ}
    (hZ : MeasureTheory.IntegrableOn (ZI u) Work.Spaces.Iz) :
    Filter.Tendsto (fun n : ℕ => ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * ZI u z)
      Filter.atTop (nhds (∫ z in Set.Ioi 0, ZI u z)) := by
  have hsub : (∫ z in Work.Spaces.Iz, ZI u z) = ∫ z in Set.Ioi 0, ZI u z :=
    MeasureTheory.setIntegral_congr_set
      ((MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ))).symm)
  have h := Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cut_mul hZ
  rw [hsub] at h
  refine h.congr' ?_
  filter_upwards with n
  exact MeasureTheory.setIntegral_congr_set
    ((MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ))).symm)

theorem Dcut_tendsto {u : ℝ → ℝ → ℝ}
    (hm : Work.FTS.EllipticEst.AngSecond.IPMem (Az u) (Work.Spaces.pthIter 2 u)) :
    Filter.Tendsto (fun n : ℕ => Dcut u n) Filter.atTop
      (nhds (Work.FTS.EllipticEst.AngSecond.IP (Az u) (Work.Spaces.pthIter 2 u))) := by
  have h := Dcut_tendsto_of_integrable (ZI_integrable hm)
  rw [integral_ZI_eq_IP u] at h
  refine h.congr' ?_
  filter_upwards with n
  exact (Dcut_eq_integral u n).symm

/-- The transfer coefficient `c_n(z) = z·(χ_n)'(z) + χ_n(z)·cw(z)`. -/
def cfun (n : ℕ) (z : ℝ) : ℝ :=
  deriv (Work.FTS.EllipticEst.cut n) z * z + Work.FTS.EllipticEst.cut n z * cwf z

/-- Derivative of the squared weight. -/
theorem deriv_wt {z : ℝ} (hz : 0 < z) :
    deriv wt z = -4 * wt z / ((1 + z) * z) :=
  Work.FTS.EllipticEst.AngSecond.deriv_w2_eq' hz

/-- The rescaled derivative of the truncation weight:
`(χ w² z²)'(z)/z = (zχ'(z) + χ(z)·cw(z))·w²(z)`. -/
theorem deriv_cut_wt_zsq {n : ℕ} {z : ℝ} (hz : 0 < z) :
    deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
      = cfun n z * wt z := by
  have hcut : HasDerivAt (Work.FTS.EllipticEst.cut n)
      (deriv (Work.FTS.EllipticEst.cut n) z) z :=
    (((Work.FTS.EllipticEst.cut_contDiff n).differentiable (by simp)).differentiableAt).hasDerivAt
  have hwt : HasDerivAt wt (deriv wt z) z := by
    have h1 : wt = fun z' : ℝ => ((1 + z') ^ 2 / z' ^ 2) ^ 2 := by
      funext z'; simp only [wt, Work.Spaces.w]
    have h2 : DifferentiableAt ℝ (fun z' : ℝ => ((1 + z') ^ 2 / z' ^ 2) ^ 2) z := by
      have h3 : DifferentiableAt ℝ (fun z' : ℝ => ((1 + z') ^ 2 / z' ^ 2) ^ 2) z := by
        have h4 := (((differentiableAt_const (1:ℝ)).add differentiableAt_id).pow 2).div
          (differentiableAt_id.pow 2) (pow_ne_zero 2 (ne_of_gt hz))
        convert h4.pow 2 using 1
        funext y
        simp only [Pi.add_apply, Pi.pow_apply, Pi.div_apply, id_eq]
      exact h3
    rw [h1]
    exact h2.hasDerivAt
  have hz2 : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hderiv : deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z
      = (deriv (Work.FTS.EllipticEst.cut n) z * wt z + Work.FTS.EllipticEst.cut n z * deriv wt z)
          * z ^ 2 + (Work.FTS.EllipticEst.cut n z * wt z) * (2 * z) :=
    ((hcut.mul hwt).mul hz2).deriv
  rw [hderiv, deriv_wt hz]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by positivity
  unfold cfun cwf
  field_simp
  ring

/-- Uniform bound for the transfer coefficient. -/
theorem abs_cfun_le {n : ℕ} {K : ℝ}
    (hK : ∀ z : ℝ, |z * deriv (Work.FTS.EllipticEst.cut n) z| ≤ K) {z : ℝ}
    (hz : 0 ≤ z) : |cfun n z| ≤ K + 2 := by
  have h1 : |deriv (Work.FTS.EllipticEst.cut n) z| * |z| ≤ K := by
    simpa only [abs_mul, mul_comm] using hK z
  have h2 : |Work.FTS.EllipticEst.cut n z| ≤ 1 := by
    rw [abs_of_nonneg (Work.FTS.EllipticEst.cut_nonneg n z)]
    exact Work.FTS.EllipticEst.cut_le_one n z
  have h3 : |cwf z| ≤ 2 := Work.FTS.EllipticEst.AngSecond.abs_cw_le_two hz
  calc |cfun n z| = |deriv (Work.FTS.EllipticEst.cut n) z * z
        + Work.FTS.EllipticEst.cut n z * cwf z| := by rfl
    _ ≤ |deriv (Work.FTS.EllipticEst.cut n) z * z| + |Work.FTS.EllipticEst.cut n z * cwf z| :=
        abs_add_le _ _
    _ = |deriv (Work.FTS.EllipticEst.cut n) z| * |z| + |Work.FTS.EllipticEst.cut n z| * |cwf z| := by
        simp only [abs_mul]
    _ ≤ K + 1 * 2 := add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) zero_le_one)
    _ = K + 2 := by ring

/-- `Trcut u n` is the `z`-integral of `c_n · YI`. -/
theorem Trcut_eq_integral (u : ℝ → ℝ → ℝ) (n : ℕ) :
    Trcut u n = ∫ z in Set.Ioi 0, cfun n z * YI u z := by
  have h1 : ∀ z : ℝ, (∫ θ in Set.Ioo 0 (Real.pi / 2),
        deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
          * sigθ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ))
      = deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 u z θ * Uz u z θ)
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    intro z
    have h2 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
          deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
            * sigθ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ))
        = deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Uz u z θ)
              * (Work.Spaces.pthIter 2 u z θ)) := by
      rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
            deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
              * sigθ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ))
          = ∫ θ in Set.Ioo 0 (Real.pi / 2),
              (deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z)
                * (sigθ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ)) from
        setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)]
      rw [MeasureTheory.integral_const_mul]
    have h3 : (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Uz u z θ)
          * (Work.Spaces.pthIter 2 u z θ))
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 u z θ * Uz u z θ)
            * Work.FTS.EllipticEst.AngSecond.sig θ := by
      rw [MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2))]
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [sigθ_eq]
      ring
    rw [h2, h3]
  rw [Trcut]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
  rw [h1 z, deriv_cut_wt_zsq hz, mul_assoc]
  rw [← MeasureTheory.integral_const_mul]
  rw [YI]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [wt_eq]
  ring

/-! ## 7. Nonnegativity of the truncated angular energy -/


end Work.FTS.EllipticEst.AeColl
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeLeftTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.H2W.Ae

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-! ## The angular slices of an `AeData` datum are `L¹` against `sinθcos²θ` -/

/-- `θ ↦ sinθcos²θ` is continuous. -/
private theorem continuous_sinCos2 : Continuous sg := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- `θ ↦ |sinθcos²θ|` is integrable on `Iθ`. -/
private theorem integrableOn_abs_sinCos2 :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |sg θ|) Iθ := by
  have h : MeasureTheory.IntegrableOn (fun θ : ℝ => |sg θ|) (Set.Icc 0 (Real.pi / 2)) :=
    continuous_sinCos2.abs.continuousOn.integrableOn_compact isCompact_Icc
  rwa [Work.Spaces.Iθ]

/-- **Slice integrability.**  For a datum whose `θ`-slices are bounded on the open interval
(which `HkMem α 0 (∂_θθu)` supplies through `Endpt.sliceBdd_of_hmB`) the product with the
bounded angular weight `sinθcos²θ` is integrable: at the two endpoints the *values* `u z 0` and
`u z (π/2)` vanish. -/
theorem slice_mul_sinCos2_integrable {α : ℝ} {u : ℝ → ℝ → ℝ} {z : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u))
    (hz : 0 < z) (h0 : u z 0 = 0) (h1 : u z (Real.pi / 2) = 0) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * sg θ) Iθ := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB hsm hmemB hz
  have hSm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => u z θ * sg θ)
      (MeasureTheory.volume.restrict Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry u) hSm.continuousOn hz).mul
      continuous_sinCos2.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' (integrableOn_abs_sinCos2.const_mul C) haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Iθ from measurableSet_Icc) (fun θ hθI => ?_)
  have hb : |u z θ| ≤ C := by
    rcases eq_or_lt_of_le hθI.1 with hθ0 | hθ0
    · rw [← hθ0, h0]; simp only [mul_zero, abs_zero]; exact hCpos.le
    rcases eq_or_lt_of_le hθI.2 with hθ1 | hθ1
    · rw [hθ1, h1]; simp only [mul_zero, abs_zero]; exact hCpos.le
    · exact (hC θ ⟨hθ0, hθ1⟩).1
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)

/-! ## The endpoint moment identity in the weak class -/

/-- **The angular-moment identity.**  For `z > 0` the pairing of the angular operator
`Lzero1 (u z ·)` against the kernel function `sinθcos²θ` is minus the left endpoint limit of the
slice.  This is the form of `Endpt.Lzero1_integral_eq_neg_limit` in which the boundedness of the
slice and of its derivative required by the fundamental theorem of calculus is supplied directly
by `Endpt.sliceBdd_of_hmB`. -/
theorem Lzero1_moment_eq_neg_limit {α : ℝ} {u : ℝ → ℝ → ℝ} {z L : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u)) (hz : 0 < z)
    (hLz : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ) Iθ)
    (hlim : Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ) = -L := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB hsm hmemB hz
  have hcd : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsm hz 2
  exact Work.FTS.EllipticEst.Honest.sliceMoment_eq_neg_limit hCpos.le hcd
    (fun θ hθ => hC θ hθ) hLz hlim

/-! ## The moment of the equation -/

/-- **The moment of the source.**  On the open quadrant the equation reads
`G = -(α²z²)∂_z²u - (α(5+α)z)∂_zu + Lzero u` (`Work.Elliptic.bslOp_apply`); taking the
`θ`-moment against `sinθcos²θ`, and using that `Lzero u` on a slice is `Lzero1 (u z ·)`, gives
the moment identity behind `AeSliceMomentIdent`. -/
theorem fstar_G_eq {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Fstar G z
      = -(α ^ 2 * z ^ 2) * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z
        - (α * (5 + α) * z) * Work.Elliptic.Fstar (Work.Spaces.pz u) z
        + ∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ := by
  -- `Lzero` of the slice is `Lzero1` of the one-variable slice
  have hLzero : ∀ θ : ℝ, Work.Elliptic.Lzero u z θ
      = Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ := by
    intro θ
    simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero,
      Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  obtain ⟨h1, h2, h3⟩ := Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite α u G h hz
  -- ## the pointwise decomposition on the open interval
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ
        = G z θ * sg θ + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
          + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ) := by
    intro θ hθ
    have heq := AeData.eq h z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hkey : Work.Elliptic.Lzero u z θ = G z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + α * (5 + α) * z * Work.Spaces.pz u z θ := by linarith
    rw [← hLzero θ, hkey]
    ring
  have hae : (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ : ℝ => G z θ * sg θ + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
        + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hpt θ hθ)
  -- ## integrability of the source term
  have hGint : MeasureTheory.IntegrableOn (fun θ : ℝ => G z θ * sg θ) Iθ := by
    have hsub : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ
          - (α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
            + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ))) Iθ :=
      h3.sub ((h2.const_mul _).add (h1.const_mul _))
    refine hsub.congr ?_
    filter_upwards [hae] with θ hθ
    linarith
  -- ## the moment identity
  have hIntegral : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
      = Work.Elliptic.Fstar G z
        + α ^ 2 * z ^ 2 * (∫ θ in Iθ, Work.Spaces.pzIter 2 u z θ * sg θ)
        + α * (5 + α) * z * (∫ θ in Iθ, Work.Spaces.pz u z θ * sg θ) := by
    have h1' : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
        = ∫ θ in Iθ, (G z θ * sg θ
            + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
            + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
      MeasureTheory.integral_congr_ae hae
    have hsplit1 : (∫ θ in Iθ, (G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
          + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)))
        = (∫ θ in Iθ, (G z θ * sg θ
            + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)))
          + (∫ θ in Iθ, α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ))
        (g := fun θ : ℝ => α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ))
        (hGint.add (h2.const_mul (α ^ 2 * z ^ 2))) (h1.const_mul (α * (5 + α) * z))
    have hsplit2 : (∫ θ in Iθ, (G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)))
        = (∫ θ in Iθ, G z θ * sg θ)
          + (∫ θ in Iθ, α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)) :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => G z θ * sg θ)
        (g := fun θ : ℝ => α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ))
        hGint (h2.const_mul (α ^ 2 * z ^ 2))
    rw [h1', hsplit1, hsplit2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    rfl
  have hfinal : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
      = Work.Elliptic.Fstar G z
        + α ^ 2 * z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z
        + α * (5 + α) * z * Work.Elliptic.Fstar (Work.Spaces.pz u) z := by
    rw [hIntegral]
    rfl
  linarith [hfinal]

/-- **The angular-moment chain of the weak class `AeData`.**  For a datum `AeData α u G` the two
radial moments of the solution vanish: `F_*(∂_zu) ≡ 0` everywhere on `(0,∞)` and
`F_*(∂_z²u) = 0` almost everywhere. -/
theorem aeMomentChain {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.pz u) z = 0) ∧
      (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z = 0) := by
  have hsm := AeData.smooth h
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hmemB := AeData.memAng2 h
  have hmemZ := AeData.memRad2 h
  -- ## the two slice-integrability inputs of the moment chain
  have hψsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * sg θ) Iθ :=
    fun z hz => slice_mul_sinCos2_integrable (α := α) hsm hmemB hz
      (AeData.dirZero h z) (AeData.dirPi h z)
  have hp1sl : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pz u z θ * sg θ) Iθ :=
    fun z hz => (Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite α u G h hz).1
  -- ## the moment relation for `∂_z u` (the box integrability of `∂_z²u` is a field of `AeData`)
  have hmr1 : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar (Work.Spaces.pz u) b - Work.Elliptic.Fstar (Work.Spaces.pz u) a
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r := by
    intro a b ha hab
    have h' := Work.FTS.EllipticEst.Blocks.moment_relation (Work.Spaces.pz u) hS.pz
      (Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi (Ψ := u) hsm hmemZ) hp1sl ha hab
    have hIcc : (∫ s in Set.Icc a b, ∫ θ in Iθ,
          Work.Spaces.pz (Work.Spaces.pz u) s θ * sg θ)
        = ∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) s := rfl
    have hconv : (∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) s)
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r := by
      rw [intervalIntegral.integral_of_le hab.le]
      exact (setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))).symm
    rw [hIcc, hconv] at h'
    linarith
  -- ## integrability of the second moment along the radius
  have hT2 : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u)) (Set.Icc a b) :=
    fun a b ha hab =>
      Work.FTS.EllipticEst.Endpt.integrableOn_fstar_pzIter2 (Ψ := u) hsm hmemZ a b ha hab
  -- ## continuity of `z ↦ F_*(∂_z u)(z)`: a constant plus the primitive of `F_*(∂_z²u)`
  have hcont1 : ContinuousOn (fun z => Work.Elliptic.Fstar (Work.Spaces.pz u) z)
      (Set.Ioi 0) := by
    intro z hz
    have hz0 : 0 < z := hz
    set a : ℝ := z / 2 with ha
    have ha0 : 0 < a := by rw [ha]; linarith
    have haz : a < z := by rw [ha]; linarith
    have haz2 : z < z + 1 := by linarith
    have hIntM2 : MeasureTheory.IntegrableOn
        (fun r => Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r) (Set.uIcc a (z + 1)) := by
      rw [Set.uIcc_of_le (by linarith : a ≤ z + 1)]
      exact hT2 a (z + 1) ha0 (by linarith)
    have hcontprim : ContinuousOn
        (fun x => ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r)
        (Set.uIcc a (z + 1)) :=
      intervalIntegral.continuousOn_primitive_interval hIntM2
    have hmem : Set.uIcc a (z + 1) ∈ 𝓝 z := by
      rw [Set.uIcc_of_le (by linarith : a ≤ z + 1)]
      exact Icc_mem_nhds haz haz2
    have hcontR : ContinuousWithinAt (fun x => Work.Elliptic.Fstar (Work.Spaces.pz u) a
        + ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r)
        (Set.Ioi 0) z :=
      continuousWithinAt_const.add (hcontprim.continuousAt hmem).continuousWithinAt
    have hrepr : ∀ x ∈ Set.Ioi 0, Work.Elliptic.Fstar (Work.Spaces.pz u) x
        = Work.Elliptic.Fstar (Work.Spaces.pz u) a
          + ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r := by
      intro x hx
      rcases lt_trichotomy a x with hlt | heq | hgt
      · linarith [hmr1 a x ha0 hlt]
      · subst heq; simp
      · have hh := hmr1 x a hx hgt
        rw [intervalIntegral.integral_symm] at hh
        linarith
    exact hcontR.congr_of_eventuallyEq
      (Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => hrepr x hx) (hrepr z hz)
  -- ## the backward difference quotient of `F_*(u)` converges to `F_*(∂_z u)`
  obtain ⟨hboxA, hsecA⟩ := absPzIter2SliceFacts (α := α) hsm hmemZ
  have hTdif : ∀ z : ℝ, 0 < z → Filter.Tendsto
      (fun hh : ℝ => (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Work.Elliptic.Fstar (Work.Spaces.pz u) z)) := by
    intro z hz
    have hev : ∀ᶠ hh : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), hh ∈ Set.Ioo (0 : ℝ) (z / 2) := by
      have h1 : Set.Iio (z / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
        nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (show (0 : ℝ) < z / 2 by linarith))
      filter_upwards [h1, self_mem_nhdsWithin] with hh hlt hgt
      exact ⟨hgt, hlt⟩
    have hlim := tendstoThetaIntervalAbsPzIter2 hboxA hsecA hz
    have hw : Filter.Tendsto (fun hh : ℝ =>
        (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
          - Work.Elliptic.Fstar (Work.Spaces.pz u) z)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hlimneg : Filter.Tendsto (fun hh : ℝ =>
          -∫ θ in Iθ, (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |sg θ|)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa using hlim.neg
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlimneg hlim ?_ ?_
      · filter_upwards [hev] with hh hhh
        have hb := difQuotSubDerivBound hsm hψsl hp1sl hz hhh.1 hhh.2
          (hboxA (z - hh) z (by linarith [hhh.1, hhh.2, hz]) (by linarith [hhh.1, hhh.2, hz]))
        exact (abs_le.mp hb).1
      · filter_upwards [hev] with hh hhh
        have hb := difQuotSubDerivBound hsm hψsl hp1sl hz hhh.1 hhh.2
          (hboxA (z - hh) z (by linarith [hhh.1, hhh.2, hz]) (by linarith [hhh.1, hhh.2, hz]))
        exact (abs_le.mp hb).2
    have := hw.add_const (Work.Elliptic.Fstar (Work.Spaces.pz u) z)
    simpa [sub_add_cancel] using this
  have hae1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.pz u) z = 0 :=
    aeZeroOfDifQuot (M₀ := fun z => Work.Elliptic.Fstar u z)
      (M₁ := fun z => Work.Elliptic.Fstar (Work.Spaces.pz u) z) (AeData.momU h) hTdif
  -- ## hence the first moment vanishes everywhere (continuity + a.e.-vanishing)
  have hpoint1 : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.pz u) z = 0 := by
    intro z hz
    refine Work.FTS.EllipticEst.Endpt.eq_zero_of_forall_intervalIntegral_eq_zero_of_continuousOn
      hz ?_ hcont1
    intro s w hs hsw
    have hae : (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.pz u) r)
        =ᵐ[volume.restrict (Set.Ioc s w)] (fun _ => (0 : ℝ)) :=
      MeasureTheory.ae_mono
        (MeasureTheory.Measure.restrict_mono (fun x hx => lt_of_lt_of_le hs (le_of_lt hx.1))
          le_rfl) hae1
    rw [intervalIntegral.integral_of_le hsw]
    rw [MeasureTheory.integral_congr_ae hae]
    simp
  -- ## hence the second moment vanishes a.e.
  have hzero2 : ∀ s t : ℝ, 0 < s → 0 < t →
      ∫ r in s..t, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r = 0 := by
    intro s t hs ht
    rcases le_total s t with hle | hle
    · rcases lt_or_eq_of_le hle with hlt | heq
      · have hh := hmr1 s t hs hlt
        rw [hpoint1 t (lt_trans hs hlt), hpoint1 s hs, sub_zero] at hh
        exact hh.symm
      · subst heq; simp
    · rcases lt_or_eq_of_le hle with hlt | heq
      · have hh := hmr1 t s ht hlt
        rw [hpoint1 s (lt_trans ht hlt), hpoint1 t ht, sub_zero] at hh
        rw [intervalIntegral.integral_symm, ← hh, neg_zero]
      · subst heq; simp
  have hInt2 : ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u)) volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hT2 a b ha hab
  have hae2 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z = 0 :=
    Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_forall_intervalIntegral_eq_zero hzero2 hInt2
  exact ⟨hpoint1, hae2⟩

theorem aeLeftTendsto : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro α u G h
  obtain ⟨hM1, hM2⟩ := aeMomentChain h
  have hsm := AeData.smooth h
  have hmemB := AeData.memAng2 h
  filter_upwards [hM2, AeData.momG h, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z hM2z hGz hz
  have hslice : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsm hz n
  have h2slice : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ := by
    have h0 := Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem (Ψ := u) hmemB hz
    refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show Work.Spaces.pthIter 2 u z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [show Work.Spaces.pthIter 2 u z θ
      = deriv (fun t => deriv (fun θ' => u z θ') t) θ from rfl]
  obtain ⟨L, hL⟩ := Work.FTS.EllipticEst.sliceLimitLeftExists (fun θ => u z θ) hslice h2slice
  -- the endpoint moment identity and the moment of the equation
  have hLzint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ) Iθ :=
    (Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite α u G h hz).2.2
  have hmom := Lzero1_moment_eq_neg_limit (α := α) hsm hmemB hz hLzint hL
  have hdecomp := fstar_G_eq h hz
  have hL0 : L = 0 := by
    rw [hGz, hM1 z hz, hM2z, hmom] at hdecomp
    linarith
  simpa [hL0] using hL

end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeSigmaSliceCoercive =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Small pointwise facts -/

/-- `sEta θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
private theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])


/-! ## Translating the `Honest` integrands into the shapes of the target -/







/-! ## The scalar core of the estimate -/

/-- The algebra of the estimate: the identity `R = A + hc - (η+6)B - 2η(1+η)W`, the Hardy
bound `W ≤ (1+η)^{-2}A + C₀B` and the positivity `0 ≤ hc` give
`A ≤ ((1+η)/(1-η))(R + K B)` with `K = η + 6 + 2η(1+η)C₀`. -/
private theorem arith_key {A R hc B W η C₀ : ℝ}
    (hid : R = (A + hc) - (η + 6) * B - 2 * η * (1 + η) * W)
    (hW : W ≤ (1 / (1 + η) ^ 2) * A + C₀ * B)
    (hhc : 0 ≤ hc) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    A ≤ (1 + η) / (1 - η) * (R + ((η + 6) + 2 * η * (1 + η) * C₀) * B) := by
  have h2η : 0 ≤ 2 * η * (1 + η) := by nlinarith
  have h1η : (1 + η) ≠ 0 := by linarith
  have hW' := mul_le_mul_of_nonneg_left hW h2η
  have hexp : 2 * η * (1 + η) * ((1 / (1 + η) ^ 2) * A + C₀ * B)
      = (2 * η / (1 + η)) * A + 2 * η * (1 + η) * C₀ * B := by
    field_simp
  have hstep : A ≤ R + ((η + 6) + 2 * η * (1 + η) * C₀) * B + (2 * η / (1 + η)) * A := by
    nlinarith [hid, hW', hexp, hhc]
  have hs2 : 1 - 2 * η / (1 + η) = (1 - η) / (1 + η) := by
    field_simp
    ring
  have hpos : 0 < 1 - 2 * η / (1 + η) := by
    rw [hs2]
    exact div_pos (by linarith) (by linarith)
  have hmain : (1 - 2 * η / (1 + η)) * A ≤ R + ((η + 6) + 2 * η * (1 + η) * C₀) * B := by
    linarith [hstep]
  have hmain' : A * (1 - 2 * η / (1 + η)) ≤ R + ((η + 6) + 2 * η * (1 + η) * C₀) * B := by
    rw [mul_comm A]
    exact hmain
  have hfin := (le_div_iff₀ hpos).mpr hmain'
  rwa [show (R + ((η + 6) + 2 * η * (1 + η) * C₀) * B) / (1 - 2 * η / (1 + η))
      = (1 + η) / (1 - η) * (R + ((η + 6) + 2 * η * (1 + η) * C₀) * B) by
    rw [hs2]
    field_simp] at hfin

/-! ## The target -/


end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.TL2.weakShiftTwoOne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Pieces.TL2

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Bookkeeping around the open quadrant -/

/-- **`z²·g` is `C^∞` on the open quadrant as soon as `g` is.**  (The open-quadrant version of
`SmoothOpen.zsq_mul`, which is not on this import cone.) -/
theorem smoothOpen_zsq_mul' {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * g z θ) := by
  have hz2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_fst (𝕜 := ℝ) (n := Work.Stability.smoothOrder)
      (s := Work.FTS.EllipticEst.Q0)).pow 2
  refine (hz2.mul hg).congr ?_
  intro p hp
  rfl

/-- **The source of the weak class is `C^∞` on the open quadrant.**  On `Q0` it agrees with
`bslOp α Ψ`, which is `C^∞` there by `SmoothOpen_bslOp_of_smoothOpen`. -/
theorem SmoothOpen_of_bslOp_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ) heq

/-- The shifted mixed slots, at the genuine smooth order: for `f` of class `C^∞` on the open
quadrant and `(z,θ)` in the open quadrant, `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`.
This is `D_z`-commutation with `D_θ^i` (`DthIterDzCommOpen`) followed by
`D_z^j (D_z g) = D_z^{j+1} g` and the local congruence of iterated `D_z` on the open quadrant. -/
theorem mixed_Dz_shift_eq {j i : ℕ} (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Work.FTS.EllipticEst.remov.Step.Qd :=
    Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hg i
  have hpt : (z, θ) ∈ Work.FTS.EllipticEst.remov.Step.Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Work.FTS.EllipticEst.remov.Step.DzIter_congr_of_isOpen Work.FTS.EllipticEst.remov.Step.isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Work.FTS.EllipticEst.remov.Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-! ## The pointwise shift bound for `HkIntegrand` -/

/-- **The pointwise `D_z`-shift bound at interior angles.**
Every slot of `HkIntegrand α (k-1) (D_z f)` is a slot of `HkIntegrand α k f` (up to the
commutation of `D_z` with `D_θ^i`), and each single slot is dominated by the whole integrand;
counting `k` radial and `k·k` mixed slots gives the factor `k + k²`. -/
theorem HkIntegrand_Dz_shift_le (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Work.FTS.EllipticEst.remov.Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2 := by
      unfold Work.FTS.EllipticEst.remov.Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Work.FTS.EllipticEst.remov.Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Work.FTS.EllipticEst.remov.Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_Dz_shift_eq f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Zsum k f z θ + Work.FTS.EllipticEst.remov.Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-! ## The two boundary angles of `Iθ`

`HkIntegrand` vanishes identically at `θ = 0` and at `θ = π/2`: the mixed slots carry the factor
`sin(2θ)` (their outermost `D_θ` is `sin(2θ)·∂_θ`, and the radial iterates of a function which
vanishes identically in `z` at a fixed angle vanish at that angle too), and the radial slots
carry the factor `Zu = w/sin(2θ)^{η/2}`. -/

/-- A `D_θ`-iterate of order `≥ 1` vanishes wherever `sin(2θ) = 0`. -/
theorem DthIter_eq_zero_of_sin_eq_zero {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsin : Real.sin (2 * θ) = 0) {i : ℕ} (hi : 1 ≤ i) :
    ∀ z : ℝ, Work.Spaces.DthIter i f z θ = 0 := by
  intro z
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, hsin, zero_mul]

/-- Radial iterates of a function that vanishes identically in `z` at a fixed angle vanish at
that angle. -/
theorem DzIter_eq_zero_at_theta {h : ℝ → ℝ → ℝ} {θ : ℝ} (hh : ∀ z, h z θ = 0) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j h z θ = 0 := by
  intro j
  induction j with
  | zero => intro z; exact hh z
  | succ j ih =>
      intro z
      show z * Work.Spaces.pz (Work.Spaces.DzIter j h) z θ = 0
      simp only [Work.Spaces.pz]
      have hzero : (fun z' => Work.Spaces.DzIter j h z' θ) = fun _ => (0 : ℝ) := funext ih
      rw [hzero, deriv_const]
      ring

/-- A mixed slot of angular order `i ≥ 1` vanishes wherever `sin(2θ) = 0`. -/
theorem mixed_eq_zero_of_sin_eq_zero {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsin : Real.sin (2 * θ) = 0) {i : ℕ} (hi : 1 ≤ i) (j : ℕ) (z : ℝ) :
    Work.Spaces.mixed j i f z θ = 0 :=
  DzIter_eq_zero_at_theta (DthIter_eq_zero_of_sin_eq_zero hsin hi) j z

/-- **`HkIntegrand` vanishes at both boundary angles**, for every `f`, `k` and `α`. -/
theorem HkIntegrand_eq_zero_of_sin_eq_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {θ : ℝ}
    (hsin : Real.sin (2 * θ) = 0) (z : ℝ) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have hZu : Work.FTS.EllipticEst.remov.Step.Zu z θ = 0 := by
    have h0 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [hsin]
      exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
    simp only [Work.FTS.EllipticEst.remov.Step.Zu, Work.Spaces.w]
    rw [h0, div_zero]
  have hZ : Work.FTS.EllipticEst.remov.Step.Zsum k f z θ = 0 := by
    unfold Work.FTS.EllipticEst.remov.Step.Zsum
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hZu]
    ring
  have hM : Work.FTS.EllipticEst.remov.Step.Msum α k f z θ = 0 := by
    unfold Work.FTS.EllipticEst.remov.Step.Msum
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine Finset.sum_eq_zero (fun j _ => ?_)
    by_cases hc : (1 ≤ i ∧ i + j ≤ k)
    · rw [if_pos hc, mixed_eq_zero_of_sin_eq_zero hsin hc.1 j z]
      ring
    · rw [if_neg hc]
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq, hZ, hM, add_zero]

/-- `HkIntegrand` vanishes at `θ = 0`. -/
theorem HkIntegrand_eq_zero_at_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α k f z 0 = 0 :=
  HkIntegrand_eq_zero_of_sin_eq_zero α k f (by simp) z

/-- `HkIntegrand` vanishes at `θ = π/2`. -/
theorem HkIntegrand_eq_zero_at_pi_half (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α k f z (Real.pi / 2) = 0 := by
  refine HkIntegrand_eq_zero_of_sin_eq_zero α k f ?_ z
  have h2 : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
  rw [h2, Real.sin_pi]

/-- **The pointwise `D_z`-shift bound on the closed quadrant `Iz × Iθ`.**  At interior angles
this is `HkIntegrand_Dz_shift_le`; at the two boundary angles both sides vanish; and at `z = 0`
both sides vanish for every angle. -/
theorem HkIntegrand_Dz_shift_le_Iz (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
        ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
  · subst h0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst α (k - 1) (Work.Spaces.Dz f) θ,
      Work.FTS.LocData.HkIntegrand_zero_fst α k f θ, mul_zero]
  · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθ0'
    · rw [← hθ0, HkIntegrand_eq_zero_at_zero α (k - 1) (Work.Spaces.Dz f) z,
        HkIntegrand_eq_zero_at_zero α k f z, mul_zero]
    · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).2 with hθpi | hθpi'
      · rw [hθpi, HkIntegrand_eq_zero_at_pi_half α (k - 1) (Work.Spaces.Dz f) z,
          HkIntegrand_eq_zero_at_pi_half α k f z, mul_zero]
      · exact HkIntegrand_Dz_shift_le α hk f hz0 ⟨hθ0', hθpi'⟩ hg

/-- **Membership form of the `D_z`-shift**: if `f` is `C^∞` on the open quadrant and in
`ℋ^k` (`k ≥ 1`), then `D_z f ∈ ℋ^{k-1}`.  This is the domination lemma
`Work.FTS.LocData.HkMem_of_majorant` applied to the pointwise bound
`HkIntegrand_Dz_shift_le_Iz`. -/
theorem HkMem_Dz_shift {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz f) := by
  refine Work.FTS.LocData.HkMem_of_majorant α (k - 1) (f := Work.Spaces.Dz f)
    (M := fun z θ => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
    ?_ ?_ ?_ ?_
  · exact (Work.FTS.EllipticEst.SmoothOpen.Dz hf).continuousOn_HkIntegrand α (k - 1)
  · intro z hz
    exact (hmem.1 z hz).const_mul _
  · show MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
    simpa only [MeasureTheory.integral_const_mul] using hmem.2.const_mul _
  · intro z hz θ hθ
    exact HkIntegrand_Dz_shift_le_Iz α hk f hf z hz θ hθ

/-! ## Commutation of `D_z` with `∂_θ²` -/

/-- **`∂_z` commutes with `∂_θ²` on the open quadrant**: Clairaut's theorem applied twice
(the first step with `∂_θ Ψ` as the function, the second by congruence on the open set). -/
theorem pz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) := by
  intro z θ hz hθ hlt
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      ContDiffAt ℝ 2 (Function.uncurry Ψ) (z', θ') := fun z' θ' hz' hθ' hlt' =>
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨ 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hlt'⟩))
  have hcd_pth : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) (z, θ) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pth Ψ)).mp
      (Work.FTS.EllipticEst.SmoothOpen.pth hΨ) 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (f := Work.Spaces.pth Ψ) hcd_pth
  have hagree : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pz (Work.Spaces.pth Ψ))
      (Work.Spaces.pth (Work.Spaces.pz Ψ)) :=
    fun z' θ' hz' hθ' hlt' => Work.Spaces.pz_pth_comm (f := Ψ) (hcd z' θ' hz' hθ' hlt')
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
      (fun p hp => by
        obtain ⟨z', θ'⟩ := p
        exact hagree z' θ' hp.1 hp.2.1 hp.2.2) hmem
  show Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact h1.trans h2

/-- **`D_z` commutes with `∂_θ²` on the open quadrant.**  Since `D_z f = z·∂_z f` and the
factor `z` does not depend on `θ`, the plain commutation `pz_pthIter_two_comm` gives the
identity for `D_z` as well. -/
theorem Dz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)) := by
  have hplain := pz_pthIter_two_comm hΨ
  have hmul : Work.Spaces.pth (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pz Ψ z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ
    rw [deriv_const_mul_field]
  have hstep : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ := by
    have h2 : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
        = Work.Spaces.pth (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ) := by
      rw [← hmul]
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
    rw [h2]
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
    rw [deriv_const_mul_field]
  intro z θ hz hθ hlt
  show z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ) z θ
  rw [hstep, hplain z θ hz hθ hlt]

/-! ## The assembly -/

/-- **The assembly of the shift, given the two moment conditions.**

All nine fields of `EllWeakPos α (k-1) (D_z F) (D_z Ψ)` are produced here except the two moment
conditions, which are supplied as explicit hypotheses:

* the equation is preserved because `bslOp` commutes with `D_z`
  (`Work.FTS.EllipticEst.TT.bslOp_DzIter_eq`);
* the Dirichlet data are preserved (`Work.FTS.EllipticEst.TT.DzIter_zero_at_zero`,
  `..._pi_half`);
* the smoothness is preserved (`SmoothOpen.DzIter`);
* the `ℋ`-membership of the three fields follows from the pointwise domination
  `HkIntegrand α (k-1) (D_z g) ≤ ((k:ℝ)+(k:ℝ)*(k:ℝ)) * HkIntegrand α k g`
  (`HkIntegrand_Dz_shift_le_Iz`, at the genuine `C^∞` order, via
  `Work.FTS.LocData.HkMem_of_majorant`) for `g ∈ {F, z²∂_zzΨ, ∂_θθΨ}`;
* the auxiliary identities needed are `pthIter 2 (D_z Ψ) = D_z (pthIter 2 Ψ)`
  (`Dz_pthIter_two_comm`) and `z² ∂_zz(D_z Ψ) = D_z (z² ∂_zzΨ)`
  (`Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm`), both pointwise on the open quadrant. -/
theorem EllWeakPos_DzIter_one_shift_of_moments {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hmomF : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0)
    (hmomΨ : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen h
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    SmoothOpen_of_bslOp_eq hSΨ (fun z θ hz hθ hlt => h.1 z hz θ hθ hlt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation commutes with `D_z`
    exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.1
  · -- the Dirichlet data at `θ = 0`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero
  · -- the Dirichlet data at `θ = π/2`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half
  · -- the source moment condition
    exact hmomF
  · -- the solution moment condition
    exact hmomΨ
  · -- smoothness on the open quadrant is preserved by `D_z`
    intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DzIter 1 Ψ)).mp
      (Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen_DzIter h 1) n
  · -- `D_z F ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz F) :=
      HkMem_Dz_shift hk hSF h.memF
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hmem
  · -- `z² ∂_zz(D_z Ψ) ∈ ℋ^{k-1}`
    have hG : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      smoothOpen_zsq_mul' (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      HkMem_Dz_shift hk hG h.memA
    have hEqOn := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ 1 0
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact (hEqOn (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      from ⟨hz, hθ⟩)).symm
  · -- `∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
      HkMem_Dz_shift hk (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2) h.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact Dz_pthIter_two_comm hSΨ z θ hz hθ.1 hθ.2
  · -- `ℋ^{k-1}`-honesty of the diagonal second-order term of the shifted datum:
    -- `z ∂_z∂_θθ(D_zΨ) = D_z (D_z ∂_θθΨ)`, and `∂_θθ` commutes with `D_z`.
    have hZ : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))) :=
      HkMem_Dz_shift hk
        (Work.FTS.EllipticEst.SmoothOpen.Dz
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2))
        h.memZPth2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hZ ?_
    intro z hz θ hθ
    show Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) z θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
    have hpe : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ :=
      Work.Spaces.pz_congr_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
        (Work.EllipticEst.H2W.pthIter2_DzIter_comm hSΨ 1) ⟨hz, hθ⟩
    rw [hpe, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    rfl


/-- **The `D_z`-shift of the weak hypothesis class.**

This is the instance of `EllWeakPos_DzIter_one_shift_of_moments` for `2 ≤ k`: here both moment
conditions are available from the *proved* lemmas `Fstar_DzIter_one_F_ge_two` (the `F`-half, via
the chain rule at `j = 0, 1` and the continuity of `F_*(D_z F)`) and `Fstar_DzIter_one_Psi` (the
`Ψ`-half, by the first-order difference-quotient argument), so the statement is complete. -/
theorem EllWeakPos_DzIter_one_shift_two_le {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  EllWeakPos_DzIter_one_shift_of_moments (by omega) h
    (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two hk h)
    (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_Psi (by omega) h)

theorem weakShiftTwoOne {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  EllWeakPos_DzIter_one_shift_two_le hk h

end Work.FTS.EllipticEst.Cores.Pieces.TL2
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.aeLeftLimitD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.H2W.Ae

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-! ## The angular slices of an `AeData` datum are `L¹` against `sinθcos²θ` -/

/-- `θ ↦ sinθcos²θ` is continuous. -/
private theorem continuous_sinCos2 : Continuous sg := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- `θ ↦ |sinθcos²θ|` is integrable on `Iθ`. -/
private theorem integrableOn_abs_sinCos2 :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |sg θ|) Iθ := by
  have h : MeasureTheory.IntegrableOn (fun θ : ℝ => |sg θ|) (Set.Icc 0 (Real.pi / 2)) :=
    continuous_sinCos2.abs.continuousOn.integrableOn_compact isCompact_Icc
  rwa [Work.Spaces.Iθ]

/-- **Slice integrability.**  For a datum whose `θ`-slices are bounded on the open interval
(which `HkMem α 0 (∂_θθu)` supplies through `Endpt.sliceBdd_of_hmB`) the product with the
bounded angular weight `sinθcos²θ` is integrable: at the two endpoints the *values* `u z 0` and
`u z (π/2)` vanish. -/
theorem slice_mul_sinCos2_integrableD {α : ℝ} {u : ℝ → ℝ → ℝ} {z : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u))
    (hz : 0 < z) (h0 : u z 0 = 0) (h1 : u z (Real.pi / 2) = 0) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * sg θ) Iθ := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB hsm hmemB hz
  have hSm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => u z θ * sg θ)
      (MeasureTheory.volume.restrict Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry u) hSm.continuousOn hz).mul
      continuous_sinCos2.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' (integrableOn_abs_sinCos2.const_mul C) haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Iθ from measurableSet_Icc) (fun θ hθI => ?_)
  have hb : |u z θ| ≤ C := by
    rcases eq_or_lt_of_le hθI.1 with hθ0 | hθ0
    · rw [← hθ0, h0]; simp only [mul_zero, abs_zero]; exact hCpos.le
    rcases eq_or_lt_of_le hθI.2 with hθ1 | hθ1
    · rw [hθ1, h1]; simp only [mul_zero, abs_zero]; exact hCpos.le
    · exact (hC θ ⟨hθ0, hθ1⟩).1
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)

/-! ## The endpoint moment identity in the weak class -/

/-- **The angular-moment identity.**  For `z > 0` the pairing of the angular operator
`Lzero1 (u z ·)` against the kernel function `sinθcos²θ` is minus the left endpoint limit of the
slice.  This is the form of `Endpt.Lzero1_integral_eq_neg_limit` in which the boundedness of the
slice and of its derivative required by the fundamental theorem of calculus is supplied directly
by `Endpt.sliceBdd_of_hmB`. -/
theorem Lzero1_moment_eq_neg_limitD {α : ℝ} {u : ℝ → ℝ → ℝ} {z L : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u)) (hz : 0 < z)
    (hLz : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ) Iθ)
    (hlim : Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ) = -L := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB hsm hmemB hz
  have hcd : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsm hz 2
  exact Work.FTS.EllipticEst.Honest.sliceMoment_eq_neg_limit hCpos.le hcd
    (fun θ hθ => hC θ hθ) hLz hlim

/-! ## The moment of the equation -/

/-- **The moment of the source.**  On the open quadrant the equation reads
`G = -(α²z²)∂_z²u - (α(5+α)z)∂_zu + Lzero u` (`Work.Elliptic.bslOp_apply`); taking the
`θ`-moment against `sinθcos²θ`, and using that `Lzero u` on a slice is `Lzero1 (u z ·)`, gives
the moment identity behind `AeSliceMomentIdent`. -/
theorem fstar_G_eqD {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Fstar G z
      = -(α ^ 2 * z ^ 2) * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z
        - (α * (5 + α) * z) * Work.Elliptic.Fstar (Work.Spaces.pz u) z
        + ∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ := by
  -- `Lzero` of the slice is `Lzero1` of the one-variable slice
  have hLzero : ∀ θ : ℝ, Work.Elliptic.Lzero u z θ
      = Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ := by
    intro θ
    simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero,
      Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  obtain ⟨h1, h2, h3⟩ := Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite α u G h hz
  -- ## the pointwise decomposition on the open interval
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ
        = G z θ * sg θ + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
          + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ) := by
    intro θ hθ
    have heq := AeData.eq h z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hkey : Work.Elliptic.Lzero u z θ = G z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + α * (5 + α) * z * Work.Spaces.pz u z θ := by linarith
    rw [← hLzero θ, hkey]
    ring
  have hae : (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ : ℝ => G z θ * sg θ + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
        + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hpt θ hθ)
  -- ## integrability of the source term
  have hGint : MeasureTheory.IntegrableOn (fun θ : ℝ => G z θ * sg θ) Iθ := by
    have hsub : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ
          - (α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
            + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ))) Iθ :=
      h3.sub ((h2.const_mul _).add (h1.const_mul _))
    refine hsub.congr ?_
    filter_upwards [hae] with θ hθ
    linarith
  -- ## the moment identity
  have hIntegral : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
      = Work.Elliptic.Fstar G z
        + α ^ 2 * z ^ 2 * (∫ θ in Iθ, Work.Spaces.pzIter 2 u z θ * sg θ)
        + α * (5 + α) * z * (∫ θ in Iθ, Work.Spaces.pz u z θ * sg θ) := by
    have h1' : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
        = ∫ θ in Iθ, (G z θ * sg θ
            + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
            + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
      MeasureTheory.integral_congr_ae hae
    have hsplit1 : (∫ θ in Iθ, (G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
          + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)))
        = (∫ θ in Iθ, (G z θ * sg θ
            + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)))
          + (∫ θ in Iθ, α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ))
        (g := fun θ : ℝ => α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ))
        (hGint.add (h2.const_mul (α ^ 2 * z ^ 2))) (h1.const_mul (α * (5 + α) * z))
    have hsplit2 : (∫ θ in Iθ, (G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)))
        = (∫ θ in Iθ, G z θ * sg θ)
          + (∫ θ in Iθ, α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)) :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => G z θ * sg θ)
        (g := fun θ : ℝ => α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ))
        hGint (h2.const_mul (α ^ 2 * z ^ 2))
    rw [h1', hsplit1, hsplit2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    rfl
  have hfinal : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
      = Work.Elliptic.Fstar G z
        + α ^ 2 * z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z
        + α * (5 + α) * z * Work.Elliptic.Fstar (Work.Spaces.pz u) z := by
    rw [hIntegral]
    rfl
  linarith [hfinal]

/-- **The angular-moment chain of the weak class `AeData`.**  For a datum `AeData α u G` the two
radial moments of the solution vanish: `F_*(∂_zu) ≡ 0` everywhere on `(0,∞)` and
`F_*(∂_z²u) = 0` almost everywhere. -/
theorem aeMomentChainD {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.pz u) z = 0) ∧
      (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z = 0) := by
  have hsm := AeData.smooth h
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hmemB := AeData.memAng2 h
  have hmemZ := AeData.memRad2 h
  -- ## the two slice-integrability inputs of the moment chain
  have hψsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * sg θ) Iθ :=
    fun z hz => slice_mul_sinCos2_integrableD (α := α) hsm hmemB hz
      (AeData.dirZero h z) (AeData.dirPi h z)
  have hp1sl : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pz u z θ * sg θ) Iθ :=
    fun z hz => (Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite α u G h hz).1
  -- ## the moment relation for `∂_z u` (the box integrability of `∂_z²u` is a field of `AeData`)
  have hmr1 : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar (Work.Spaces.pz u) b - Work.Elliptic.Fstar (Work.Spaces.pz u) a
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r := by
    intro a b ha hab
    have h' := Work.FTS.EllipticEst.Blocks.moment_relation (Work.Spaces.pz u) hS.pz
      (Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi (Ψ := u) hsm hmemZ) hp1sl ha hab
    have hIcc : (∫ s in Set.Icc a b, ∫ θ in Iθ,
          Work.Spaces.pz (Work.Spaces.pz u) s θ * sg θ)
        = ∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) s := rfl
    have hconv : (∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) s)
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r := by
      rw [intervalIntegral.integral_of_le hab.le]
      exact (setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))).symm
    rw [hIcc, hconv] at h'
    linarith
  -- ## integrability of the second moment along the radius
  have hT2 : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u)) (Set.Icc a b) :=
    fun a b ha hab =>
      Work.FTS.EllipticEst.Endpt.integrableOn_fstar_pzIter2 (Ψ := u) hsm hmemZ a b ha hab
  -- ## continuity of `z ↦ F_*(∂_z u)(z)`: a constant plus the primitive of `F_*(∂_z²u)`
  have hcont1 : ContinuousOn (fun z => Work.Elliptic.Fstar (Work.Spaces.pz u) z)
      (Set.Ioi 0) := by
    intro z hz
    have hz0 : 0 < z := hz
    set a : ℝ := z / 2 with ha
    have ha0 : 0 < a := by rw [ha]; linarith
    have haz : a < z := by rw [ha]; linarith
    have haz2 : z < z + 1 := by linarith
    have hIntM2 : MeasureTheory.IntegrableOn
        (fun r => Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r) (Set.uIcc a (z + 1)) := by
      rw [Set.uIcc_of_le (by linarith : a ≤ z + 1)]
      exact hT2 a (z + 1) ha0 (by linarith)
    have hcontprim : ContinuousOn
        (fun x => ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r)
        (Set.uIcc a (z + 1)) :=
      intervalIntegral.continuousOn_primitive_interval hIntM2
    have hmem : Set.uIcc a (z + 1) ∈ 𝓝 z := by
      rw [Set.uIcc_of_le (by linarith : a ≤ z + 1)]
      exact Icc_mem_nhds haz haz2
    have hcontR : ContinuousWithinAt (fun x => Work.Elliptic.Fstar (Work.Spaces.pz u) a
        + ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r)
        (Set.Ioi 0) z :=
      continuousWithinAt_const.add (hcontprim.continuousAt hmem).continuousWithinAt
    have hrepr : ∀ x ∈ Set.Ioi 0, Work.Elliptic.Fstar (Work.Spaces.pz u) x
        = Work.Elliptic.Fstar (Work.Spaces.pz u) a
          + ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r := by
      intro x hx
      rcases lt_trichotomy a x with hlt | heq | hgt
      · linarith [hmr1 a x ha0 hlt]
      · subst heq; simp
      · have hh := hmr1 x a hx hgt
        rw [intervalIntegral.integral_symm] at hh
        linarith
    exact hcontR.congr_of_eventuallyEq
      (Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => hrepr x hx) (hrepr z hz)
  -- ## the backward difference quotient of `F_*(u)` converges to `F_*(∂_z u)`
  obtain ⟨hboxA, hsecA⟩ := Work.FTS.EllipticEst.AngAWeak.absPzIter2SliceFacts (α := α) hsm hmemZ
  have hTdif : ∀ z : ℝ, 0 < z → Filter.Tendsto
      (fun hh : ℝ => (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Work.Elliptic.Fstar (Work.Spaces.pz u) z)) := by
    intro z hz
    have hev : ∀ᶠ hh : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), hh ∈ Set.Ioo (0 : ℝ) (z / 2) := by
      have h1 : Set.Iio (z / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
        nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (show (0 : ℝ) < z / 2 by linarith))
      filter_upwards [h1, self_mem_nhdsWithin] with hh hlt hgt
      exact ⟨hgt, hlt⟩
    have hlim := Work.FTS.EllipticEst.AngAWeak.tendstoThetaIntervalAbsPzIter2 hboxA hsecA hz
    have hw : Filter.Tendsto (fun hh : ℝ =>
        (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
          - Work.Elliptic.Fstar (Work.Spaces.pz u) z)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hlimneg : Filter.Tendsto (fun hh : ℝ =>
          -∫ θ in Iθ, (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |sg θ|)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa using hlim.neg
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlimneg hlim ?_ ?_
      · filter_upwards [hev] with hh hhh
        have hb := Work.FTS.EllipticEst.Dispatch.difQuotSubDerivBoundD hsm hψsl hp1sl hz hhh.1 hhh.2
          (hboxA (z - hh) z (by linarith [hhh.1, hhh.2, hz]) (by linarith [hhh.1, hhh.2, hz]))
        exact (abs_le.mp hb).1
      · filter_upwards [hev] with hh hhh
        have hb := Work.FTS.EllipticEst.Dispatch.difQuotSubDerivBoundD hsm hψsl hp1sl hz hhh.1 hhh.2
          (hboxA (z - hh) z (by linarith [hhh.1, hhh.2, hz]) (by linarith [hhh.1, hhh.2, hz]))
        exact (abs_le.mp hb).2
    have := hw.add_const (Work.Elliptic.Fstar (Work.Spaces.pz u) z)
    simpa [sub_add_cancel] using this
  have hae1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.pz u) z = 0 :=
    Work.FTS.EllipticEst.AngAWeak.aeZeroOfDifQuot (M₀ := fun z => Work.Elliptic.Fstar u z)
      (M₁ := fun z => Work.Elliptic.Fstar (Work.Spaces.pz u) z) (AeData.momU h) hTdif
  -- ## hence the first moment vanishes everywhere (continuity + a.e.-vanishing)
  have hpoint1 : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.pz u) z = 0 := by
    intro z hz
    refine Work.FTS.EllipticEst.Endpt.eq_zero_of_forall_intervalIntegral_eq_zero_of_continuousOn
      hz ?_ hcont1
    intro s w hs hsw
    have hae : (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.pz u) r)
        =ᵐ[volume.restrict (Set.Ioc s w)] (fun _ => (0 : ℝ)) :=
      MeasureTheory.ae_mono
        (MeasureTheory.Measure.restrict_mono (fun x hx => lt_of_lt_of_le hs (le_of_lt hx.1))
          le_rfl) hae1
    rw [intervalIntegral.integral_of_le hsw]
    rw [MeasureTheory.integral_congr_ae hae]
    simp
  -- ## hence the second moment vanishes a.e.
  have hzero2 : ∀ s t : ℝ, 0 < s → 0 < t →
      ∫ r in s..t, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r = 0 := by
    intro s t hs ht
    rcases le_total s t with hle | hle
    · rcases lt_or_eq_of_le hle with hlt | heq
      · have hh := hmr1 s t hs hlt
        rw [hpoint1 t (lt_trans hs hlt), hpoint1 s hs, sub_zero] at hh
        exact hh.symm
      · subst heq; simp
    · rcases lt_or_eq_of_le hle with hlt | heq
      · have hh := hmr1 t s ht hlt
        rw [hpoint1 s (lt_trans ht hlt), hpoint1 t ht, sub_zero] at hh
        rw [intervalIntegral.integral_symm, ← hh, neg_zero]
      · subst heq; simp
  have hInt2 : ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u)) volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hT2 a b ha hab
  have hae2 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z = 0 :=
    Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_forall_intervalIntegral_eq_zero hzero2 hInt2
  exact ⟨hpoint1, hae2⟩

theorem aeLeftLimitD : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro α u G h
  obtain ⟨hM1, hM2⟩ := aeMomentChainD h
  have hsm := AeData.smooth h
  have hmemB := AeData.memAng2 h
  filter_upwards [hM2, AeData.momG h, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z hM2z hGz hz
  have hslice : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsm hz n
  have h2slice : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ := by
    have h0 := Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem (Ψ := u) hmemB hz
    refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show Work.Spaces.pthIter 2 u z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [show Work.Spaces.pthIter 2 u z θ
      = deriv (fun t => deriv (fun θ' => u z θ') t) θ from rfl]
  obtain ⟨L, hL⟩ := Work.FTS.EllipticEst.sliceLimitLeftExists (fun θ => u z θ) hslice h2slice
  -- the endpoint moment identity and the moment of the equation
  have hLzint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ) Iθ :=
    (Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite α u G h hz).2.2
  have hmom := Lzero1_moment_eq_neg_limitD (α := α) hsm hmemB hz hLzint hL
  have hdecomp := fstar_G_eqD h hz
  have hL0 : L = 0 := by
    rw [hGz, hM1 z hz, hM2z, hmom] at hdecomp
    linarith
  simpa [hL0] using hL

end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.angL0weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# `angL0weak`: the level-`0` angular elliptic estimate in the weak class

Target: `L2Sq (∂θθU · W) ≤ C · L2Sq (S · W)` for `W = w / sin(2θ)^{η/2}` and `(S,U)` in the
weak hypothesis class (equation on the open quadrant, Dirichlet values, decay in `z`, both
`OrthCond`s, smoothness on the open quadrant, and `HkMem α 0 S` only — no honesty hypothesis on
the left hand side).

See `NOTES_angL0weak.md` (this directory) for the analysis of the statement (it is *true*, and
the naive counterexample routes — homogeneous/self-similar data, the "mixture" data of
`NOTES_slice_honest_open.md`, the adiabatic two-sided `z`-profile — are all blocked by the
"self-regulation" recorded there), for the route (the paper's Step 2: test against `-∂θθU·ρ` and
control `I₁ … I₅`), for the review-driven correction that the analytic inputs must be stated as
*pairings* (not norms), and for the remaining gaps (weak-class Step 1, the weak-class `I₁`/`I₄`
pairing bounds, and the junk/totalisation layer).

## Contents of this file

* `pthIter_two_eq` — the pointwise identity behind the whole computation:
  `∂θθU = -(bslOp α U) - (α²z²)∂zzU - (α(5+α)z)∂zU + ∂θ(tanθ·U) - 6U` on the open quadrant.
  Every bound of Step 2 is a consequence of this identity together with estimates for the four
  displayed terms.
* `weakBarBound` — the weak-class pointwise bound on the slice profile `Ψ̄ = u / cos θ` which the
  `I₄` analysis consumes, obtained from `weakSliceDerivBound`.
-/

/-- **The pointwise identity of the whole Step 2 computation.**  On the open quadrant,

`∂θθU = -(bslOp α U) - (α²z²)·∂_zzU - (α(5+α)z)·∂_zU + ∂_θ(tanθ·U) - 6U`.

Indeed `bslOp α U = -(α²z²)∂zzU - (α(5+α)z)∂zU + Lzero U` and
`Lzero U = -∂θθU + ∂θ(tanθ·U) - 6U`. -/
theorem pthIter_two_eq (α : ℝ) (U : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 U z θ
      = -(Work.Elliptic.bslOp α U z θ) - (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 U z θ
        - (α * (5 + α) * z) * Work.Spaces.pz U z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * U z θ) z θ - 6 * U z θ := by
  simp only [Work.Elliptic.bslOp, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  ring




end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.low_order_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-!
# `low_order_le`

The low-order angular terms `∫∫ w²((∂_θΨ)² + Ψ²)` of a datum of the weak class
`TT.EllWeakPos α k F Ψ` are controlled by the `η`-weighted second angular derivative
`∫∫ w² (∂_θθΨ)² sin(2θ)^{-η}`.

The proof is slicewise.  For a single slice `u = Ψ z ·`:

* `∫ (u'')² sin(2θ)^{-η} < ∞` (the `i = 0` slot of `HkMem`), which also bounds `u` and `u'`
  uniformly (`Honest.SliceBddSqSigma`), so that `u σ` is honest;
* the moment condition `∫ u sinθcos²θ = 0` (a field of `EllWeakPos`) and the continuity of `u`
  on the open interval produce an **interior zero** `θ₁` of `u` (a constant sign would make the
  moment integral strictly signed);
* the right endpoint has limit `0`, so Rolle's theorem on `[θ₁, π/2]` produces an interior
  critical point `θ₀` of `u`;
* the fundamental theorem of calculus from `θ₀` bounds `(u')² ≤ (π/2)∫(u'')²`, and from `θ₁`
  bounds `|u| ≤ √((π/2)∫(u'')²)·|θ - θ₁|`.  Integrating gives the constant
  `(π/2)² + (π/2)⁴ < 20`.

No left endpoint limit is used, so the argument applies to the whole weak class.
-/

/-- `sin θ cos²θ > 0` on the open interval `(0, π/2)`. -/
theorem sinCos2_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.Elliptic.sinCos2 θ := by
  have h0 : (0 : ℝ) < θ := hθ.1
  have h1 : θ < Real.pi / 2 := hθ.2
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  rw [Work.Elliptic.sinCos2]
  exact mul_pos hsin (pow_pos hcos 2)

/-- A continuous function on the open interval with no zero there has constant sign. -/
theorem sign_const_of_no_zero {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ ≠ 0) :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < u θ) ∨
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ < 0) := by
  have hq : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rcases lt_or_gt_of_ne (a := (0 : ℝ)) (b := u (Real.pi / 4))
    (Ne.symm (hne (Real.pi / 4) hq)) with hpos | hneg
  · left
    intro θ hθ
    by_contra hcon
    rw [not_lt] at hcon
    have hneg' : u θ < 0 := lt_of_le_of_ne hcon (hne θ hθ)
    have hiv := IsPreconnected.intermediate_value isPreconnected_Ioo hθ hq hcont
      (f := u) ⟨le_of_lt hneg', le_of_lt hpos⟩
    obtain ⟨x, hx, hxu⟩ := hiv
    exact hne x hx hxu
  · right
    intro θ hθ
    by_contra hcon
    rw [not_lt] at hcon
    have hpos' : 0 < u θ := lt_of_le_of_ne hcon (Ne.symm (hne θ hθ))
    have hiv := IsPreconnected.intermediate_value isPreconnected_Ioo hq hθ hcont
      (f := u) ⟨le_of_lt hneg, le_of_lt hpos'⟩
    obtain ⟨x, hx, hxu⟩ := hiv
    exact hne x hx hxu

/-- **The moment condition gives an interior zero.**  A continuous function on `(0, π/2)` which
is integrable against `sinθcos²θ` and has vanishing angular moment must vanish somewhere in the
open interval (otherwise it has a constant sign and the moment integral is strictly signed). -/
theorem exists_interior_zero_of_moment {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : IntegrableOn (fun θ => u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, u θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∃ θ₁ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ₁ = 0 := by
  by_contra h
  push_neg at h
  have hsupp_measure : ∀ v : ℝ → ℝ, Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Function.support v →
      0 < volume (Function.support v ∩ Work.Spaces.Iθ) := by
    intro v hsub
    have h1 : volume (Set.Ioo (0 : ℝ) (Real.pi / 2))
        ≤ volume (Function.support v ∩ Work.Spaces.Iθ) :=
      measure_mono fun x hx => ⟨hsub hx, ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
    refine lt_of_lt_of_le ?_ h1
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
  rcases sign_const_of_no_zero hcont h with hpos | hneg
  · have hle : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => u θ * Work.Elliptic.sinCos2 θ) :=
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ =>
        le_of_lt (mul_pos (hpos θ hθ) (sinCos2_pos_of_mem_Ioo hθ))
    have hsupp : 0 < volume (Function.support (fun θ => u θ * Work.Elliptic.sinCos2 θ)
        ∩ Work.Spaces.Iθ) :=
      hsupp_measure _ fun θ hθ => by
        rw [Function.mem_support]
        exact ne_of_gt (mul_pos (hpos θ hθ) (sinCos2_pos_of_mem_Ioo hθ))
    have hpos' := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hle hint).mpr hsupp
    rw [hmom] at hpos'
    exact lt_irrefl 0 hpos'
  · have hle : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => -(u θ * Work.Elliptic.sinCos2 θ)) :=
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ =>
        le_of_lt (neg_pos.mpr (mul_neg_of_neg_of_pos (hneg θ hθ) (sinCos2_pos_of_mem_Ioo hθ)))
    have hsupp : 0 < volume (Function.support (fun θ => -(u θ * Work.Elliptic.sinCos2 θ))
        ∩ Work.Spaces.Iθ) :=
      hsupp_measure _ fun θ hθ => by
        rw [Function.mem_support]
        exact ne_of_gt
          (neg_pos.mpr (mul_neg_of_neg_of_pos (hneg θ hθ) (sinCos2_pos_of_mem_Ioo hθ)))
    have hneg' := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hle hint.neg).mpr hsupp
    rw [MeasureTheory.integral_neg, hmom, neg_zero] at hneg'
    exact lt_irrefl 0 hneg'

/-- Continuity on `[θ₁, π/2]` from continuity on the open interval, the right limit `0` and the
value `0` at `π/2`. -/
theorem continuousOn_Icc_of_tendsto {u : ℝ → ℝ} {a : ℝ}
    (hcont : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hπ : Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hval : u (Real.pi / 2) = 0) (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ContinuousOn u (Set.Icc a (Real.pi / 2)) := by
  intro x hx
  rcases lt_or_eq_of_le hx.2 with h | h
  · exact (hcont.continuousAt
      (isOpen_Ioo.mem_nhds ⟨lt_of_lt_of_le ha.1 hx.1, h⟩)).continuousWithinAt
  · subst h
    rw [ContinuousWithinAt, hval]
    have hsub : Set.Icc a (Real.pi / 2) ⊆ Set.Ico a (Real.pi / 2) ∪ {Real.pi / 2} := by
      intro y hy
      rcases eq_or_lt_of_le hy.2 with h2 | h2
      · exact Or.inr h2
      · exact Or.inl ⟨hy.1, h2⟩
    have hpure : Tendsto u (pure (Real.pi / 2)) (nhds 0) := by
      have h := tendsto_pure_nhds u (Real.pi / 2)
      rwa [hval] at h
    have h1 : Tendsto u (nhdsWithin (Real.pi / 2) (Set.Ico a (Real.pi / 2))
        ⊔ pure (Real.pi / 2)) (nhds 0) :=
      Tendsto.sup (hπ.mono_left (nhdsWithin_mono _ fun y hy => hy.2)) hpure
    have h2 : nhdsWithin (Real.pi / 2) (Set.Icc a (Real.pi / 2))
        ≤ nhdsWithin (Real.pi / 2) (Set.Ico a (Real.pi / 2)) ⊔ pure (Real.pi / 2) := by
      have h3 := nhdsWithin_mono (Real.pi / 2) hsub
      rwa [nhdsWithin_union, nhdsWithin_singleton] at h3
    exact h1.mono_left h2

/-- **The `(u')²`-bound from an interior critical point.**  On the open interval, `(u')²` is
bounded by `(π/2)·∫(u'')²` as soon as `u'` vanishes somewhere inside. -/
theorem slice_deriv_bound {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hcrit : deriv u θ₀ = 0)
    (h2 : IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2
      ≤ (Real.pi / 2) * (∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2) := by
  have hder1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hv_cont : ContinuousOn (fun s => deriv (fun t => deriv u t) s)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h2' : ContDiffOn ℝ 0 (deriv (fun t => deriv u t))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hder1.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
    exact h2'.continuousOn
  -- integrability of `(u'')²` on the slice
  have hE2 : IntegrableOn (fun s => (deriv (fun t => deriv u t) s) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' h2
      ((measurable_deriv (fun t => deriv u t)).pow_const 2).aestronglyMeasurable ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 := Work.FTS.EllipticEst.Honest.one_le_sEta hθ
    nlinarith [sq_nonneg (deriv (fun t => deriv u t) θ)]
  -- the derivative of `deriv u` is `deriv (deriv u)`
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t => deriv u t) x) x := by
    intro x hx
    exact ((hder1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  -- fundamental theorem of calculus for `deriv u`
  have hftc : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∫ s in a..b, deriv (fun t => deriv u t) s = deriv u b - deriv u a := by
    intro a b hab hsub
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ ?_
    · exact hder1.continuousOn.mono hsub
    · intro x hx
      exact hderiv x (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    · exact (hv_cont.mono hsub).intervalIntegrable_of_Icc hab
  -- monotonicity of the energy along subintervals
  have hmono : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (∫ s in a..b, (deriv (fun t => deriv u t) s) ^ 2)
        ≤ ∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2 := by
    intro a b hab hsub
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.setIntegral_mono_set hE2
      (Eventually.of_forall fun s => sq_nonneg _)
      (Eventually.of_forall fun s hs => by
        obtain ⟨h1, h2⟩ := hsub ⟨le_of_lt hs.1, hs.2⟩
        exact ⟨le_of_lt h1, le_of_lt h2⟩)
  intro θ hθ
  rcases le_total θ₀ θ with hle | hle
  · have hsub : Set.Icc θ₀ θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hθ₀.1 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    have hdiff : deriv u θ - deriv u θ₀ = ∫ s in θ₀..θ, deriv (fun t => deriv u t) s :=
      (hftc hle hsub).symm
    have hcs := Work.FTS.EllipticEst.TanTheta.sq_integral_le
      (fun s => deriv (fun t => deriv u t) s) θ₀ θ hle (hv_cont.mono hsub)
    have hnn : 0 ≤ ∫ s in θ₀..θ, (deriv (fun t => deriv u t) s) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hle fun s => sq_nonneg _
    calc (deriv u θ) ^ 2 = (deriv u θ - deriv u θ₀) ^ 2 := by rw [hcrit, sub_zero]
      _ = (∫ s in θ₀..θ, deriv (fun t => deriv u t) s) ^ 2 := by rw [hdiff]
      _ ≤ (θ - θ₀) * (∫ s in θ₀..θ, (deriv (fun t => deriv u t) s) ^ 2) := hcs
      _ ≤ (Real.pi / 2) * (∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2) :=
          mul_le_mul (by linarith [hθ.2, hθ₀.1]) (hmono hle hsub) hnn (by positivity)
  · have hsub : Set.Icc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hθ₀.2⟩
    have hdiff : deriv u θ₀ - deriv u θ = ∫ s in θ..θ₀, deriv (fun t => deriv u t) s :=
      (hftc hle hsub).symm
    have hcs := Work.FTS.EllipticEst.TanTheta.sq_integral_le
      (fun s => deriv (fun t => deriv u t) s) θ θ₀ hle (hv_cont.mono hsub)
    have hnn : 0 ≤ ∫ s in θ..θ₀, (deriv (fun t => deriv u t) s) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hle fun s => sq_nonneg _
    calc (deriv u θ) ^ 2 = (deriv u θ - deriv u θ₀) ^ 2 := by rw [hcrit, sub_zero]
      _ = (∫ s in θ..θ₀, deriv (fun t => deriv u t) s) ^ 2 := by
          rw [← hdiff]; ring
      _ ≤ (θ₀ - θ) * (∫ s in θ..θ₀, (deriv (fun t => deriv u t) s) ^ 2) := hcs
      _ ≤ (Real.pi / 2) * (∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2) :=
          mul_le_mul (by linarith [hθ₀.2, hθ.1]) (hmono hle hsub) hnn (by positivity)

/-- **The `u²`-bound from an interior zero.**  If `u` vanishes at an interior point and
`(u')² ≤ (π/2)∫(u'')²` on the slice, then `u² ≤ (π/2)³∫(u'')²`. -/
theorem slice_value_bound {u : ℝ → ℝ} {θ₁ : ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hθ₁ : θ₁ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hzero : u θ₁ = 0)
    (h1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2
      ≤ (Real.pi / 2) * (∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2)) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2
      ≤ (Real.pi / 2) ^ 3 * (∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2) := by
  set E : ℝ := ∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2 with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact MeasureTheory.integral_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun s => (deriv (fun t => deriv u t) s) ^ 2) fun s => sq_nonneg _
  have hC : 0 ≤ (Real.pi / 2) * E := mul_nonneg (by positivity) hE0
  have hseed : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 ≤ (Real.pi / 2) * E :=
    fun θ hθ => by rw [hE]; exact h1 θ hθ
  have hder1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  -- the norm bound on the difference quotient
  have hstep : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |∫ s in a..b, deriv u s| ≤ Real.sqrt ((Real.pi / 2) * E) * |b - a| := by
    intro a b hab hsub
    refine intervalIntegral.norm_integral_le_of_norm_le_const (f := fun s => deriv u s)
      (a := a) (b := b) (C := Real.sqrt ((Real.pi / 2) * E)) fun s hs => ?_
    rw [Set.uIoc_of_le hab] at hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨(hsub ⟨le_of_lt hs.1, hs.2⟩).1, (hsub ⟨le_of_lt hs.1, hs.2⟩).2⟩
    rw [Real.norm_eq_abs]
    calc |deriv u s| = Real.sqrt ((deriv u s) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((Real.pi / 2) * E) := Real.sqrt_le_sqrt (hseed s hs')
  -- fundamental theorem of calculus for `u`
  have hftc : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∫ s in a..b, deriv u s = u b - u a := by
    intro a b hab hsub
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ ?_
    · exact hsm.continuousOn.mono hsub
    · intro x hx
      exact ((hsm.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩))).hasDerivAt
    · exact hder1.continuousOn.mono hsub |>.intervalIntegrable_of_Icc hab
  intro θ hθ
  rcases le_total θ₁ θ with hle | hle
  · have hsub : Set.Icc θ₁ θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hθ₁.1 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    have habs : |u θ| ≤ Real.sqrt ((Real.pi / 2) * E) * (θ - θ₁) := by
      calc |u θ| = |∫ s in θ₁..θ, deriv u s| := by rw [hftc hle hsub, hzero, sub_zero]
        _ ≤ Real.sqrt ((Real.pi / 2) * E) * |θ - θ₁| := hstep hle hsub
        _ = Real.sqrt ((Real.pi / 2) * E) * (θ - θ₁) := by
            rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ - θ₁)]
    have hkey : (u θ) ^ 2 ≤ ((Real.pi / 2) * E) * (θ - θ₁) ^ 2 := by
      have h2 := pow_le_pow_left₀ (abs_nonneg (u θ)) habs 2
      rwa [mul_pow, Real.sq_sqrt hC, sq_abs] at h2
    calc (u θ) ^ 2 ≤ ((Real.pi / 2) * E) * (θ - θ₁) ^ 2 := hkey
      _ ≤ ((Real.pi / 2) * E) * (Real.pi / 2) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          nlinarith [hθ.2, hθ₁.1]
      _ = (Real.pi / 2) ^ 3 * E := by ring
  · have hsub : Set.Icc θ θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hθ₁.2⟩
    have habs : |u θ| ≤ Real.sqrt ((Real.pi / 2) * E) * (θ₁ - θ) := by
      calc |u θ| = |∫ s in θ..θ₁, deriv u s| := by rw [hftc hle hsub, hzero, zero_sub, abs_neg]
        _ ≤ Real.sqrt ((Real.pi / 2) * E) * |θ₁ - θ| := hstep hle hsub
        _ = Real.sqrt ((Real.pi / 2) * E) * (θ₁ - θ) := by
            rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ₁ - θ)]
    have hkey : (u θ) ^ 2 ≤ ((Real.pi / 2) * E) * (θ₁ - θ) ^ 2 := by
      have h2 := pow_le_pow_left₀ (abs_nonneg (u θ)) habs 2
      rwa [mul_pow, Real.sq_sqrt hC, sq_abs] at h2
    calc (u θ) ^ 2 ≤ ((Real.pi / 2) * E) * (θ₁ - θ) ^ 2 := hkey
      _ ≤ ((Real.pi / 2) * E) * (Real.pi / 2) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          nlinarith [hθ₁.2, hθ.1]
      _ = (Real.pi / 2) ^ 3 * E := by ring

/-- **The slice facts supplied by the weak class.**  For `z > 0`: the slice is `C²` on the open
interval, its `η`-weighted second derivative is integrable, `Ψ z · · sinθcos²θ` is integrable,
the angular moment vanishes, and the Dirichlet value at `π/2` is `0`. -/
theorem slice_class_facts {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    IntegrableOn (fun θ => (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
    IntegrableOn (fun θ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Elliptic.sinCos2 θ) = 0 ∧
    Ψ z (Real.pi / 2) = 0 := by
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hsm2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Honest.contDiffOn_slice Ψ hz (hwk.smooth 2)
  have hB2p : IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice ((hS.pth).pth) hwk.memB 0 (Nat.zero_le k) hz
  have hB2 : IntegrableOn (fun θ => (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using hB2p
  refine ⟨hsm2, hB2, ?_, ?_, hwk.pi_half z⟩
  · -- `Ψ z · · sinθcos²θ` is integrable (from the boundedness of the slice)
    obtain ⟨C, hC0, hC⟩ := Work.FTS.EllipticEst.Honest.SliceBddSqSigma hsm2 hB2
    have hσ : IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.remov.ws_sEta_integrableOn
    refine MeasureTheory.Integrable.mono' (hσ.const_mul C) ?_ ?_
    · have h1 : AEStronglyMeasurable (fun θ => Ψ z θ) (volume.restrict Work.Spaces.Iθ) :=
        Work.FTS.EllipticEst.remov.ws_aesm_slice hS hz
      have h2 : AEStronglyMeasurable (fun θ => Work.Elliptic.sinCos2 θ)
          (volume.restrict Work.Spaces.Iθ) :=
        (by simp only [Work.Elliptic.sinCos2]; fun_prop :
          Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ).aestronglyMeasurable
      exact h1.mul h2
    · refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => ?_
      have hsin0 : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
      have hsc0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
        rw [Work.Elliptic.sinCos2]; exact mul_nonneg hsin0 (sq_nonneg _)
      have hσ0 : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
        Work.FTS.EllipticEst.Honest.sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsc0]
      have hsc1 : Work.Elliptic.sinCos2 θ ≤ 1 := by
        rw [Work.Elliptic.sinCos2]
        have hc : Real.cos θ ^ 2 ≤ 1 := by
          nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ, sq_nonneg (Real.cos θ)]
        nlinarith [Real.sin_le_one θ, hsin0, hc]
      have hsc2 : Work.Elliptic.sinCos2 θ ≤ Work.FTS.EllipticEst.sEta θ :=
        le_trans hsc1 (Work.FTS.EllipticEst.Honest.one_le_sEta hθ)
      calc |Ψ z θ| * Work.Elliptic.sinCos2 θ ≤ C * Work.Elliptic.sinCos2 θ :=
            mul_le_mul_of_nonneg_right (hC θ hθ).2 hsc0
        _ ≤ C * Work.FTS.EllipticEst.sEta θ := mul_le_mul_of_nonneg_left hsc2 hC0.le
  · have h := hwk.orthPsi z hz
    simpa only [Work.Elliptic.Fstar] using h

/-- A.e. strong measurability in `z` of the angular energy of `∂_θθΨ`. -/
theorem aesm_slice_second {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iz) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hS2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := (hS.pth).pth
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pthIter 2 Ψ p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hS2.continuousOn.pow 2
  have hcontσ : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := Work.FTS.EllipticEst.remov.ws_contOn_sEta
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.pthIter 2 Ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hcont2.mul hcontσ)
  have h := hjoint.integral_prod_right' (ν := volume.restrict Work.Spaces.Iθ)
  simpa only [Function.uncurry] using h

/-- Integrability in `z` of `w(z)²·∫_θ (∂_θθΨ)² σ`: the `i = 0` slot of `HkMem`. -/
theorem integrable_w_sq_thetaEnergy {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      Work.Spaces.Iz := by
  have haesm : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (volume.restrict Work.Spaces.Iz) := by
    have hw : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
      simp only [Work.Spaces.w, div_eq_mul_inv]
      fun_prop
    exact hw.aestronglyMeasurable.mul (aesm_slice_second hwk.smooth)
  refine MeasureTheory.Integrable.mono' hwk.memB.2 haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · rw [← h0, show Work.Spaces.w (0 : ℝ) = 0 by simp [Work.Spaces.w]]
    have hz0' : (0 : ℝ) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 2 Ψ 0 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) = 0 := by
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    rw [Real.norm_eq_abs, hz0', abs_zero]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ _ =>
      Work.Spaces.HkIntegrand_nonneg α k _ 0 θ
  · -- the pointwise domination by the `i = 0` slot of the integrand
    have hθint : IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.remov.ws_slot_slice
        ((Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth).pth.pth) hwk.memB 0
        (Nat.zero_le k) hz0
    have hnonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
    have hw0 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg hw0 hnonneg)]
    calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
          rw [MeasureTheory.integral_const_mul]
      _ = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
          rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq_Iθ α _ hθ]
          ring
      _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 Ψ) z θ := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
            (hwk.memB.1 z (Set.mem_Ici.mpr hz0.le)) ?_
          exact Eventually.of_forall fun θ => by
            rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α (Work.Spaces.pthIter 2 Ψ) z θ]
            exact Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 Ψ) z θ 0
              (Nat.zero_le k)

end




end Work.FTS.EllipticEst.TT.ESW
end
-- ===== merged: Submission.Work.FTS.EllipticEst.UopHk.Gsing_cDiff_kp1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.UopHk

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# `Gsing` is `C^{k+1}` and `Gbar` is `C^k` for a source in the interior class `RegQ α k`

This module proves `Work.FTS.EllipticEst.UopHk.Gsing_cDiff_kp1`: for `0 < α ≤ 1`, `k ≥ 2` and
a source `F` in the interior class `RegQ α k F` (`C^∞` on the open quadrant, honest
weighted `ℋ^k`-membership, boundary traces),

* `Work.Elliptic.Gsing α F` is `C^{k+1}` on `(0,∞)`, and
* `Work.Elliptic.Gbar α F` is `C^k` on `(0,∞)`.

## The route

The two functions are

`Gsing = Gstar + Gbar`, `Gstar = -(1/(4α)) L₁₂(F)`, `Gbar z = -(3/(4α)) z^{-5/α} J(z)`,

with `L₁₂(F)(z) = 3∫_z^∞ F_*(r)/r dr` and `J(z) = ∫_0^z s^{(5-α)/α} F_*(s) ds`.

The single analytic input is the sharp interior regularity of the angular moment
`F_* = ∫_θ F sinθcos²θ dθ` supplied by `GsingFactsInterior`: `F_*` is `C^{k-1}` on `(0,∞)`, with
`deriv F_* = F_*(D_z F)/z`.  From it:

* the integrand `s ↦ s^{(5-α)/α} F_*(s)` of `J` is `C^{k-1}`, so `J ∈ C^k`
  (`contDiffOn_Jfun_k`; this is the sharp order — the monomial factor costs only the `1/s` of
  the exponent);
* `Gbar = Abar · J` with `Abar = -(3/(4α)) z^{-5/α}` smooth, hence `Gbar ∈ C^k`;
* the first integral of the ODE for `Gsing` is `α z ∂_z Gsing = -5 Gbar` (`Gsing_deriv_rel`),
  i.e. `∂_z Gsing = -5 Gbar/(α z)`, a `C^k` function on `(0,∞)`.  Since `Gsing` is
  differentiable at every `z > 0` with that derivative, the one-order-gain lemma
  `contDiffOn_succ_of_hasDerivAt` upgrades `Gsing` to `C^{k+1}`.

This is exactly one order more than `Gbar`: the extra order comes from the first-order relation
`α z ∂_z Gsing = -5 Gbar`, i.e. from the cancellation of the `F_*`-terms between `Gstar` and
`Gbar` (`Gsing` solves `α²z²y'' + α(5+α)zy' = (15/4)F_*`).
-/




end Work.FTS.EllipticEst.UopHk
end
-- ===== merged: Submission.Work.FTS.H2.prodW_interior_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The Leibniz calculus of `∂_z^k D_θ^j` in the interior class `SmoothQuad`

`Work.FTS.LocData.SmoothQuad` is genuine `C^∞` on the open quadrant
`z > -1, 0 < θ < π/2`; on this class the `θ`-Leibniz rule is
`Work.FTS.LocData.DthIter_mul_smoothQuad` and the `z`-Leibniz rule is
`Work.FTS.H2.Q.pzIter_mul_local_sm`.  Combining the two gives the mixed Leibniz expansion of a
product, which is the `SmoothQuad` counterpart of `Work.Spaces.pz_DthIter_mul_eq` (whose
hypothesis is `SmoothInt`). -/

/-- The `z`-slices of the `D_θ`-iterates of a `SmoothQuad` function are `C^∞` at every
`z ∈ [0,∞)`, for `θ ∈ (0,π/2)`. -/
theorem sqm_dthIter_zslice_contDiffAt {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (a : ℕ) :
    ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Work.Spaces.DthIter a f z' θ) z := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hzIoi : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  exact ((hf.DthIter a).curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hzIoi)

/-- At a fixed angle `θ ∈ (0,π/2)` the `D_θ`-Leibniz expansion of a product agrees with
`D_θ^j (f g)` on a neighbourhood of every `z ∈ [0,∞)`. -/
theorem sqm_DthIter_mul_zslice_eventuallyEq (j : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (fun z' => Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ)
          * (Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ)) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hzIoi : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  filter_upwards [isOpen_Ioi.mem_nhds hzIoi] with z' hz'
  exact Work.FTS.LocData.DthIter_mul_smoothQuad j f g hθ (hf.curry_θ hz') (hg.curry_θ hz')

/-- **The mixed Leibniz identity in the interior class**: for `SmoothQuad` functions `f, g`,
every `z ∈ [0,∞)` and `θ ∈ (0,π/2)`,
`∂_z^k D_θ^j (f g) = ∑_{a≤j} ∑_{c≤k} C(j,a) C(k,c) ∂_z^c D_θ^a f · ∂_z^{k-c} D_θ^{j-a} g`. -/
theorem sqm_pz_DthIter_mul_eq (k j : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
        = ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
            ((j.choose a : ℝ) * (k.choose c : ℝ))
              * (Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ
                  * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ) := by
  intro z hz θ hθ
  have hslice : ∀ (h : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad h → ∀ a : ℕ,
      ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Work.Spaces.DthIter a h z' θ) z :=
    fun h hh a => sqm_dthIter_zslice_contDiffAt hh hθ hz a
  have hleib := sqm_DthIter_mul_zslice_eventuallyEq j f g hf hg hz hθ
  rw [Work.Spaces.pzIter_eq_iteratedDeriv k _ z θ, Filter.EventuallyEq.iteratedDeriv_eq k hleib]
  have hsum := Work.Spaces.iteratedDeriv_sum_const_mul (s := Finset.range (j + 1))
    (c := fun a => (j.choose a : ℝ))
    (F := fun a z' => Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ) k z
    (fun a _ => ((hslice f hf a).mul (hslice g hg (j - a))).of_le
      (by rw [Work.Stability.smoothOrder]; simp))
  rw [hsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hfun : (fun z' => Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ)
      = (fun z' => Work.Spaces.DthIter a f z' θ)
        * (fun z' => Work.Spaces.DthIter (j - a) g z' θ) := by
    funext z'; rfl
  rw [hfun]
  have hmul := iteratedDeriv_mul (f := fun z' => Work.Spaces.DthIter a f z' θ)
    (g := fun z' => Work.Spaces.DthIter (j - a) g z' θ) (x := z) (n := k)
    ((hslice f hf a).of_le (by rw [Work.Stability.smoothOrder]; simp))
    ((hslice g hg (j - a)).of_le (by rw [Work.Stability.smoothOrder]; simp))
  rw [hmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Work.Spaces.pzIter_eq_iteratedDeriv c (Work.Spaces.DthIter a f) z θ,
    ← Work.Spaces.pzIter_eq_iteratedDeriv (k - c) (Work.Spaces.DthIter (j - a) g) z θ]
  ring

/-- **The Leibniz bound in the interior class**, with the explicit constant `257` of
`Work.Spaces.one_add_choose_double_sum_le` (the `SmoothQuad` counterpart of
`Work.Spaces.pz_mixed_mul_le_4`). -/
theorem sqm_pz_DthIter_mul_le_4 (k j : ℕ) (hk : k ≤ 4) (hj : j ≤ 4)
    (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ| ≤
        (257 : ℝ) * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
          |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| *
            |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ| := by
  intro z hz θ hθ
  rw [sqm_pz_DthIter_mul_eq k j f g hf hg z hz θ hθ]
  have h1 := Work.Spaces.abs_binom_double_sum_le k j
    (fun a c => Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ)
    (fun a c => Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ)
  have hT : (0 : ℝ) ≤ ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| *
        |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ| :=
    Finset.sum_nonneg fun c _ =>
      Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_right
    (Work.Spaces.one_add_choose_double_sum_le k j hk hj) hT)

/-! ## Nonnegativity of the `𝒲^{l,∞}`-norm -/

/-- The `𝒲^{l,∞}`-norm is nonnegative whenever it is honest. -/
theorem sqm_WlInf_nonneg (α : ℝ) (l : ℕ) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.WlInfMem α l h) :
    0 ≤ Work.Spaces.WlInf α l h := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α l h hmem)
    (Work.Spaces.wlThSum_nonneg α l h hmem)

/-! ## The pointwise bound for one summand of the angular Leibniz expansion -/

/-- One summand of the angular Leibniz expansion, bounded by the product of the two
`𝒲^{4,∞}`-norms: for `c ≤ k`, `a ≤ j`, `1 ≤ j`, `k + j ≤ 4`,

`|(z+1)^c ∂_z^c D_θ^a f| · |(z+1)^{k-c} ∂_z^{k-c} D_θ^{j-a} g| · sin(2θ)^{-α/5}/(α+sin 2θ)
   ≤ 2 |f|_𝒲 |g|_𝒲`. -/
theorem sqm_ang_summand_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f g : ℝ → ℝ → ℝ) (hmf : Work.Spaces.WlInfMem α 4 f) (hmg : Work.Spaces.WlInfMem α 4 g)
    (c a k j : ℕ) (hc : c ≤ k) (ha : a ≤ j) (hj : 1 ≤ j) (hkj : k + j ≤ 4)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
        * |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ 2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hspos : 0 < α + Real.sin (2 * θ) := by linarith
  have hWfnn : 0 ≤ Work.Spaces.WlInf α 4 f := sqm_WlInf_nonneg α 4 f hmf
  have hWgnn : 0 ≤ Work.Spaces.WlInf α 4 g := sqm_WlInf_nonneg α 4 g hmg
  have hWWnn : 0 ≤ Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := mul_nonneg hWfnn hWgnn
  have hψa : 0 ≤ (if a = 0 then (1 : ℝ)
      else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    by_cases h : a = 0
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; exact mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)
  have hψb : 0 ≤ (if j - a = 0 then (1 : ℝ)
      else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    by_cases h : j - a = 0
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; exact mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)
  have hZnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    div_nonneg (Real.rpow_nonneg hs0 _) (le_of_lt hspos)
  have hFA := Work.Spaces.factor_bound α hα f hmf c a (by omega) (fun _ => by omega) z θ hz hθI
  have hGA := Work.Spaces.factor_bound α hα g hmg (k - c) (j - a) (by omega) (fun _ => by omega)
    z θ hz hθI
  have hpsi := Work.Spaces.psi_mw_le α hα hα1 θ hθI a j ha hj
  have hstep : |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
        * |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|
      ≤ (Work.Spaces.WlInf α 4 f * (if a = 0 then (1 : ℝ)
            else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
        * (Work.Spaces.WlInf α 4 g * (if j - a = 0 then (1 : ℝ)
            else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
    mul_le_mul hFA hGA (abs_nonneg _) (mul_nonneg hWfnn hψa)
  calc |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
          * |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ ((Work.Spaces.WlInf α 4 f * (if a = 0 then (1 : ℝ)
            else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
        * (Work.Spaces.WlInf α 4 g * (if j - a = 0 then (1 : ℝ)
            else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right hstep hZnn
    _ = (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g)
          * ((if a = 0 then (1 : ℝ)
              else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * (if j - a = 0 then (1 : ℝ)
              else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
    _ ≤ (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) * 2 :=
          mul_le_mul_of_nonneg_left hpsi hWWnn
    _ = 2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by ring

/-! ## The interior part of `ProdW` -/

/-- The **interior** part of `Work.FTS.H2.ProdW`: on the *open* quadrant, where the `z`-slices
of a `SmoothQuad` function are `C^∞` (`Work.FTS.LocData.SmoothQuad.curry_z`), the Leibniz
expansion is available for both `∂_z^k` and `D_θ^j`, and hence the weighted derivatives of the
product are bounded by `|f|_𝒲 |g|_𝒲`:

* radial: `|(z+1)^k ∂_z^k (fg)| ≤ C |f|_𝒲 |g|_𝒲` for `k ≤ 4`;
* angular: `|(z+1)^k ∂_z^k D_θ^j (fg) · sin(2θ)^{-α/5}/(α+sin 2θ)| ≤ C |f|_𝒲 |g|_𝒲` for
  `1 ≤ j`, `k+j ≤ 4`.

The pointwise factor bounds are `Work.Spaces.WlInf_z_bound` and `Work.Spaces.factor_bound`
(which is `Work.Spaces.WlInf_mixed_bound` after the weight cancellation), and the sharing of the
single angular weight between the two factors of each Leibniz summand is
`Work.Spaces.psi_mw_le`.  The Leibniz expansions at the genuine smooth order are
`Work.FTS.H2.Q.pzIter_mul_local_sm` (for `∂_z^k`) and `Work.FTS.LocData.DthIter_mul_smoothQuad`
(for `D_θ^j`). -/
theorem prodW_interior_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.LocData.SmoothQuad f → Work.FTS.LocData.SmoothQuad g →
      Work.Spaces.WlInfMem α 4 f → Work.Spaces.WlInfMem α 4 g →
      (∀ k ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ|
          ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) ∧
      (∀ j k : ℕ, 1 ≤ j → k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(z + 1) ^ k * Work.Spaces.pzIter k
              (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro α f g hα hα1 hf hg hmf hmg
  have hWfnn : 0 ≤ Work.Spaces.WlInf α 4 f := sqm_WlInf_nonneg α 4 f hmf
  have hWgnn : 0 ≤ Work.Spaces.WlInf α 4 g := sqm_WlInf_nonneg α 4 g hmg
  have hWWnn : 0 ≤ Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := mul_nonneg hWfnn hWgnn
  constructor
  · -- the radial part
    intro k hk z hz θ hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    have hzIoi : z ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
    have hzp : 0 ≤ (z + 1) ^ k := pow_nonneg (by linarith) k
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hzu : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => f z' θ) z :=
      (hf.curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hzIoi)
    have hgv : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => g z' θ) z :=
      (hg.curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hzIoi)
    have hleib := Work.FTS.H2.Q.pzIter_mul_local_sm (u := f) (v := g) k hzu hgv
    have h1 : |Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ|
        ≤ ∑ c ∈ Finset.range (k + 1),
            (k.choose c : ℝ)
              * (|Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ|) := by
      rw [hleib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun c _ => ?_)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), abs_mul]
    have hstep : ∀ c ∈ Finset.range (k + 1),
        (z + 1) ^ k * (|Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ|)
          ≤ Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := by
      intro c hc
      have hc_le : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      have hc4 : c ≤ 4 := by omega
      have hkc4 : k - c ≤ 4 := by omega
      have hc0 : (0 : ℝ) ≤ (z + 1) ^ c := pow_nonneg (by linarith) c
      have hkc0 : (0 : ℝ) ≤ (z + 1) ^ (k - c) := pow_nonneg (by linarith) (k - c)
      have hA := Work.Spaces.WlInf_z_bound α 4 f hmf c hc4 z θ hz hθI
      have hB := Work.Spaces.WlInf_z_bound α 4 g hmg (k - c) hkc4 z θ hz hθI
      rw [abs_mul, abs_of_nonneg hc0] at hA
      rw [abs_mul, abs_of_nonneg hkc0] at hB
      have heq : (z + 1) ^ k
            * (|Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ|)
          = ((z + 1) ^ c * |Work.Spaces.pzIter c f z θ|)
            * ((z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) g z θ|) := by
        rw [show (z + 1) ^ k = (z + 1) ^ c * (z + 1) ^ (k - c) by
          rw [← pow_add, Nat.add_sub_cancel' hc_le]]
        ring
      rw [heq]
      exact mul_le_mul hA hB (mul_nonneg hkc0 (abs_nonneg _)) hWfnn
    calc |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ|
        = (z + 1) ^ k * |Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ| := by
          rw [abs_mul, abs_of_nonneg hzp]
      _ ≤ (z + 1) ^ k * (∑ c ∈ Finset.range (k + 1),
            (k.choose c : ℝ)
              * (|Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ|)) :=
          mul_le_mul_of_nonneg_left h1 hzp
      _ = ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)
            * ((z + 1) ^ k
                * (|Work.Spaces.pzIter c f z θ| * |Work.Spaces.pzIter (k - c) g z θ|)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)
            * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) :=
          Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hstep c hc) (Nat.cast_nonneg _)
      _ = (∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ))
            * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by rw [Finset.sum_mul]
      _ = (2 : ℝ) ^ k * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
          have h2 : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
          have hc : (∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)) = (2 : ℝ) ^ k := by
            rw [← Nat.cast_sum, Nat.sum_range_choose k, h2]
          rw [hc]
      _ ≤ 16 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
          apply mul_le_mul_of_nonneg_right _ hWWnn
          calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hk
            _ = 16 := by norm_num
      _ ≤ 100000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
          apply mul_le_mul_of_nonneg_right _ hWWnn; norm_num
      _ = 100000 * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := by ring
  · -- the angular part
    intro j k hj hkj z hz θ hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    have hzp : 0 ≤ (z + 1) ^ k := pow_nonneg (by linarith) k
    have hk4 : k ≤ 4 := by omega
    have hj4 : j ≤ 4 := by omega
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hspos : 0 < α + Real.sin (2 * θ) := by linarith
    have hZnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      div_nonneg (Real.rpow_nonneg hs0 _) (le_of_lt hspos)
    have hleib := sqm_pz_DthIter_mul_le_4 k j hk4 hj4 f g hf hg z hz θ hθ
    have hLHS : |(z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        = (z + 1) ^ k * |Work.Spaces.pzIter k
              (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
      rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hzp,
        abs_of_nonneg (Real.rpow_nonneg hs0 _), abs_of_pos hspos]
      ring
    have hbound1 : (z + 1) ^ k * |Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ|
        ≤ 257 * ((z + 1) ^ k * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
                * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|) := by
      have h1 := mul_le_mul_of_nonneg_left hleib hzp
      calc (z + 1) ^ k * |Work.Spaces.pzIter k
              (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ|
          ≤ (z + 1) ^ k * (257 * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
                  * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|) := h1
        _ = 257 * ((z + 1) ^ k * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
                  * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|) := by ring
    have hbound2 : (z + 1) ^ k * (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
        = ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
    have hstep : ∀ c ∈ Finset.range (k + 1), ∀ a ∈ Finset.range (j + 1),
        (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          ≤ 2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
      intro c hc a ha
      have hc_le : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      have ha_le : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      have heq : (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
          = |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
            * |(z + 1) ^ (k - c)
                * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ| := by
        have hz1 : (0 : ℝ) < z + 1 := by linarith
        have hp1 : (0 : ℝ) ≤ (z + 1) ^ c := pow_nonneg (le_of_lt hz1) c
        have hp2 : (0 : ℝ) ≤ (z + 1) ^ (k - c) := pow_nonneg (le_of_lt hz1) (k - c)
        rw [abs_mul, abs_of_nonneg hp1, abs_mul, abs_of_nonneg hp2]
        rw [show (z + 1) ^ k = (z + 1) ^ c * (z + 1) ^ (k - c) by
          rw [← pow_add, Nat.add_sub_cancel' hc_le]]
        ring
      rw [heq]
      exact sqm_ang_summand_bound α hα hα1 f g hmf hmg c a k j hc_le ha_le hj hkj hz hθ
    have hsum : (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_mul]
    have hsumle : ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
              * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) :=
      Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hstep c hc a ha
    calc |(z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        = (z + 1) ^ k * |Work.Spaces.pzIter k
              (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := hLHS
      _ ≤ 257 * ((z + 1) ^ k * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
                * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right hbound1 hZnn
      _ = 257 * ((∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              (z + 1) ^ k * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
                * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ|))
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by
          rw [hbound2]
          ring
      _ ≤ 257 * (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [hsum]
          exact hsumle
      _ = 257 * (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))
            * (2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g)) := by
          rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, nsmul_eq_mul]
          ring
      _ ≤ 100000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by
          have hk1 : ((k + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show k + 1 ≤ 5 by omega)
          have hj1 : ((j + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show j + 1 ≤ 5 by omega)
          have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          have hj0 : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          have hu : 257 * (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) * 2 ≤ 100000 := by nlinarith
          calc 257 * (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))
                * (2 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g))
              = (257 * (((k + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) * 2)
                * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) := by ring
            _ ≤ 100000 * (Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g) :=
                mul_le_mul_of_nonneg_right hu hWWnn
      _ = 100000 * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := by ring

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.VsFields =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false

/-- The angular weight `Λ` is at most `2` for `0 < α ≤ 1`, `θ ∈ Iθ`. -/
theorem lam_le_two {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) :
    (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hr : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
    Real.rpow_le_one hs0 hs1 (by linarith : (0:ℝ) ≤ α / 5)
  have hr0 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hs0 _
  have h1 : α + Real.sin (2 * θ) ≤ 1 + 1 := add_le_add hα1 hs1
  nlinarith [hr, hr0, hs0, hs1, h1]

/-- `Λ ≥ 0`. -/
theorem lam_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  exact mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)



end Work.FTS.Nonlinear.Pieces.RNP.row19
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.PsiDivS2Ode =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-equation for the divided angular profile `ψ / sin 2θ`

`Work.FTS.PhiStar.Psi0Ode` constructs the angular model `ψ` with `Lzero1 ψ = Γ̄` on `(0,π/2)`.
Writing `ψ = sin 2θ · G` (so that `G = ψ / sin 2θ` is the *divided* profile), the elliptic
equation turns into the second-order equation without singular coefficients

  `sin 2θ · G'' = (6 sin²θ - 4 cos²θ) · G' - Γ̄(θ)`,

which is the statement of `PsiDivS2Ode` and the equation solved by the paper's profile.

The algebraic content is the substitution identity
`Work.FTS.H2.StarPkg.LzeroSubst.lzero_sin_cos_mul`,

  `Lzero (sin θ cos θ · w) = -sin θ cos θ · ∂_θθw + (3 sin²θ - 2 cos²θ) · ∂_θw`,

applied to `w = 2G` (because `sin 2θ = 2 sin θ cos θ`), together with the fact that `Lzero`
only sees the `θ`-slice of its argument at the given `z` (lemma `Lzero_congr_slice` below).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- `Lzero` only sees the `θ`-slice at the given `z`: two functions whose `z`-slices agree in a
neighbourhood of `θ` have the same `Lzero`-value at `(z,θ)`. -/
lemma Lzero_congr_slice {Ψ Φ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun t => Ψ z t) =ᶠ[𝓝 θ] fun t => Φ z t) :
    Work.Elliptic.Lzero Ψ z θ = Work.Elliptic.Lzero Φ z θ := by
  have h1 : Work.Spaces.pthIter 2 Ψ z θ = Work.Spaces.pthIter 2 Φ z θ := by
    show deriv (fun t => deriv (fun t' => Ψ z t') t) θ
      = deriv (fun t => deriv (fun t' => Φ z t') t) θ
    exact h.deriv.deriv_eq
  have h2 : Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * Φ z θ) z θ := by
    show deriv (fun t => Real.tan t * Ψ z t) θ = deriv (fun t => Real.tan t * Φ z t) θ
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [h] with t ht
    rw [ht]
  simp only [Work.Elliptic.Lzero, h1, h2, h.eq_of_nhds]

theorem PsiDivS2Ode {α : ℝ} {ψ : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.sin (2 * θ) * deriv (fun t => deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) t) θ
        = (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2)
            * deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ
          - Work.FTS.VocabO.GamBar α θ := by
  intro θ hθ
  set G : ℝ → ℝ := fun θ' => ψ θ' / Real.sin (2 * θ') with hG
  have hpos : 0 < Real.pi := Real.pi_pos
  -- `G` is smooth on the open interval (where `sin 2θ > 0`)
  have hsm2 : ∀ n : ℕ, ContDiffOn ℝ n G (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have hsin : ContDiffOn ℝ n (fun t : ℝ => Real.sin (2 * t)) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    have hd := (hsm n).div hsin (fun t ht => by
      have h2 : 0 < Real.sin (2 * t) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, hpos])
      exact ne_of_gt h2)
    rw [hG]
    exact hd
  have hdiffG : DifferentiableOn ℝ G (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm2 1).differentiableOn (by norm_num)
  have hderivG : DifferentiableOn ℝ (deriv G) (Set.Ioo 0 (Real.pi / 2)) :=
    ((hsm2 2).deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).differentiableOn (by norm_num)
  -- `ψ` agrees near `θ` with `sin θ cos θ · (2G)`, i.e. with `sin 2θ · G`
  have hψeq : (fun t : ℝ => ψ t) =ᶠ[𝓝 θ]
      fun t : ℝ => Real.sin t * Real.cos t * (2 * G t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    have h1 : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, hpos])
    have h2 : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, hpos], ht.2⟩
    simp only [hG]
    rw [Real.sin_two_mul]
    calc ψ t = (2 * Real.sin t * Real.cos t) * (ψ t / (2 * Real.sin t * Real.cos t)) :=
          (mul_div_cancel₀ (ψ t) (by positivity)).symm
      _ = Real.sin t * Real.cos t * (2 * (ψ t / (2 * Real.sin t * Real.cos t))) := by ring
  -- transport the equation along the equality of the slices
  have hL1 : Work.FTS.EllipticEst.Lzero1 ψ θ
      = Work.Elliptic.Lzero (fun z t => Real.sin t * Real.cos t * (2 * G t)) 0 θ := by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero ψ 0]
    exact Lzero_congr_slice hψeq
  -- the `θ`-derivatives of the substituted function
  have hpthw : Work.Spaces.pth (fun _ t : ℝ => 2 * G t) 0 θ = 2 * deriv G θ := by
    show deriv (fun t : ℝ => 2 * G t) θ = 2 * deriv G θ
    exact Work.Spaces.deriv_const_mul' 2 θ G
  have hpthIter2w : Work.Spaces.pthIter 2 (fun _ t : ℝ => 2 * G t) 0 θ
      = 2 * deriv (deriv G) θ := by
    have hfun : (fun t : ℝ => Work.Spaces.pth (fun _ t : ℝ => 2 * G t) 0 t)
        = fun t => 2 * deriv G t := by
      funext t
      show deriv (fun t : ℝ => 2 * G t) t = 2 * deriv G t
      exact Work.Spaces.deriv_const_mul' 2 t G
    show deriv (fun t : ℝ => Work.Spaces.pth (fun _ t : ℝ => 2 * G t) 0 t) θ
      = 2 * deriv (deriv G) θ
    rw [hfun]
    exact Work.Spaces.deriv_const_mul' 2 θ (deriv G)
  -- the substitution identity
  have hsub := Work.FTS.H2.StarPkg.LzeroSubst.lzero_sin_cos_mul (w := fun _ t : ℝ => 2 * G t)
      (z := 0) (θ := θ) hθ (hdiffG.const_mul 2) (by
        have he : (fun θ' : ℝ => deriv (fun θ'' : ℝ => 2 * G θ'') θ')
            = fun θ' => 2 * deriv G θ' := by
          funext t
          exact Work.Spaces.deriv_const_mul' 2 t G
        rw [he]
        exact hderivG.const_mul 2)
  -- the divided equation
  have hkey : -(Real.sin (2 * θ)) * deriv (deriv G) θ
        + (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) * deriv G θ
      = Work.FTS.VocabO.GamBar α θ := by
    rw [← heq θ hθ, hL1, hsub, hpthIter2w, hpthw, Real.sin_two_mul]
    ring
  show Real.sin (2 * θ) * deriv (deriv G) θ
      = (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) * deriv G θ - Work.FTS.VocabO.GamBar α θ
  rw [← hkey]
  ring

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.N_b6_star.Tools =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_b6_star.Tools` — the elementary tools of the nine star pieces of the level-`6` `N`-block

The per-piece arithmetic of `Nblock6.N_b6_star`: every star piece is a scalar times a product
`A·P` of a `𝒲^{6,∞}`-coefficient priced by `KA` and an `ℋ⁶`-factor priced by `SP`; the product
rule `RawE6Aux.wlInfMul6` gives `HkSq α 6 (A·P) ≤ Cw α⁻¹ KA² (1 + SP)`, and the three lemmas
`piece_arith_e1`, `piece_arith_e2`, `piece_arith_sl1` reduce the three occurring shapes
(`1 + A·E`, `1 + Z`) to a constant times `B`.
-/

namespace Work.FTS.StrongEps.E4R3.Nblock6

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open MeasureTheory Set Filter
open scoped Real Topology

open Work.FTS.Galerkin (Fn)

/-! ## Elementary tools -/

/-- `HkNorm`-`HkSq` bookkeeping (a local copy; the `RawE6Aux` one sits in a file with development
stubs). -/
theorem hkNorm_sq_loc (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    (Work.Spaces.HkNorm α k f) ^ 2 = Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkNorm]
  exact Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)

/-- `α^{-1}·(K α)² ≤ K²` for `0 < α ≤ 1`. -/
theorem inv_mul_sq_le {α K : ℝ} (hα1 : α ≤ 1) (hα0 : 0 < α) :
    α ^ (-(1 : ℝ)) * (K * α) ^ 2 ≤ K ^ 2 := by
  have h : α ^ (-(1 : ℝ)) * (K * α) ^ 2 = K ^ 2 * α := by
    rw [Real.rpow_neg_one, mul_pow]; field_simp
  rw [h]; nlinarith [sq_nonneg K]

/-- `α^{-1}·(K α²)² ≤ K²` for `0 < α ≤ 1`. -/
theorem inv_mul_sq_sq_le {α K : ℝ} (hα1 : α ≤ 1) (hα0 : 0 < α) :
    α ^ (-(1 : ℝ)) * (K * α ^ 2) ^ 2 ≤ K ^ 2 := by
  have h : α ^ (-(1 : ℝ)) * (K * α ^ 2) ^ 2 = K ^ 2 * α ^ 3 := by
    rw [Real.rpow_neg_one, mul_pow]; field_simp
  rw [h]
  have h3 : α ^ 3 ≤ 1 := pow_le_one₀ (n := 3) hα0.le hα1
  nlinarith [sq_nonneg K]

/-- `HkSq α k P ≤ Ce²·HkSq α k f` from `HkNorm α k P ≤ Ce·HkNorm α k f` (no sign hypothesis on
`Ce`: the absolute value is taken first). -/
theorem hkSq_le_of_hkNorm_le {α : ℝ} (k : ℕ) {P f : ℝ → ℝ → ℝ} {Ce : ℝ}
    (h : Work.Spaces.HkNorm α k P ≤ Ce * Work.Spaces.HkNorm α k f) :
    Work.Spaces.HkSq α k P ≤ Ce ^ 2 * Work.Spaces.HkSq α k f := by
  have h2 : Work.Spaces.HkNorm α k P ≤ |Ce| * Work.Spaces.HkNorm α k f :=
    le_trans h (mul_le_mul_of_nonneg_right (le_abs_self Ce) (Real.sqrt_nonneg _))
  have h1 : (Work.Spaces.HkNorm α k P) ^ 2 ≤ (|Ce| * Work.Spaces.HkNorm α k f) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  rw [hkNorm_sq_loc, mul_pow, sq_abs, hkNorm_sq_loc] at h1
  exact h1

/-- `HkSq α k P ≤ K²` from `HkNorm α k P ≤ K`. -/
theorem hkSq_le_sq_of_le {α : ℝ} (k : ℕ) {P : ℝ → ℝ → ℝ} {K : ℝ}
    (h : Work.Spaces.HkNorm α k P ≤ K) : Work.Spaces.HkSq α k P ≤ K ^ 2 := by
  have h1 : (Work.Spaces.HkNorm α k P) ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rwa [hkNorm_sq_loc] at h1

/-! ## The per-piece arithmetic

Each piece is `c·(A·P)` with `HkSq α 6 (A·P) ≤ Cw α⁻¹ KA² (1 + SP)` and `KA = Ci·α^p`; the
following three lemmas reduce that to the final constant. -/

/-- The `1 + A·E`-shape (fixed and `w`-slots): reduce `c·(Cw α⁻¹(Ciα)^2(1+AE))`. -/
theorem piece_arith_e1 {α Cw Ci A E c2 B : ℝ}
    (hCw : 0 ≤ Cw) (hcore : α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 ≤ Ci ^ 2)
    (hc2 : 0 ≤ c2) (hc2le : c2 ≤ 4) (hA : 0 ≤ A) (hE : 0 ≤ E) (hEB : E ≤ B) (hB1 : 1 ≤ B) :
    c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 * (1 + A * E))
      ≤ 4 * (Cw * Ci ^ 2) * ((1 + A) * B) := by
  have hZ : 0 ≤ 1 + A * E := add_nonneg zero_le_one (mul_nonneg hA hE)
  have h1 : 1 + A * E ≤ (1 + A) * B := by nlinarith
  have hfac : 0 ≤ c2 * Cw * (1 + A * E) := mul_nonneg (mul_nonneg hc2 hCw) hZ
  calc c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 * (1 + A * E))
      = (c2 * Cw * (1 + A * E)) * (α ^ (-(1 : ℝ)) * (Ci * α) ^ 2) := by ring
    _ ≤ (c2 * Cw * (1 + A * E)) * Ci ^ 2 := mul_le_mul_of_nonneg_left hcore hfac
    _ ≤ (4 * Cw * (1 + A * E)) * Ci ^ 2 := by
        have h2 : c2 * Cw * (1 + A * E) ≤ 4 * Cw * (1 + A * E) := by
          have hAE : 0 ≤ Cw * (1 + A * E) := mul_nonneg hCw hZ
          calc c2 * Cw * (1 + A * E) = c2 * (Cw * (1 + A * E)) := by ring
            _ ≤ 4 * (Cw * (1 + A * E)) := mul_le_mul_of_nonneg_right hc2le hAE
            _ = 4 * Cw * (1 + A * E) := by ring
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg Ci)
    _ ≤ (4 * Cw * ((1 + A) * B)) * Ci ^ 2 := by
        have h3 : 4 * Cw * (1 + A * E) ≤ 4 * Cw * ((1 + A) * B) :=
          mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 * Cw)
        exact mul_le_mul_of_nonneg_right h3 (sq_nonneg Ci)
    _ = 4 * (Cw * Ci ^ 2) * ((1 + A) * B) := by ring

/-- The `1 + A·E`-shape with a *quadratic* slot `(Ci·α²)²` (piece `5`). -/
theorem piece_arith_e2 {α Cw Ci A E c2 B : ℝ}
    (hCw : 0 ≤ Cw) (hcore : α ^ (-(1 : ℝ)) * (Ci * α ^ 2) ^ 2 ≤ Ci ^ 2)
    (hc2 : 0 ≤ c2) (hc2le : c2 ≤ 4) (hA : 0 ≤ A) (hE : 0 ≤ E) (hEB : E ≤ B) (hB1 : 1 ≤ B) :
    c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α ^ 2) ^ 2 * (1 + A * E))
      ≤ 4 * (Cw * Ci ^ 2) * ((1 + A) * B) := by
  have hZ : 0 ≤ 1 + A * E := add_nonneg zero_le_one (mul_nonneg hA hE)
  have h1 : 1 + A * E ≤ (1 + A) * B := by nlinarith
  have hfac : 0 ≤ c2 * Cw * (1 + A * E) := mul_nonneg (mul_nonneg hc2 hCw) hZ
  calc c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α ^ 2) ^ 2 * (1 + A * E))
      = (c2 * Cw * (1 + A * E)) * (α ^ (-(1 : ℝ)) * (Ci * α ^ 2) ^ 2) := by ring
    _ ≤ (c2 * Cw * (1 + A * E)) * Ci ^ 2 := mul_le_mul_of_nonneg_left hcore hfac
    _ ≤ (4 * Cw * (1 + A * E)) * Ci ^ 2 := by
        have h2 : c2 * Cw * (1 + A * E) ≤ 4 * Cw * (1 + A * E) := by
          have hAE : 0 ≤ Cw * (1 + A * E) := mul_nonneg hCw hZ
          calc c2 * Cw * (1 + A * E) = c2 * (Cw * (1 + A * E)) := by ring
            _ ≤ 4 * (Cw * (1 + A * E)) := mul_le_mul_of_nonneg_right hc2le hAE
            _ = 4 * Cw * (1 + A * E) := by ring
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg Ci)
    _ ≤ (4 * Cw * ((1 + A) * B)) * Ci ^ 2 := by
        have h3 : 4 * Cw * (1 + A * E) ≤ 4 * Cw * ((1 + A) * B) :=
          mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 * Cw)
        exact mul_le_mul_of_nonneg_right h3 (sq_nonneg Ci)
    _ = 4 * (Cw * Ci ^ 2) * ((1 + A) * B) := by ring

/-- The `1 + Z`-shape with an arbitrary nonnegative `Z` (the shifted `F_*`-slots). -/
theorem piece_arith_sl1 {α Cw Ci Z c2 B : ℝ}
    (hCw : 0 ≤ Cw) (hcore : α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 ≤ Ci ^ 2)
    (hc2 : 0 ≤ c2) (hc2le : c2 ≤ 4) (hB1 : 1 ≤ B) (hZ : 0 ≤ Z) :
    c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 * (1 + Z))
      ≤ 4 * (Cw * Ci ^ 2) * ((1 + Z) * B) := by
  have hfac : 0 ≤ c2 * Cw * (1 + Z) := mul_nonneg (mul_nonneg hc2 hCw) (by linarith)
  calc c2 * (Cw * α ^ (-(1 : ℝ)) * (Ci * α) ^ 2 * (1 + Z))
      = (c2 * Cw * (1 + Z)) * (α ^ (-(1 : ℝ)) * (Ci * α) ^ 2) := by ring
    _ ≤ (c2 * Cw * (1 + Z)) * Ci ^ 2 := mul_le_mul_of_nonneg_left hcore hfac
    _ ≤ (4 * Cw * (1 + Z)) * Ci ^ 2 := by
        have h2 : c2 * Cw * (1 + Z) ≤ 4 * Cw * (1 + Z) := by
          have hAE : 0 ≤ Cw * (1 + Z) := mul_nonneg hCw (by linarith)
          calc c2 * Cw * (1 + Z) = c2 * (Cw * (1 + Z)) := by ring
            _ ≤ 4 * (Cw * (1 + Z)) := mul_le_mul_of_nonneg_right hc2le hAE
            _ = 4 * Cw * (1 + Z) := by ring
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg Ci)
    _ = 4 * (Cw * Ci ^ 2) * (1 + Z) := by ring
    _ ≤ 4 * (Cw * Ci ^ 2) * ((1 + Z) * B) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact le_mul_of_one_le_right (by linarith) hB1

/-- **The generic per-piece estimate.**  For a scalar `c`, a `𝒲^{6,∞}`-coefficient `A` priced by
`KA` and an `ℋ⁶`-factor `P` priced by `SP`, the level-`6` energy of `c·(A·P)` is at most
`c²·Cw·α⁻¹·KA²·(1+SP)`. -/
theorem piece_le {α Cw c KA SP : ℝ} {A P : ℝ → ℝ → ℝ}
    (hwl : ∀ (A' P' : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A' → Work.Spaces.WlInfMem α 6 A' → Work.Spaces.WlInf α 6 A' ≤ K →
      Work.FTS.EllipticEst.SmoothOpen P' → Work.Spaces.HkMem α 6 P' →
      Work.Spaces.HkSq α 6 (fun z θ => A' z θ * P' z θ)
        ≤ Cw * α ^ (-(1 : ℝ)) * K ^ 2 * (1 + Work.Spaces.HkSq α 6 P'))
    (hCw : 0 ≤ Cw) (hα0 : 0 < α)
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hAm : Work.Spaces.WlInfMem α 6 A)
    (hAb : Work.Spaces.WlInf α 6 A ≤ KA)
    (hP : Work.FTS.EllipticEst.SmoothOpen P) (hPm : Work.Spaces.HkMem α 6 P)
    (hPb : Work.Spaces.HkSq α 6 P ≤ SP) :
    Work.Spaces.HkSq α 6 (fun z θ => c * (A z θ * P z θ))
      ≤ c ^ 2 * (Cw * α ^ (-(1 : ℝ)) * KA ^ 2 * (1 + SP)) := by
  rw [Work.FTS.StrongEps.HkSq_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 A := Work.Spaces.WlInf_nonneg α 6 A hAm
  have hKAnn : 0 ≤ KA := le_trans hWnn hAb
  refine le_trans (hwl A P KA hA hAm hAb hP hPm) ?_
  have hbase : 0 ≤ Cw * α ^ (-(1 : ℝ)) * KA ^ 2 :=
    mul_nonneg (mul_nonneg hCw (Real.rpow_nonneg hα0.le _)) (sq_nonneg KA)
  exact mul_le_mul_of_nonneg_left (by linarith) hbase
end Work.FTS.StrongEps.E4R3.Nblock6
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.L12_z_lipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false

/-! ## The two elementary inputs: a pointwise comparison and a tail integral -/

/-- `Wlam s² = s²/(1+s)⁴ ≤ 1/(1+s)²` for `s ≥ 0`: since `s ≤ 1+s`, the numerator `s²` is at
most `(1+s)²`, so the quotient is at most `(1+s)²/(1+s)⁴ = 1/(1+s)²`. -/
lemma Wlam_sq_le_inv_sq (s : ℝ) (hs : 0 ≤ s) :
    Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ 1 / (1 + s) ^ 2 := by
  have hle : s ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
  have hpos : 0 < (1 + s) ^ 2 := by positivity
  rw [Work.FTS.GalBasis.cc.Wlam, div_pow, show ((1 + s) ^ 2) ^ 2 = (1 + s) ^ 4 by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc s ^ 2 * (1 + s) ^ 2 ≤ (1 + s) ^ 2 * (1 + s) ^ 2 :=
        mul_le_mul_of_nonneg_right hle hpos.le
    _ = 1 * (1 + s) ^ 4 := by ring

/-- The integrand of the tail integral: `x ↦ 1/(1+x)²` is the derivative of
`x ↦ (1+x)^{-1}`, which is positive and decreasing to `0` at `+∞`, so its derivative
(negated) is automatically integrable on `(a,∞)` by
`MeasureTheory.integrableOn_Ioi_deriv_of_nonpos`. -/
private lemma integrableOn_Ioi_one_add_sq_inv_aux (a : ℝ) (_ha : 0 ≤ a) :
    MeasureTheory.IntegrableOn (fun x : ℝ => 1 / (1 + x) ^ 2) (Set.Ioi a) ∧
      ∫ x in Set.Ioi a, 1 / (1 + x) ^ 2 = 1 / (1 + a) := by
  have hg'neg : ∀ x ∈ Set.Ioi a, -(1 / (1 + x) ^ 2) ≤ 0 := by
    intro x _
    have h : 0 ≤ 1 / (1 + x) ^ 2 := by positivity
    linarith
  have hcont : ContinuousWithinAt (fun x : ℝ => (1 + x)⁻¹) (Set.Ici a) a := by
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.inv₀ ?_ ?_
    · fun_prop
    · linarith
  have hlim : Tendsto (fun x : ℝ => (1 + x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_const_nhds.add_atTop tendsto_id)
  have hderiv : ∀ x ∈ Set.Ioi a,
      HasDerivAt (fun x : ℝ => (1 + x)⁻¹) (-(1 / (1 + x) ^ 2)) x := by
    intro x hx
    have hx0 : (1 + x) ≠ 0 := by
      simp only [Set.mem_Ioi] at hx
      linarith
    have h := (hasDerivAt_inv hx0).comp x ((hasDerivAt_id x).const_add 1)
    convert h using 1
    funext y
    simp only [Function.comp_apply]
    ring_nf
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => -(1 / (1 + x) ^ 2)) (Set.Ioi a) :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonpos hcont hderiv hg'neg hlim
  refine ⟨by simpa using hint.neg, ?_⟩
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hg'neg hlim
  rw [MeasureTheory.integral_neg, zero_sub] at h
  rw [one_div]
  linarith [h]

/-- `x ↦ 1/(1+x)²` is integrable on `(a,∞)` for `a ≥ 0`. -/
lemma integrableOn_Ioi_one_add_sq_inv (a : ℝ) (ha : 0 ≤ a) :
    MeasureTheory.IntegrableOn (fun x : ℝ => 1 / (1 + x) ^ 2) (Set.Ioi a) :=
  (integrableOn_Ioi_one_add_sq_inv_aux a ha).1

/-- **The tail integral**: `∫_{x>a} (1+x)^{-2} dx = 1/(1+a)` for `a ≥ 0`.  (FTC on
`x ↦ -(1+x)^{-1}`, whose derivative is `(1+x)^{-2}` and which tends to `0` at `+∞`.) -/
lemma integral_Ioi_one_add_sq_inv (a : ℝ) (ha : 0 ≤ a) :
    ∫ x in Set.Ioi a, 1 / (1 + x) ^ 2 = 1 / (1 + a) :=
  (integrableOn_Ioi_one_add_sq_inv_aux a ha).2

/-! ## Cauchy–Schwarz in the radial variable with the sharp weight bound `1/(1+z)` -/

/-- Cauchy–Schwarz in the radial variable with the weight bound `∫_{s>z} Wlam² ≤ 1/(1+z)`,
valid for `z ≥ 0`.  No measurability of `A` is assumed: the argument uses the measurable
surrogate `B = √(A²)`, which agrees with `A` on `(z,∞)` because `A ≥ 0` there. -/
lemma Wlam_mul_le_sqrt_one_add {A : ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (hnn : ∀ s ∈ Set.Ioi z, 0 ≤ A s)
    (hint : MeasureTheory.IntegrableOn (fun s => A s ^ 2) (Set.Ioi z)) :
    ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Real.sqrt (1 / (1 + z)) * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) := by
  -- the measurable surrogate `B = √(A²)`, equal to `A` on `(z,∞)`
  set B : ℝ → ℝ := fun s => Real.sqrt (A s ^ 2) with hB
  have hBnn : ∀ s, 0 ≤ B s := fun s => Real.sqrt_nonneg _
  have hBeq : B =ᵐ[volume.restrict (Set.Ioi z)] A := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [hB]
    exact Real.sqrt_sq (hnn s hs)
  have hBsq : ∀ s, B s ^ 2 = A s ^ 2 := fun s => by
    change Real.sqrt (A s ^ 2) ^ 2 = A s ^ 2
    exact Real.sq_sqrt (sq_nonneg (A s))
  have hB_aesm : AEStronglyMeasurable B (volume.restrict (Set.Ioi z)) := by
    change AEStronglyMeasurable (fun s => Real.sqrt (A s ^ 2)) (volume.restrict (Set.Ioi z))
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hB_int : MeasureTheory.IntegrableOn (fun s => B s ^ 2) (Set.Ioi z) :=
    hint.congr_fun (fun s _ => (hBsq s).symm) measurableSet_Ioi
  have hB_memLp : MemLp B 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hB_aesm).mpr hB_int
  -- the radial weight
  have hWlam_aesm : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi z)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi z))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi z) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using
      Work.Elliptic.psi_sq_integrable_aux.mono_set (fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢
        linarith)
  have hWlam_memLp : MemLp Work.FTS.GalBasis.cc.Wlam 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hWlam_aesm).mpr hWlam_sq_int
  -- the sharp weight bound `∫_{s>z} Wlam² ≤ 1/(1+z)`
  have hWlam_sq_le : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ 1 / (1 + z) := by
    have h1 : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2
        ≤ ∫ s in Set.Ioi z, 1 / (1 + s) ^ 2 :=
      MeasureTheory.setIntegral_mono_on hWlam_sq_int (integrableOn_Ioi_one_add_sq_inv z hz)
        measurableSet_Ioi (fun s hs =>
          Wlam_sq_le_inv_sq s (le_of_lt (lt_of_le_of_lt hz hs)))
    rw [integral_Ioi_one_add_sq_inv z hz] at h1
    exact h1
  -- Cauchy–Schwarz for the two measurable factors
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
    (u := Work.FTS.GalBasis.cc.Wlam) (v := B) (s := Set.Ioi z) hWlam_memLp hB_memLp
  have hprod : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s
      = |∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s| := by
    rw [abs_of_nonneg]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_of_le_of_lt hz hs)))
      (hBnn s)
  calc ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      = ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hBeq] with s hs
        rw [hs]
    _ = |∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * B s| := hprod
    _ ≤ Real.sqrt (∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2)
          * Real.sqrt (∫ s in Set.Ioi z, B s ^ 2) := hcs
    _ = Real.sqrt (∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2)
          * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) := by
        rw [MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun s => hBsq s)]
    _ ≤ Real.sqrt (1 / (1 + z)) * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hWlam_sq_le) (Real.sqrt_nonneg _)

/-! ## The integrated bound on the tail `(z,∞)` -/

/-- **The main estimate**, at order `4` and for `z ≥ 0`:
`∫_{s>z} |L₁₂-density h s| ds ≤ BK · √(1/(1+z)) · √(HkSq α 4 h)`. -/
lemma tail_abs_L12dens_le {α : ℝ} {h : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 h)
    {z : ℝ} (hz : 0 ≤ z) :
    ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / (1 + z))
        * Real.sqrt (Work.Spaces.HkSq α 4 h) := by
  -- the angular marginal `H` and its square root `A`
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 h s θ
  have hAnn : ∀ s, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  -- integrability of `H` on `[0,∞)` and hence on `(z,∞)`
  have hH_int_Iz : MeasureTheory.IntegrableOn H Work.Spaces.Iz := by
    simpa only [hH] using hmem.2
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := by
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith
  have hH_int : MeasureTheory.IntegrableOn H (Set.Ioi z) := hH_int_Iz.mono_set hsub
  have hA2_int : MeasureTheory.IntegrableOn (fun s => A s ^ 2) (Set.Ioi z) := by
    refine hH_int.congr_fun (fun s _ => ?_) measurableSet_Ioi
    rw [hA]
    exact (Real.sq_sqrt (hHnn s)).symm
  -- `∫_{s>z} A² ≤ HkSq α 4 h`
  have hA2_le : ∫ s in Set.Ioi z, A s ^ 2 ≤ Work.Spaces.HkSq α 4 h := by
    have h1 : ∫ s in Set.Ioi z, A s ^ 2 = ∫ s in Set.Ioi z, H s :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]
        exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi z, H s ≤ ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_mono_set hH_int_Iz (Filter.Eventually.of_forall hHnn)
        (Filter.Eventually.of_forall fun x hx => hsub hx)
    have h3 : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α 4 h := by
      rw [hH]
      rfl
    linarith
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Real.sqrt (1 / (1 + z)) * Real.sqrt (Work.Spaces.HkSq α 4 h) :=
    le_trans (Wlam_mul_le_sqrt_one_add hz (fun s _ => hAnn s) hA2_int)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA2_le) (Real.sqrt_nonneg _))
  -- the pointwise bound on the density
  have hbd : ∀ s ∈ Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * A s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hz hs
    have hb := Work.FTS.GalBasis.cc.abs_L12dens_le α h hmem hs0
    simpa only [hA, hH] using hb
  -- the majorant is integrable (AM–GM) and the bound passes to the integral
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi z)) := by
    rw [hA]
    exact (hH_int.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hWlam_aesm : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi z)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi z))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi z) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using
      Work.Elliptic.psi_sq_integrable_aux.mono_set (fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢
        linarith)
  have hAMGM : ∀ s ∈ Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Work.FTS.GalBasis.cc.Wlam s ^ 2 + A s ^ 2 := by
    intro s _
    nlinarith [sq_nonneg (Work.FTS.GalBasis.cc.Wlam s - A s)]
  have hsum_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2 + A s ^ 2) (Set.Ioi z) :=
    hWlam_sq_int.add hA2_int
  have hdom_int : MeasureTheory.IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s))
      (Set.Ioi z) := by
    refine MeasureTheory.Integrable.mono' (hsum_int.const_mul Work.FTS.GalBasis.cc.BK) ?_ ?_
    · exact (hWlam_aesm.mul hA_aesm).const_mul Work.FTS.GalBasis.cc.BK
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hnn : 0 ≤ Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) :=
        mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg
          (mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_of_le_of_lt hz hs)))
            (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) Work.FTS.GalBasis.cc.BK_nonneg
  have h2 : ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      |Work.Construction.L12dens h s|
        ≤ Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun s hs => ?_
    calc |Work.Construction.L12dens h s|
        ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * A s) := hbd s hs
      _ = Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by ring
  have h3 : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s)
      = Work.FTS.GalBasis.cc.BK * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s :=
    MeasureTheory.integral_const_mul Work.FTS.GalBasis.cc.BK _
  calc ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := h2
    _ = Work.FTS.GalBasis.cc.BK * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s := h3
    _ ≤ Work.FTS.GalBasis.cc.BK * (Real.sqrt (1 / (1 + z)) * Real.sqrt (Work.Spaces.HkSq α 4 h)) :=
        mul_le_mul_of_nonneg_left hCS Work.FTS.GalBasis.cc.BK_nonneg
    _ = Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / (1 + z)) * Real.sqrt (Work.Spaces.HkSq α 4 h) := by
        ring

/-! ## The Lipschitz statement -/

theorem L12_z_lipschitz : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ f g : Work.FTS.Galerkin.Fn,
    Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
    Work.FTS.VocabO.HQo α 4 (fun z θ => f z θ - g z θ) →
    ∀ z : ℝ, 0 ≤ z →
      |Work.Construction.L12 f z - Work.Construction.L12 g z|
        ≤ C / Real.sqrt (1 + z) * Work.FTS.Nonlin.Xn α (fun z θ => f z θ - g z θ) := by
  refine ⟨Work.FTS.GalBasis.cc.BK + 1, by linarith [Work.FTS.GalBasis.cc.BK_nonneg], ?_⟩
  intro α _ f g hf hg hfg z hz
  -- the difference datum
  set h : ℝ → ℝ → ℝ := fun z θ => f z θ - g z θ with hh
  have hmemh : Work.Spaces.HkMem α 4 h := hfg.2
  -- additivity of `L₁₂` in the first argument, for `z ≥ 0`
  have hsub : Work.Construction.L12 f z - Work.Construction.L12 g z
      = Work.Construction.L12 h z := by
    refine (Work.FTS.StrongEps.EComparison.L12_sub_HkMem hf.1 hg.1 hf.2 hg.2 z ?_).symm
    simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
  have h1 : |Work.Construction.L12 h z|
      ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens h s| := by
    have hL12 : Work.Construction.L12 h z
        = ∫ s in Set.Ioi z, Work.Construction.L12dens h s := rfl
    rw [hL12]
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi z))
        (f := fun s => Work.Construction.L12dens h s))
  have h2 : ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / (1 + z))
        * Real.sqrt (Work.Spaces.HkSq α 4 h) :=
    tail_abs_L12dens_le hmemh hz
  have h3 : Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / (1 + z))
        * Real.sqrt (Work.Spaces.HkSq α 4 h)
      = Work.FTS.GalBasis.cc.BK * Real.sqrt (Work.Spaces.HkSq α 4 h)
        / Real.sqrt (1 + z) := by
    rw [Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num), Real.sqrt_one]
    ring
  have h4 : Work.FTS.GalBasis.cc.BK * Real.sqrt (Work.Spaces.HkSq α 4 h)
        / Real.sqrt (1 + z)
      ≤ (Work.FTS.GalBasis.cc.BK + 1) * Real.sqrt (Work.Spaces.HkSq α 4 h)
        / Real.sqrt (1 + z) := by
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hXn : Work.FTS.Nonlin.Xn α h = Real.sqrt (Work.Spaces.HkSq α 4 h) := rfl
  have hmain : |Work.Construction.L12 f z - Work.Construction.L12 g z|
      ≤ (Work.FTS.GalBasis.cc.BK + 1) / Real.sqrt (1 + z)
        * Work.FTS.Nonlin.Xn α h := by
    calc |Work.Construction.L12 f z - Work.Construction.L12 g z|
        = |Work.Construction.L12 h z| := by rw [hsub]
      _ ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens h s| := h1
      _ ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt (1 / (1 + z))
            * Real.sqrt (Work.Spaces.HkSq α 4 h) := h2
      _ = Work.FTS.GalBasis.cc.BK * Real.sqrt (Work.Spaces.HkSq α 4 h)
            / Real.sqrt (1 + z) := h3
      _ ≤ (Work.FTS.GalBasis.cc.BK + 1) * Real.sqrt (Work.Spaces.HkSq α 4 h)
            / Real.sqrt (1 + z) := h4
      _ = (Work.FTS.GalBasis.cc.BK + 1) / Real.sqrt (1 + z) * Work.FTS.Nonlin.Xn α h := by
          rw [hXn]
          ring
  simpa only [hh] using hmain

end Work.FTS.StrongEps.L12
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.SupPort.slotM_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.SupPort

open MeasureTheory Set Filter
open scoped Real Topology

theorem slotM_open (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) ≤ Work.Spaces.HkSq α 4 f
    ∧ MeasureTheory.IntegrableOn (fun θ => ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ
    ∧ (∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun z => (Work.Spaces.mixed j i f z θ) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) := by
  classical
  -- Tonelli for the whole `ℋ⁴`-integrand, in the order `∫_θ ∫_z`
  obtain ⟨hHk_eq, hHk_int, hHk_slice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hf hmem
  -- almost every angle is interior
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π/2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0:ℝ))
      (b := Real.pi/2)] with σ h _
    exact h.mpr ‹σ ∈ Work.Spaces.Iθ›
  -- a.e. strong measurability of the uncurried weighted slot square
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      ((((hf.mixed j i).continuousOn).mul (Work.FTS.H2.continuousOn_Wt_Qd α)).pow 2)
  have hslice_meas : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.AEStronglyMeasurable
        (fun z => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := haesm.prodMk_right
  have hAESM_outer : MeasureTheory.AEStronglyMeasurable
      (fun θ => ∫ z in Work.Spaces.Iz, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := (haesm.prod_swap).integral_prod_right'
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iz)
    simpa only [Function.uncurry, Prod.swap_prod_mk] using h
  -- third conjunct: a.e. radial-slice integrability of `(D_z^j D_θ^i f)² w²`
  have hconv : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.mixed j i f z θ) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    filter_upwards [hHk_slice, hslice_meas, haeθ] with θ hHkint hmeas hθ
    have hs : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hgint : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz :=
      hHkint.mono' hmeas (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij)
    have hSS : (Real.sin (2*θ)) ^ (Work.Spaces.gam α)
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) = 1 := by
      rw [← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero]
    have hkey : ∀ z : ℝ, (Real.sin (2*θ)) ^ (Work.Spaces.gam α) * (Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 := by
      intro z
      have hWtsq : (Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.w z) ^ 2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) := by
        simpa [Work.Spaces.Wt, Work.Spaces.wTheta] using Work.FTS.H2.Wt_sq_Ioo α z θ hθ
      calc (Real.sin (2*θ)) ^ (Work.Spaces.gam α) * (Work.Spaces.Wt α z θ) ^ 2
          = (Real.sin (2*θ)) ^ (Work.Spaces.gam α)
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α))) := by rw [hWtsq]
        _ = ((Real.sin (2*θ)) ^ (Work.Spaces.gam α)
            * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α))) * (Work.Spaces.w z) ^ 2 := by ring
        _ = (Work.Spaces.w z) ^ 2 := by rw [hSS, one_mul]
    exact MeasureTheory.IntegrableOn.congr_fun
      (hgint.const_mul ((Real.sin (2*θ)) ^ (Work.Spaces.gam α)))
      (fun z _ => by
        calc (Real.sin (2*θ)) ^ (Work.Spaces.gam α)
              * (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.mixed j i f z θ) ^ 2
              * ((Real.sin (2*θ)) ^ (Work.Spaces.gam α) * (Work.Spaces.Wt α z θ) ^ 2) := by ring
          _ = (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by rw [hkey])
      measurableSet_Ici
  -- second conjunct: the partially integrated slot is `θ`-integrable
  have hGint : MeasureTheory.IntegrableOn
      (fun θ => ∫ z in Work.Spaces.Iz, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      Work.Spaces.Iθ := by
    refine Integrable.mono' hHk_int hAESM_outer ?_
    filter_upwards [hHk_slice] with θ hHkint
    have hle : (∫ z in Work.Spaces.Iz, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ z in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f z θ :=
      integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hHkint
        (Eventually.of_forall fun z => Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij)
    rw [Real.norm_of_nonneg (integral_nonneg fun z => sq_nonneg _)]
    exact hle
  -- first conjunct: monotone comparison of the two iterated integrals
  refine ⟨?_, hGint, hconv⟩
  have hle : (fun θ => ∫ z in Work.Spaces.Iz, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => ∫ z in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f z θ) := by
    filter_upwards [hHk_slice] with θ hHkint
    exact integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hHkint
      (Eventually.of_forall fun z => Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij)
  calc (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f z θ :=
        integral_mono_ae hGint hHk_int hle
    _ = Work.Spaces.HkSq α 4 f := hHk_eq

end Work.FTS.StrongEps.SupPort
end
-- ===== merged: Submission.Work.H2.T1Q.ExpandQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The Leibniz expansions -/





end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.H2.T1Q.SlotOpen =====
section

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
set_option maxHeartbeats 800000

open Work.FTS.H2

/-! ## `pm` is carried by the open quadrant -/

/-- Almost every point of the product measure `pm` has its angular coordinate in the *open*
interval `(0, π/2)`: the boundary lines `θ = 0` and `θ = π/2` are null for `pm`. -/
theorem ae_pm_theta_mem_Ioo : ∀ᵐ p ∂pm, p.2 ∈ Set.Ioo 0 (π / 2) := by
  rw [MeasureTheory.ae_iff]
  have hset : {p : ℝ × ℝ | ¬ p.2 ∈ Set.Ioo 0 (π / 2)}
      = Set.univ ×ˢ (Set.Ioo 0 (π / 2))ᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, true_and]
  rw [hset, pm, MeasureTheory.Measure.prod_prod]
  have hS : (volume.restrict Work.Spaces.Iθ) (Set.Ioo 0 (π / 2))ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
    have hsub : (Set.Ioo 0 (π / 2))ᶜ ∩ Work.Spaces.Iθ ⊆ ({0, π / 2} : Set ℝ) := by
      intro θ hθ
      rw [Set.mem_inter_iff, Set.mem_compl_iff] at hθ
      obtain ⟨hn, hI⟩ := hθ
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hI
      rw [Set.mem_Ioo] at hn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases le_or_gt θ 0 with h | h
      · exact Or.inl (le_antisymm h hI.1)
      · exact Or.inr (le_antisymm hI.2 (not_lt.mp (not_and.mp hn h)))
    refine MeasureTheory.measure_mono_null hsub ?_
    exact Set.Finite.measure_zero (by simp : ({0, π / 2} : Set ℝ).Finite) volume
  rw [hS, mul_zero]

/-! ## Continuity of the two weights on the open quadrant -/

/-- The `η`-weight `Whz z θ = w z / sin(2θ)^{η/2}` is continuous on the open quadrant. -/
theorem continuousOn_Whz_quad :
    ContinuousOn (fun p : ℝ × ℝ => Whz p.1 p.2) Work.FTS.H2.HQ.quadQ := by
  have hfun : (fun p : ℝ × ℝ => Whz p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := rfl
  rw [hfun]
  exact Work.FTS.H2.HQ.continuousOn_light_quad

/-- The `γ`-weight `Wm α z θ = w z · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wm_quad (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Wm α p.1 p.2) Work.FTS.H2.HQ.quadQ :=
  Work.FTS.H2.HQ.continuousOn_Wt_quad α

/-! ## Strong measurability of a triple product of slots -/


/-! ## The pairing lemma with an open-quadrant bound -/

/-- **The pairing lemma of the interior class.**  Same conclusion as
`Work.FTS.H2.term_of_slot`, but the `V`-factor only has to be bounded by `K` on the *open*
quadrant `0 < z`, `0 < θ < π/2`.

Route: truncate `V` to `V' = V · 1_{(0,π/2)}(θ)` (zero on the two boundary lines, where the
`V`-bound is unavailable), apply `Work.FTS.H2.term_of_slot` to `V'` (the closed-quadrant
hypothesis now holds), and observe that `V'` agrees with `V` `pm`-almost everywhere
(`ae_pm_theta_mem_Ioo`), so the integrability and the value of the integral are unchanged. -/
theorem term_of_slot_open (α : ℝ) (u v : ℝ → ℝ → ℝ) (hmu : Work.Spaces.HkMem α 4 u)
    (hmv : Work.Spaces.HkMem α 4 v) (A B V : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hV : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2), |V z θ| ≤ K)
    (hA0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A z θ)
    (hB0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ B z θ)
    (hA : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 u z θ)
    (hB : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (B z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 v z θ)
    (hAmeas : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => A z θ) (volume.restrict Work.Spaces.Iθ))
    (hBmeas : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => B z θ) (volume.restrict Work.Spaces.Iθ))
    (hVABmeas : AEStronglyMeasurable
      (Function.uncurry (fun z θ => |V z θ * A z θ * B z θ|)) pm) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ => |V z θ * A z θ * B z θ|)) pm ∧
      (∫ p, |V p.1 p.2 * A p.1 p.2 * B p.1 p.2| ∂pm)
        ≤ K * Work.Spaces.HkNorm α 4 u * Work.Spaces.HkNorm α 4 v := by
  set V' : ℝ → ℝ → ℝ := fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then V z θ else 0 with hV'def
  have hV' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |V' z θ| ≤ K := by
    intro z hz θ hθ
    by_cases h : θ ∈ Set.Ioo 0 (π / 2)
    · simpa only [hV'def, h, ite_true] using hV z hz θ h
    · simp only [hV'def, h, ite_false, abs_zero]
      exact hK
  have hae : (fun p : ℝ × ℝ => |V p.1 p.2 * A p.1 p.2 * B p.1 p.2|)
      =ᵐ[pm] (fun p : ℝ × ℝ => |V' p.1 p.2 * A p.1 p.2 * B p.1 p.2|) := by
    filter_upwards [ae_pm_theta_mem_Ioo] with p hp
    simp only [hV'def, hp, ite_true]
  have hV'ABmeas : AEStronglyMeasurable
      (Function.uncurry (fun z θ => |V' z θ * A z θ * B z θ|)) pm :=
    hVABmeas.congr hae
  obtain ⟨hint, hbd⟩ := term_of_slot α u v hmu hmv A B V' K hK hV' hA0 hB0 hA hB hAmeas
    hBmeas hV'ABmeas
  exact ⟨hint.congr hae.symm, by rw [← integral_congr_ae hae.symm]; exact hbd⟩

end Work.H2.T1Q
end
end
