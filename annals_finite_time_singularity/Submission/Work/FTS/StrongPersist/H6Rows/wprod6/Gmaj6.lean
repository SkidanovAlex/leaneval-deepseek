import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.Tools.aesm_Fpair_fts
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceMomentIdentity
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Auxiliary facts -/

/-- The level-`0` `ℋ`-integrand is the weighted square of the function. -/
theorem hkIntegrand_zero_eq_of_mem (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigE θ := by
  rw [Work.FTS.EllipticEst.TT.AeI1.HkIntegrand_zero_eq α f hθ]
  rfl

/-- **Pointwise equality of the level-`0` integrands** on the domain, from agreement of the
functions on the open quadrant. -/
theorem HkIntegrand_zero_congr (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ = Work.Spaces.HkIntegrand α 0 g z θ := by
  rw [hkIntegrand_zero_eq_of_mem α f hθ, hkIntegrand_zero_eq_of_mem α g hθ]
  by_cases hw : Work.Spaces.w z = 0
  · rw [hw]; ring
  by_cases hs : sigE θ = 0
  · rw [hs]; ring
  have hzpos : 0 < z := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | h0
    · exact absurd (by rw [← h0, Work.FTS.EllipticEst.TT.AeI1.w_eq_zero_at_zero]) hw
    · exact h0
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    intro hsin0
    apply hs
    rw [sigE, hsin0,
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
  have hθ0 : θ ≠ 0 := by
    intro h; exact hsin (by rw [h]; norm_num)
  have hθπ : θ ≠ Real.pi / 2 := by
    intro h
    exact hsin (by rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])
  have hθIoo : 0 < θ ∧ θ < Real.pi / 2 :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθπ⟩
  rw [heq z θ hzpos hθIoo.1 hθIoo.2]

/-- **`HkMem` is invariant under equality on the open quadrant.** -/
theorem HkMem_zero_congr {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hf : Work.Spaces.HkMem α 0 f) : Work.Spaces.HkMem α 0 g := by
  refine ⟨fun z hz => ?_, ?_⟩
  · exact (hf.1 z hz).congr_fun (fun θ hθ => HkIntegrand_zero_congr α heq hz hθ)
      measurableSet_Icc
  · exact (hf.2).congr_fun (fun z hz =>
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ hθ => HkIntegrand_zero_congr α heq hz hθ)) measurableSet_Ici

/-- The slice derivative of `U u = z ∂_z u` is `V u = z ∂_z ∂_θ u` on the open quadrant. -/
theorem slice_deriv_eq {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ}
    (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Iθo) :
    deriv (fun θ' => U u z θ') θ = V u z θ := by
  have hcd2 : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
    (hS.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))
  have hcl := Work.Spaces.pz_pth_comm (f := u) hcd2
  have hcd1 : ContDiffOn ℝ 1 (fun θ' => Work.Spaces.pz u z θ') Iθo := by
    refine (hS.pz.curry_θ hz).of_le ?_
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  have hdiff : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz u z θ') θ :=
    (hcd1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  calc deriv (fun θ' => U u z θ') θ
      = deriv (fun θ' => z * Work.Spaces.pz u z θ') θ := rfl
    _ = z * deriv (fun θ' => Work.Spaces.pz u z θ') θ := deriv_const_mul z hdiff
    _ = z * Work.Spaces.pth (Work.Spaces.pz u) z θ := rfl
    _ = z * Work.Spaces.pz (Work.Spaces.pth u) z θ := by rw [hcl]
    _ = V u z θ := rfl

/-! ## The per-slice bound -/

/-- **The per-slice bound.**  For a slice `z > 0` whose two endpoint traces vanish and for which
`V u z ·` is weighted-square-integrable, the `N`-integrand of the slice is integrable and
dominated by the `V`-energy of the slice, with the constant `40000`. -/
theorem slice_bound {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hV : Work.Spaces.HkMem α 0 (V u)) {z : ℝ} (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ => U u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Filter.Tendsto (fun θ => U u z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    MeasureTheory.IntegrableOn
        (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) Iθo
      ∧ (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
        ≤ 40000 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) := by
  have hη0 : (0 : ℝ) ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have hzmem : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hwpos : 0 < Work.Spaces.w z := Work.FTS.EllipticEst.TT.AeI1.w_pos_of_pos hz
  -- the `C¹` slice
  have hcd : ContDiffOn ℝ 1 (fun θ => U u z θ) Iθo := by
    refine (hS.Dz.curry_θ hz).of_le ?_
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  have haem : AEMeasurable (fun θ => U u z θ) (volume.restrict Iθo) :=
    hcd.continuousOn.aemeasurable measurableSet_Ioo
  -- integrability of the `V`-energy of the slice
  have hintV : MeasureTheory.IntegrableOn (fun θ => (V u z θ) ^ 2 * sigE θ) Iθo := by
    have h1' : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 0 (V u) z θ) Work.Spaces.Iθ := hV.1 z hzmem
    have h2' : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.w z) ^ 2 * ((V u z θ) ^ 2 * sigE θ)) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun h1' (fun θ hθ => ?_) measurableSet_Icc
      show Work.Spaces.HkIntegrand α 0 (V u) z θ = (Work.Spaces.w z) ^ 2 * ((V u z θ) ^ 2 * sigE θ)
      rw [hkIntegrand_zero_eq_of_mem α (V u) hθ]
      ring
    have h4' : MeasureTheory.IntegrableOn
        (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
          * ((Work.Spaces.w z) ^ 2 * ((V u z θ) ^ 2 * sigE θ))) Work.Spaces.Iθ :=
      MeasureTheory.Integrable.const_mul h2' _
    have h3' : MeasureTheory.IntegrableOn (fun θ => (V u z θ) ^ 2 * sigE θ) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun h4' (fun θ _ => ?_) measurableSet_Icc
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hwpos)), one_mul]
    exact (MeasureTheory.integrableOn_congr_set_ae
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2))).mpr h3'
  have hVnn : ∀ θ ∈ Iθo, 0 ≤ (V u z θ) ^ 2 * sigE θ := by
    intro θ hθ
    refine mul_nonneg (sq_nonneg _) ?_
    rw [sigE]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have hBnn : 0 ≤ ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo hVnn
  -- the two facts about the constant
  have hKnn : (0 : ℝ) ≤ (Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
      * (4 / (1 + Work.Spaces.eta) ^ 2) := by
    have h2'' : (0 : ℝ) ≤ 2 ^ Work.Spaces.eta :=
      Real.rpow_nonneg (by norm_num) _
    have h3'' : (0 : ℝ) ≤ 4 / (1 + Work.Spaces.eta) ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) h2'') h3''
  have hKle : (Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
      * (4 / (1 + Work.Spaces.eta) ^ 2) ≤ 40000 := by
    have h1'' : (Real.pi / 4) ^ (2 + Work.Spaces.eta) ≤ 1 := by
      refine Real.rpow_le_one (by positivity) ?_ (by linarith [hη0])
      rw [div_le_one (by norm_num : (0 : ℝ) < 4)]
      linarith [Real.pi_lt_four]
    have h2'' : (2 : ℝ) ^ Work.Spaces.eta ≤ 2 := by
      calc (2 : ℝ) ^ Work.Spaces.eta ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hη1)
        _ = 2 := Real.rpow_one 2
    have h3'' : 4 / (1 + Work.Spaces.eta) ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hη0]
    have h1''' : (0 : ℝ) ≤ (Real.pi / 4) ^ (2 + Work.Spaces.eta) :=
      Real.rpow_nonneg (by positivity) _
    have h2''' : (0 : ℝ) ≤ (2 : ℝ) ^ Work.Spaces.eta := Real.rpow_nonneg (by norm_num) _
    have h3''' : (0 : ℝ) ≤ 4 / (1 + Work.Spaces.eta) ^ 2 := by positivity
    calc (Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
          * (4 / (1 + Work.Spaces.eta) ^ 2)
        ≤ 1 * 2 * 4 :=
          mul_le_mul (mul_le_mul h1'' h2'' h2''' (by norm_num)) h3'' h3''' (by norm_num)
      _ = 8 := by norm_num
      _ ≤ 40000 := by norm_num
  -- the `∫⁻`-bound
  have hpow := powerHardySinOpen hη0 hη1 haem hcd h0 h1
  have hR : (∫⁻ θ in Iθo, ENNReal.ofReal
        ((deriv (fun θ' => U u z θ') θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      = ENNReal.ofReal (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintV
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hVnn)]
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
    rw [slice_deriv_eq hS hz hθ]
    simp only [sigE]
  have hmain : (∫⁻ θ in Iθo, ENNReal.ofReal
        ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ))
      ≤ ENNReal.ofReal (40000 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)) := by
    calc (∫⁻ θ in Iθo, ENNReal.ofReal
          ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ))
        ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
            * (4 / (1 + Work.Spaces.eta) ^ 2))
          * (∫⁻ θ in Iθo, ENNReal.ofReal
              ((deriv (fun θ' => U u z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
          simpa only [sig2] using hpow
      _ = ENNReal.ofReal ((Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
            * (4 / (1 + Work.Spaces.eta) ^ 2))
          * ENNReal.ofReal (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) := by rw [hR]
      _ = ENNReal.ofReal (((Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
            * (4 / (1 + Work.Spaces.eta) ^ 2))
          * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)) := (ENNReal.ofReal_mul hKnn).symm
      _ ≤ ENNReal.ofReal (40000 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKle hBnn)
  have hfin : (∫⁻ θ in Iθo, ENNReal.ofReal
      ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)) < ⊤ :=
    lt_of_le_of_lt hmain ENNReal.ofReal_lt_top
  -- a.e. strong measurability of the slice integrand
  have hcont_sig2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      Iθo :=
    (by fun_prop : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (by linarith only [hθ.1]) (by linarith only [hθ.2, Real.pi_pos]))))
  have haesm : AEStronglyMeasurable
      (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      (volume.restrict Iθo) := by
    have h1'' : AEStronglyMeasurable (fun θ => (U u z θ) ^ 2) (volume.restrict Iθo) :=
      (hcd.continuousOn.pow 2).aestronglyMeasurable measurableSet_Ioo
    have h2'' : AEStronglyMeasurable (fun θ => (Real.cos (2 * θ)) ^ 2)
        (volume.restrict Iθo) :=
      (((by fun_prop : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) Iθo).pow 2)).aestronglyMeasurable
        measurableSet_Ioo
    have h3'' : AEStronglyMeasurable (fun θ => sig2 θ) (volume.restrict Iθo) := by
      have hh : (fun θ => sig2 θ)
          = fun θ => (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
        funext θ; rw [sig2]
      rw [hh]
      exact hcont_sig2.aestronglyMeasurable measurableSet_Ioo
    exact (h1''.mul h2'').mul h3''
  have hnnslice : ∀ θ ∈ Iθo, 0 ≤ (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ := by
    intro θ hθ
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
    rw [sig2]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have hnn : 0 ≤ᵐ[volume.restrict Iθo]
      (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hnnslice
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) Iθo :=
    ⟨haesm, (MeasureTheory.hasFiniteIntegral_iff_ofReal hnn).mpr hfin⟩
  refine ⟨hint, ?_⟩
  have htoReal : (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      = (∫⁻ θ in Iθo, ENNReal.ofReal
          ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)).toReal := by
    have h1'' := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
    have h2'' := congrArg ENNReal.toReal h1''
    rwa [ENNReal.toReal_ofReal
      (MeasureTheory.setIntegral_nonneg measurableSet_Ioo hnnslice)] at h2''
  calc (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      = (∫⁻ θ in Iθo, ENNReal.ofReal
          ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)).toReal := htoReal
    _ ≤ (ENNReal.ofReal (40000 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = 40000 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) :=
        ENNReal.toReal_ofReal (by positivity)

/-! ## The target -/


end Work.FTS.EllipticEst.AeI1Fts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.unwMain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeS1

set_option autoImplicit false

theorem restrict_Iz_eq_Ioi :
    MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm

/-- **The a.e. slicewise constrained gap in `∫⁻` form**: `9 M ≤ B` with
`M = ∫⁻_z ofReal(w²)∫⁻_θ ofReal(u²)` and `B = ∫⁻_z ofReal(w²)∫⁻_θ ofReal((∂_θu)²)`. -/
theorem gap9_lintegral {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    ENNReal.ofReal 9 * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      ≤ (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
  have hgap := Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices α u G h hC
    (ae_integrableOn_pth_sq h)
  have hu := ae_integrableOn_u_sq h
  have hp := ae_integrableOn_pth_sq h
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (ENNReal.ofReal 9
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
        ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) := by
    rw [restrict_Iz_eq_Ioi]
    filter_upwards [hgap, hu, hp] with z hz hzu hzp
    have h1 : ENNReal.ofReal (9 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
        ≤ ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) :=
      ENNReal.ofReal_le_ofReal hz
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hzu
        (Filter.Eventually.of_forall fun θ => sq_nonneg _),
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hzp
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)] at h1
    exact mul_le_mul_of_nonneg_left h1 zero_le
  calc ENNReal.ofReal 9 * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal 9
          * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) := by
        rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal 9)
          (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
          ENNReal.ofReal_ne_top]
    _ = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (ENNReal.ofReal 9
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) := by
        refine lintegral_congr fun z => ?_
        ring
    _ ≤ _ := MeasureTheory.lintegral_mono_ae hpt

/-- **The main reduction**: the unweighted first-order energy inequality follows from the
`∫⁻`-form energy inequality `hineq` (with the constant `13/2 + 3α² + (3/2)α(5+α) < 9`). -/
theorem unwEnergyD_of
    (hineq : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)))
        + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
      ≤ ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
          * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z) ∧
        Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) ∧
        α ^ 2 * Work.Spaces.L2Sq (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z)
          + Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
        ≤ C * Work.Spaces.HkSq α 0 G := by
  refine ⟨16, by norm_num, ?_⟩
  intro α u G h
  -- ## the a.e. continuity of the fibres (needed for the gap)
  have hL0 := Work.FTS.EllipticEst.Dispatch.aeLeftLimitD α u G h
  have hC := Work.FTS.EllipticEst.H2W.AeProof.ae_continuousOn_slice h hL0
  -- ## abbreviations
  set A : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)) with hAdef
  set B : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) with hBdef
  set M : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)) with hMdef
  set K : ℝ := 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) with hKdef
  set H : ℝ := Work.Spaces.HkSq α 0 G with hHdef
  have hH0 : 0 ≤ H := by rw [hHdef]; exact Work.Spaces.HkSq_nonneg α 0 G
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have hα0 := h.hα.le
    nlinarith [sq_nonneg α]
  have hKle : K ≤ 8.657 := by
    rw [hKdef]
    have hα0 := h.hα.le
    have hα4 := h.hα4
    nlinarith [sq_nonneg α]
  -- ## the gap and the finiteness
  have hgap : ENNReal.ofReal 9 * M ≤ B := gap9_lintegral h hC
  have hM : M ≠ ⊤ := lintegral_ne_top_of_HkMem (Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h)
  have hKW : ENNReal.ofReal K * M ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM
  have hHH : ENNReal.ofReal (1 / 2) * ENNReal.ofReal H ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hRne : ENNReal.ofReal K * M + ENNReal.ofReal (1 / 2) * ENNReal.ofReal H ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hKW, hHH⟩
  have hineq' : ENNReal.ofReal (α ^ 2) * A + B
      ≤ ENNReal.ofReal K * M + ENNReal.ofReal (1 / 2) * ENNReal.ofReal H := hineq α u G h
  have hLne : ENNReal.ofReal (α ^ 2) * A + B ≠ ⊤ := ne_top_of_le_ne_top hRne hineq'
  have hA : A ≠ ⊤ := by
    intro hAtop
    refine hLne ?_
    have h1 : ENNReal.ofReal (α ^ 2) * A = ⊤ := by
      rw [hAtop, ENNReal.mul_top]
      exact ENNReal.ofReal_ne_zero_iff.mpr (pow_pos h.hα 2)
    rw [h1, top_add]
  have hB : B ≠ ⊤ := by
    intro hBtop
    exact hLne (by rw [hBtop, add_top])
  -- ## passing to `toReal`
  have hA2 : ENNReal.ofReal (α ^ 2) * A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA
  have hreal : α ^ 2 * A.toReal + B.toReal ≤ K * M.toReal + (1 / 2) * H := by
    have h1 := ENNReal.toReal_mono hRne hineq'
    rw [ENNReal.toReal_add hA2 hB, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg α),
      ENNReal.toReal_add hKW hHH, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.toReal_ofReal hH0] at h1
    exact h1
  have hgapR : 9 * M.toReal ≤ B.toReal := by
    have h1 := ENNReal.toReal_mono hB hgap
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 9)] at h1
  have hX0 : 0 ≤ A.toReal := ENNReal.toReal_nonneg
  have hY0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  have hW0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  -- ## the arithmetic
  have hWle : M.toReal ≤ B.toReal / 9 := by linarith
  have hKWle : K * M.toReal ≤ (K / 9) * B.toReal := by
    have h1 := mul_le_mul_of_nonneg_left hWle hK0
    calc K * M.toReal ≤ K * (B.toReal / 9) := h1
      _ = (K / 9) * B.toReal := by ring
  have hK9 : (1 : ℝ) / 30 ≤ 1 - K / 9 := by linarith
  have hYb : B.toReal ≤ 15 * H := by nlinarith [hreal, hgapR, hK0, hKle, hH0, hX0, hY0]
  have hXb : α ^ 2 * A.toReal ≤ (1 / 2) * H := by
    have hYnn : 0 ≤ (1 - K / 9) * B.toReal := mul_nonneg (by linarith) hY0
    nlinarith [hreal, hKWle, hYnn]
  have hfinal : α ^ 2 * A.toReal + B.toReal ≤ 16 * H := by nlinarith [hXb, hYb]
  -- ## the dictionary: `L2Mem` and the identification of the `∫⁻`-norms
  obtain ⟨hmA, hsqA⟩ := l2Dictionary (f := fun z θ => z * Work.Spaces.pz u z θ)
    (aesm_prod_gradW_sq h.smooth) (integrableOn_gradW_sq h) hA
  obtain ⟨hmB, hsqB⟩ := l2Dictionary (f := Work.Spaces.pth u)
    (aesm_prod_pthW_sq h.smooth) (integrableOn_pthW_sq h) hB
  have hsqA' : Work.Spaces.L2Sq (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z)
      = A.toReal := hsqA
  have hsqB' : Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
      = B.toReal := hsqB
  refine ⟨?_, ?_, ?_⟩
  · exact hmA
  · exact hmB
  · rw [hsqA', hsqB']
    exact hfinal

end Work.FTS.EllipticEst.AeS1
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch._scratch.AeSigmaCleanCopy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The angular weight `sin(2θ)^{-η}` of the level-`0` estimate. -/
local notation "σw" => Work.FTS.EllipticEst.sEta

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem θIntegral_const_mul (c : ℝ) (h : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, c * h θ) = c * ∫ θ in Work.Spaces.Iθ, h θ :=
  MeasureTheory.integral_const_mul c h

theorem zIntegral_const_mul (c : ℝ) (h : ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, c * h z) = c * ∫ z in Work.Spaces.Iz, h z :=
  MeasureTheory.integral_const_mul c h

/-! ## The weighted profile and the level-`0` integrand -/

/-- The squared radial weight `w(z)^2` of the level-`0` `z`-weight. -/
def phiW (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

theorem phiW_nonneg (z : ℝ) : 0 ≤ phiW z := by
  rw [phiW]; exact sq_nonneg _

theorem continuousOn_phiW_Ioi : ContinuousOn phiW (Set.Ioi 0) := by
  rw [show phiW = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 by
    funext z; rw [phiW]; simp [Work.Spaces.w]]
  refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)

theorem aestronglyMeasurable_phiW :
    MeasureTheory.AEStronglyMeasurable phiW
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h : MeasureTheory.AEStronglyMeasurable phiW
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    continuousOn_phiW_Ioi.aestronglyMeasurable measurableSet_Ioi
  rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact h

theorem aemeasurable_phiW :
    AEMeasurable phiW (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  aestronglyMeasurable_phiW.aemeasurable

/-- **The level-`0` integrand is the square of the weighted profile.** -/
theorem hkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Finset.range_one, Finset.sum_singleton]
  norm_num

/-- On `Iθ` the level-`0` integrand is `w(z)² · (g z θ)² · σ θ`. -/
theorem hkIntegrand_eq_phiW_mul (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ = phiW z * ((g z θ) ^ 2 * σw θ) := by
  rw [hkIntegrand_zero_eq, phiW, Work.FTS.EllipticEst.sEta, div_eq_mul_inv, sq]
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rcases eq_or_lt_of_le hsin with h0 | hpos
  · rw [← h0]
    have h1 : Work.Spaces.eta / 2 ≠ 0 := by
      rw [Work.Spaces.eta]; norm_num
    have h2 : -(Work.Spaces.eta) ≠ 0 := by
      rw [Work.Spaces.eta]; norm_num
    rw [Real.zero_rpow h1, Real.zero_rpow h2]
    ring
  · have hsq : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [← Real.rpow_add hpos,
        show -(Work.Spaces.eta / 2) + -(Work.Spaces.eta / 2) = -(Work.Spaces.eta) by ring]
    rw [← Real.rpow_neg hpos.le (Work.Spaces.eta / 2)]
    rw [show g z θ * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
          * (g z θ * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))))
        = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) by ring]
    rw [hsq]; ring

/-- **`HkSq α 0` in weighted-slice form**: `∫_z w(z)² ∫_θ (g z θ)² σ θ`. -/
theorem HkSq_eq_weighted (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = ∫ z in Work.Spaces.Iz, phiW z * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * σw θ) := by
  rw [Work.Spaces.HkSq]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [← θIntegral_const_mul (phiW z) (fun θ => (g z θ) ^ 2 * σw θ)]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hkIntegrand_eq_phiW_mul α g hθ)

/-- **The weighted slice data of an honest function.** -/
theorem integrableOn_of_HkMem_zero {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.Spaces.HkMem α 0 g) :
    (∀ z, 0 < z →
        MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * σw θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z =>
        phiW z * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * σw θ)) Work.Spaces.Iz := by
  constructor
  · intro z hz
    have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have h1 : MeasureTheory.IntegrableOn (fun θ => phiW z * ((g z θ) ^ 2 * σw θ))
        Work.Spaces.Iθ :=
      (hg.1 z hzI).congr_fun_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hkIntegrand_eq_phiW_mul α g hθ)
    have hφz : phiW z ≠ 0 := by
      rw [phiW]
      exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 (ne_of_gt (by linarith :
        (0 : ℝ) < 1 + z))) (pow_ne_zero 2 (ne_of_gt hz)))
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (phiW z)⁻¹ * (phiW z * ((g z θ) ^ 2 * σw θ))) Work.Spaces.Iθ :=
      h1.const_mul _
    refine h2.congr_fun ?_ measurableSet_Icc
    intro θ hθ
    show (phiW z)⁻¹ * (phiW z * ((g z θ) ^ 2 * σw θ)) = (g z θ) ^ 2 * σw θ
    rw [← mul_assoc, inv_mul_cancel₀ hφz, one_mul]
  · refine hg.2.congr_fun ?_ measurableSet_Ici
    intro z hz
    show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
        = phiW z * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * σw θ)
    rw [← θIntegral_const_mul (phiW z) (fun θ => (g z θ) ^ 2 * σw θ)]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hkIntegrand_eq_phiW_mul α g hθ)

/-- The weighted slice integrability in the shape used below. -/
theorem weighted_slice_integrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.Spaces.HkMem α 0 g) :
    MeasureTheory.IntegrableOn (fun z =>
      phiW z * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * σw θ)) Work.Spaces.Iz :=
  (integrableOn_of_HkMem_zero hg).2

/-- The slice mass `z ↦ ∫_θ (u z θ)² σ θ` is nonnegative. -/
theorem uMass_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * σw θ := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
    mul_nonneg (sq_nonneg _) ?_)
  exact Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ

/-- Almost every point of `Iz = [0,∞)` is positive. -/
theorem ae_pos_of_mem_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-! ## The first conjunct: the weighted radial profile is square integrable -/

/-- **`L2Mem` of the weighted radial first derivative**, from the honesty of `grad u`. -/
theorem l2mem_grad_profile {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
  have hmem : Work.Spaces.HkMem α 0 (grad u) := Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  have hgrad : grad u = fun z θ => z * Work.Spaces.pz u z θ := rfl
  constructor
  · intro z hz
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) z θ)
        Work.Spaces.Iθ := hmem.1 z hz
    refine h1.congr_fun_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hkIntegrand_zero_eq α (fun z θ => z * Work.Spaces.pz u z θ) z θ
  · have h2 : MeasureTheory.IntegrableOn (fun z => phiW z * (∫ θ in Work.Spaces.Iθ,
        ((fun z θ => z * Work.Spaces.pz u z θ) z θ) ^ 2 * σw θ)) Work.Spaces.Iz :=
      weighted_slice_integrable hmem
    refine h2.congr_fun ?_ measurableSet_Ici
    intro z _
    show phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)
      = ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    rw [← θIntegral_const_mul (phiW z) (fun θ => (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)]
    refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [← hkIntegrand_zero_eq α (fun z θ => z * Work.Spaces.pz u z θ) z θ,
      hkIntegrand_eq_phiW_mul α (fun z θ => z * Work.Spaces.pz u z θ) hθ]

/-! ## Comparison lemmas -/

/-- **The angular AM–GM pairing bound.** -/
theorem theta_pairing_le {f g : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * σw θ) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * σw θ) Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, f θ * g θ * σw θ|
      ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σw θ)
        + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * σw θ)) := by
  have hstep1 : |∫ θ in Work.Spaces.Iθ, f θ * g θ * σw θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |f θ * g θ * σw θ| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (fun θ => f θ * g θ * σw θ)
  have hint : MeasureTheory.IntegrableOn (fun θ => (1 / 2) *
      ((f θ) ^ 2 * σw θ + (g θ) ^ 2 * σw θ)) Work.Spaces.Iθ :=
    (hf.add hg).const_mul _
  have hstep2 : (∫ θ in Work.Spaces.Iθ, |f θ * g θ * σw θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, (1 / 2) * ((f θ) ^ 2 * σw θ + (g θ) ^ 2 * σw θ) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hint ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    show |f θ * g θ * σw θ| ≤ (1 / 2) * (f θ ^ 2 * σw θ + g θ ^ 2 * σw θ)
    have hσ : 0 ≤ σw θ := Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ
    have hkey : |f θ| * |g θ| ≤ (1 / 2) * ((f θ) ^ 2 + (g θ) ^ 2) := by
      have h := abs_mul (f θ) (g θ)
      nlinarith [sq_nonneg (|f θ| - |g θ|), sq_abs (f θ), sq_abs (g θ), h]
    rw [abs_mul, abs_mul, abs_of_nonneg hσ]
    calc |f θ| * |g θ| * σw θ ≤ ((1 / 2) * ((f θ) ^ 2 + (g θ) ^ 2)) * σw θ :=
          mul_le_mul_of_nonneg_right hkey hσ
      _ = (1 / 2) * ((f θ) ^ 2 * σw θ + (g θ) ^ 2 * σw θ) := by ring
  have hsplit : (∫ θ in Work.Spaces.Iθ, (1 / 2) * ((f θ) ^ 2 * σw θ + (g θ) ^ 2 * σw θ))
      = (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σw θ)
        + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * σw θ)) := by
    rw [θIntegral_const_mul (1 / 2), MeasureTheory.integral_add hf hg]
  linarith [hstep1, hstep2, hsplit]

/-- **A weighted comparison bound**: a function bounded by `C φ` integrates against a nonnegative
slice mass against `C φ · mass`. -/
theorem weighted_le_of_bound {c m : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmint : MeasureTheory.IntegrableOn (fun z => phiW z * m z) Work.Spaces.Iz)
    (hmnn : ∀ z, 0 ≤ m z)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), |c z| ≤ C * phiW z) :
    |∫ z in Work.Spaces.Iz, c z * m z| ≤ C * (∫ z in Work.Spaces.Iz, phiW z * m z) := by
  have hstep1 : |∫ z in Work.Spaces.Iz, c z * m z|
      ≤ ∫ z in Work.Spaces.Iz, |c z * m z| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (fun z => c z * m z)
  have hint : MeasureTheory.IntegrableOn (fun z => C * (phiW z * m z)) Work.Spaces.Iz :=
    hmint.const_mul C
  have hstep2 : (∫ z in Work.Spaces.Iz, |c z * m z|)
      ≤ ∫ z in Work.Spaces.Iz, C * (phiW z * m z) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => abs_nonneg _) hint ?_
    filter_upwards [hbound] with z hz
    rw [abs_mul]
    calc |c z| * |m z| ≤ (C * phiW z) * m z :=
          mul_le_mul hz (by rw [abs_of_nonneg (hmnn z)]) (abs_nonneg _)
            (mul_nonneg hC (phiW_nonneg z))
      _ = C * (phiW z * m z) := by ring
  have hsplit : (∫ z in Work.Spaces.Iz, C * (phiW z * m z))
      = C * (∫ z in Work.Spaces.Iz, phiW z * m z) :=
    zIntegral_const_mul C (fun z => phiW z * m z)
  linarith [hstep1, hstep2, hsplit]

/-- **The monotone-cutoff limit of the radial energy term.** -/
theorem tendsto_radial_energy (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hXint : MeasureTheory.IntegrableOn (fun z => phiW z *
      (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)) Work.Spaces.Iz)
    (χ : ℕ → ℝ → ℝ) (hχdiff : ∀ n, ContDiff ℝ 2 (χ n))
    (hχ01 : ∀ n z, 0 ≤ χ n z ∧ χ n z ≤ 1)
    (hχlim : ∀ z, 0 < z → Filter.Tendsto (fun n => χ n z) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => ∫ z in Work.Spaces.Iz, χ n z * phiW z *
        (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)) Filter.atTop
      (nhds (∫ z in Work.Spaces.Iz, phiW z *
        (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun z => phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))
    ?_ hXint ?_ ?_
  · intro n
    have h1 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => χ n z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      ((hχdiff n).continuous).aestronglyMeasurable
    have h2 : MeasureTheory.AEStronglyMeasurable phiW
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      aestronglyMeasurable_phiW
    have h3 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have hcont : ContinuousOn (fun p : ℝ × ℝ =>
          (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 * σw p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
        have hpz : ContinuousOn (Function.uncurry (Work.Spaces.pz u))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          ((Work.FTS.EllipticEst.smoothOpen_of_forall hsm).pz.forall 1).continuousOn
        have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
            (Set.Ioo 0 (Real.pi / 2)) :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
        have hsE : ContinuousOn (fun θ : ℝ => σw θ) (Set.Ioo 0 (Real.pi / 2)) :=
          hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt
            (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
              (by linarith [hθ.2, Real.pi_pos]))))
        have hz : ContinuousOn (fun p : ℝ × ℝ => p.1)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_fst
        have hθ : ContinuousOn (fun p : ℝ × ℝ => p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_snd
        exact ((hz.mul hpz).pow 2).mul (hsE.comp hθ (fun p hp => hp.2))
      exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
    have hprod : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => χ n z * phiW z *
          (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      exact (h1.mul h2).mul h3
    exact hprod
  · intro n
    filter_upwards with z
    have hφ : 0 ≤ phiW z := phiW_nonneg z
    have hmi : 0 ≤ ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        mul_nonneg (sq_nonneg _) ?_)
      exact Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hχ01 n z).1 hφ) hmi)]
    calc χ n z * phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)
        ≤ 1 * phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ) := by
          refine mul_le_mul_of_nonneg_right ?_ hmi
          exact mul_le_mul_of_nonneg_right (hχ01 n z).2 hφ
      _ = phiW z * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ) := by ring
  · filter_upwards [ae_pos_of_mem_Iz] with z hz
    have h1 : Filter.Tendsto (fun n => χ n z * phiW z) Filter.atTop (nhds (1 * phiW z)) :=
      (hχlim z hz).mul tendsto_const_nhds
    have h2 := h1.mul_const (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * σw θ)
    simpa only [one_mul] using h2

/-! ## The main theorem -/
end Work.FTS.EllipticEst.H2W.Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeW2SliceBundle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeW2SliceBundle` — the a.e. slice integrability bundle of the level-`0` a.e. class

For a datum `AeData α u G` of the almost-everywhere class of the level-`0` elliptic estimate,
for almost every `z > 0` the six angular fibres occurring in the truncated level-`0` energy
identity are integrable on `Iθ = [0,π/2]`:

`bslOp α u · u`, `Lzero u · u`, `∂_zzu · u`, `∂_zu · u`, `(z ∂_zu)²`, `u²`.

The proof is *pointwise in `z`* (the a.e. statement is therefore immediate): for `z > 0`

* the unweighted angular squares of `u`, `∂_zu` and `∂_zzu` are integrable because
  `HkMem α 0` of `u` (`Dispatch.hkMem_uM`), of `z ∂_zu` (`Dispatch.hkMem_gradUD`) and of
  `z²∂_zzu` (a field of `AeData`) gives the *weighted* integrability
  (`AngAWeak.integrableOn_slice_sq_mul_w_sq`), and the weight `w z ≠ 0` may be divided out;
  `G` is the same with the field `AeData.memG`;
* the products `G·u`, `(∂_zu)·u`, `(∂_zzu)·u` follow from `2|XY| ≤ X² + Y²` and the continuity
  of the slices on the open angular interval;
* `Lzero u · u` is *not* obtained from the `tan θ`-form of `Lzero` (whose middle term is not
  controlled by the available squares) but from the identity
  `Lzero u = G + α²z²∂_zzu + α(5+α)z∂_zu` on the open quadrant, which is `bslOp α u = G`
  (`AeData.eq`) rearranged;
* `bslOp α u · u` agrees with `G·u` on *all* of `Iθ`, since at the two endpoints the factor `u`
  vanishes (`AeData.dirZero`, `AeData.dirPi`) so both products are `0`.
-/

namespace Work.FTS.EllipticEst.Cores.Pieces

open MeasureTheory Set Filter

set_option autoImplicit false

/-- The unweighted angular square of a level-`0` honest function is integrable on `Iθ`, for
`z > 0`: divide the weight `(w z)²` out of `AngAWeak.integrableOn_slice_sq_mul_w_sq`. -/
private theorem aew2_integrableOn_sq_of_HkMem {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_mul_w_sq hmem (le_of_lt hz)).1.congr_fun
      (fun θ _ => by ring) measurableSet_Icc
  exact Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_of_mul_const hw h1

/-- `AM–GM` for a product of two functions whose angular squares are integrable. -/
private theorem aew2_integrableOn_mul_of_sq {f g : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => f θ * g θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => f θ * g θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' ((hf.add hg).const_mul (1 / 2)) hmeas ?_
  filter_upwards with θ
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f θ| - |g θ|), sq_abs (f θ), sq_abs (g θ)]

/-- A function continuous on the **open** quadrant has an a.e. strongly measurable angular
slice at every `z > 0`. -/
private theorem aew2_aesm_slice {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hf : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.AngAWeak.Qd) :
    MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.FTS.EllipticEst.AngAWeak.aestronglyMeasurable_of_continuousOn_Ioo <| by
    have hc : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry f p)
        Work.FTS.EllipticEst.AngAWeak.Qd := hf
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => Work.FTS.EllipticEst.AngAWeak.mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩)

theorem AeW2SliceBundle (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ := by
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  -- joint continuity of the slices on the open quadrant
  have hu_cont : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.AngAWeak.Qd :=
    (h.smooth 0).continuousOn_zero
  have hpz_cont : ContinuousOn (Function.uncurry (Work.Spaces.pz u))
      Work.FTS.EllipticEst.AngAWeak.Qd :=
    (Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ
      (U := Work.FTS.EllipticEst.AngAWeak.Qd)
      Work.FTS.EllipticEst.AngAWeak.isOpen_Qd (n := 0)
      (by simpa only [Work.FTS.EllipticEst.AngAWeak.Qd] using h.smooth 1)).continuousOn_zero
  have hpz2_cont : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 u))
      Work.FTS.EllipticEst.AngAWeak.Qd :=
    Work.FTS.EllipticEst.AngAWeak.continuousOn_uncurry_pzIter_two
      (fun n => by simpa only [Work.FTS.EllipticEst.AngAWeak.Qd] using h.smooth n)
  -- the degrees of freedom `u`, `z ∂_zu` are honest
  have hu_mem : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h
  have hg_mem : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  -- the angular squares
  have hU2 : MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
    aew2_integrableOn_sq_of_HkMem hu_mem hz
  have hG2 : MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2) Work.Spaces.Iθ :=
    aew2_integrableOn_sq_of_HkMem h.memG hz
  have hB2 : MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
      Work.Spaces.Iθ := by
    simpa only [Work.FTS.EllipticEst.H2W.Ae.grad] using aew2_integrableOn_sq_of_HkMem hg_mem hz
  have hR2 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2) Work.Spaces.Iθ :=
    aew2_integrableOn_sq_of_HkMem h.memRad2 hz
  have hP2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz u z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_of_mul_const (c := z ^ 2)
      (pow_ne_zero 2 (ne_of_gt hz))
      (hB2.congr_fun (fun θ _ => by ring) measurableSet_Icc)
  have hP22 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pzIter 2 u z θ) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_of_mul_const (c := (z ^ 2) ^ 2)
      (pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz)))
      (hR2.congr_fun (fun θ _ => by ring) measurableSet_Icc)
  -- the products
  have hGu : MeasureTheory.IntegrableOn (fun θ => G z θ * u z θ) Work.Spaces.Iθ :=
    aew2_integrableOn_mul_of_sq hG2 hU2
      ((Work.FTS.EllipticEst.AngAWeak.aesm_slice_G h hz).mul (aew2_aesm_slice hz hu_cont))
  have hPu : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ)
      Work.Spaces.Iθ :=
    aew2_integrableOn_mul_of_sq hP2 hU2
      ((aew2_aesm_slice hz hpz_cont).mul (aew2_aesm_slice hz hu_cont))
  have hP2u : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ)
      Work.Spaces.Iθ :=
    aew2_integrableOn_mul_of_sq hP22 hU2
      ((aew2_aesm_slice hz hpz2_cont).mul (aew2_aesm_slice hz hu_cont))
  -- `Lzero u · u` through the equation `Lzero u = G + α²z²∂_zzu + α(5+α)z∂_zu`
  have hLuu : MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
      Work.Spaces.Iθ := by
    have hsum : MeasureTheory.IntegrableOn (fun θ => G z θ * u z θ
        + ((α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 u z θ * u z θ)
          + (α * (5 + α) * z) * (Work.Spaces.pz u z θ * u z θ))) Work.Spaces.Iθ :=
      hGu.add ((hP2u.const_mul _).add (hPu.const_mul _))
    refine hsum.congr ?_
    filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hθ
    have hbsl : Work.Elliptic.bslOp α u z θ = G z θ := h.eq z hz θ hθ.1 hθ.2
    have hkey : Work.Elliptic.Lzero u z θ = G z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + (α * (5 + α) * z) * Work.Spaces.pz u z θ := by
      rw [← hbsl, Work.Elliptic.bslOp_apply]; ring
    rw [hkey]; ring
  -- `bslOp α u · u = G · u` on all of `Iθ` (both products vanish at the endpoints)
  have hBuu : MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
      Work.Spaces.Iθ := by
    refine hGu.congr_fun (fun θ hθ => ?_) measurableSet_Icc
    show G z θ * u z θ = Work.Elliptic.bslOp α u z θ * u z θ
    by_cases h0 : θ = 0
    · rw [h0, Work.FTS.EllipticEst.H2W.Ae.AeData.dirZero h z]; ring
    · by_cases hpi : θ = Real.pi / 2
      · rw [hpi, Work.FTS.EllipticEst.H2W.Ae.AeData.dirPi h z]; ring
      · rw [h.eq z hz θ (lt_of_le_of_ne hθ.1 (Ne.symm h0)) (lt_of_le_of_ne hθ.2 hpi)]
  exact ⟨hBuu, hLuu, hP2u, hPu, hB2, hU2⟩

end Work.FTS.EllipticEst.Cores.Pieces
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.lzeroProfInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-- `Iz = [0,∞)` and `(0,∞)` carry the same Lebesgue measure. -/
private theorem restrict_Iz_eq_Ioi :
    volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) :=
  (Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm

/-- **Angular AM–GM against the `ℋ⁰`-integrand.**  For `θ` in the open interval,
`w(z)² |f||g| ≤ (HkIntegrand α 0 f + HkIntegrand α 0 g)/2`; the two terms are handled
separately so that the result applies to the three pairings of the `Lzero` decomposition. -/
private theorem pair_le (α : ℝ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hp : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * |f z θ| * |g z θ|
      ≤ (Work.Spaces.HkIntegrand α 0 f z θ + Work.Spaces.HkIntegrand α 0 g z θ) / 2 := by
  have hamgm : |f z θ| * |g z θ| ≤ ((f z θ) ^ 2 + (g z θ) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|f z θ| - |g z θ|), sq_abs (f z θ), sq_abs (g z θ)]
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  calc (Work.Spaces.w z) ^ 2 * |f z θ| * |g z θ|
      = (Work.Spaces.w z) ^ 2 * (|f z θ| * |g z θ|) := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (((f z θ) ^ 2 + (g z θ) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hamgm hw2
    _ = ((Work.Spaces.w z) ^ 2 * (f z θ) ^ 2
          + (Work.Spaces.w z) ^ 2 * (g z θ) ^ 2) / 2 := by ring
    _ ≤ (Work.Spaces.HkIntegrand α 0 f z θ + Work.Spaces.HkIntegrand α 0 g z θ) / 2 := by
        linarith [Work.FTS.EllipticEst.Dispatch.sq_weight_le_Hk (z := z) α f hp,
          Work.FTS.EllipticEst.Dispatch.sq_weight_le_Hk (z := z) α g hp]

theorem lzeroProfInt (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ)
    (hφm : Measurable φ) (hφ0 : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1) :
    MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, |Work.Elliptic.Lzero u z θ * u z θ|)) Work.Spaces.Iz := by
  -- ## the smoothness of the datum on the open quadrant
  have hU : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hG : Work.FTS.EllipticEst.SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen (α := α) hU)
      (fun z θ hz hθ hθ' => h.eq z hz θ hθ hθ')
  have hR : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hU
  have hD : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Ae.grad u) := hU.Dz
  -- ## the honest `ℋ⁰`-memberships
  have hmu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h
  have hmg : Work.Spaces.HkMem α 0 G := h.memG
  have hmr : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) := h.memRad2
  have hmd : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  -- ## joint integrability of the four `ℋ⁰`-integrands
  have hIu := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hU hmu
  have hIg := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hG hmg
  have hIr := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hR hmr
  have hIdx := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hD hmd
  have hα5 : 0 ≤ α * (5 + α) := by nlinarith [h.hα]
  -- ## continuity of the radial weight on the quadrant
  have hw2cont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        = fun p : ℝ × ℝ => (((1 + p.1) ^ 2) / (p.1) ^ 2) ^ 2 := by
      funext p; simp only [Work.Spaces.w]
    rw [hfun]
    refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
    · exact (continuous_const.add continuous_fst).continuousOn.pow 2
    · exact continuous_fst.continuousOn.pow 2
    · intro p hp; exact pow_ne_zero 2 (ne_of_gt hp.1)
  -- ## continuity on the quadrant of the decomposed `Lzero`-pairing
  have hZcont : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2 * u p.1 p.2
      + α ^ 2 * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)
      + (α * (5 + α)) * ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2 * u p.1 p.2)
        Work.FTS.EllipticEst.Q0 := hG.continuousOn.mul hU.continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2)
        Work.FTS.EllipticEst.Q0 := hR.continuousOn
    have h3 : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2)
        Work.FTS.EllipticEst.Q0 := hD.continuousOn
    have h4 := (h2.mul hU.continuousOn).const_mul (α ^ 2)
    have h5 := (h3.mul hU.continuousOn).const_mul (α * (5 + α))
    exact (h1.add h4).add h5
  -- ## a.e. strong measurability of the (decomposed) target integrand
  have haesmφw : AEStronglyMeasurable
      (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2) Dispatch.nuFts :=
    ((hφm.comp measurable_fst).aestronglyMeasurable).mul
      (Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 hw2cont)
  have haesmZ : AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2
      * |G p.1 p.2 * u p.1 p.2
        + α ^ 2 * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)
        + (α * (5 + α)) * ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)|) Dispatch.nuFts :=
    haesmφw.mul (Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 hZcont).norm
  -- ## the majorant (in the association produced by `Integrable.add`)
  have hMajInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (1 / 2) * (Work.Spaces.HkIntegrand α 0 G p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      + ((α ^ 2 / 2) * (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
        + ((α * (5 + α) / 2) * (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)))) Dispatch.nuFts :=
    ((hIg.add hIu).const_mul (1 / 2)).add
      (((hIr.add hIu).const_mul (α ^ 2 / 2)).add ((hIdx.add hIu).const_mul (α * (5 + α) / 2)))
  have hMajInt' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (1 / 2) * (Work.Spaces.HkIntegrand α 0 G p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      + (α ^ 2 / 2) * (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      + ((α * (5 + α) / 2) * (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2))) Dispatch.nuFts :=
    hMajInt.congr (Filter.Eventually.of_forall fun p => by ring)
  -- ## the pointwise bound
  have hbound : ∀ᵐ p ∂Dispatch.nuFts, ‖φ p.1 * (Work.Spaces.w p.1) ^ 2
      * |G p.1 p.2 * u p.1 p.2
        + α ^ 2 * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)
        + (α * (5 + α)) * ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)|‖
      ≤ (1 / 2) * (Work.Spaces.HkIntegrand α 0 G p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
        + (α ^ 2 / 2) * (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)
        + ((α * (5 + α) / 2) * (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) p.1 p.2
            + Work.Spaces.HkIntegrand α 0 u p.1 p.2)) := by
    filter_upwards [Dispatch.ae_mem_Ioo_nu] with p hp
    obtain ⟨z, θ⟩ := p
    set X : ℝ := G z θ * u z θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
      + (α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ) with hX
    have hGterm : (Work.Spaces.w z) ^ 2 * |G z θ| * |u z θ|
        ≤ (Work.Spaces.HkIntegrand α 0 G z θ + Work.Spaces.HkIntegrand α 0 u z θ) / 2 :=
      pair_le α G u hp
    have hRterm : (Work.Spaces.w z) ^ 2 * |z ^ 2 * Work.Spaces.pzIter 2 u z θ| * |u z θ|
        ≤ (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
            + Work.Spaces.HkIntegrand α 0 u z θ) / 2 :=
      pair_le α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) u hp
    have hXterm : (Work.Spaces.w z) ^ 2 * |z * Work.Spaces.pz u z θ| * |u z θ|
        ≤ (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
            + Work.Spaces.HkIntegrand α 0 u z θ) / 2 :=
      pair_le α (Work.FTS.EllipticEst.H2W.Ae.grad u) u hp
    have hdec : |X| ≤ |G z θ| * |u z θ| + α ^ 2 * (|z ^ 2 * Work.Spaces.pzIter 2 u z θ| * |u z θ|)
          + (α * (5 + α)) * (|z * Work.Spaces.pz u z θ| * |u z θ|) := by
      rw [hX]
      have hAB := abs_add_le (G z θ * u z θ)
        (α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ))
      have hABC := abs_add_le
        (G z θ * u z θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ))
        ((α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ))
      have h1 : |G z θ * u z θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
          + (α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ)|
          ≤ |G z θ * u z θ| + |α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)|
            + |(α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ)| := by
        linarith [hABC, hAB]
      refine h1.trans (le_of_eq ?_)
      simp only [abs_mul, abs_of_nonneg (sq_nonneg α), abs_of_nonneg hα5]
    have hstep1 : φ z * (Work.Spaces.w z) ^ 2 * |X| ≤ (Work.Spaces.w z) ^ 2 * |X| := by
      have h : φ z * ((Work.Spaces.w z) ^ 2 * |X|) ≤ 1 * ((Work.Spaces.w z) ^ 2 * |X|) :=
        mul_le_mul_of_nonneg_right (hφ1 z)
          (mul_nonneg (sq_nonneg (Work.Spaces.w z)) (abs_nonneg X))
      linarith [h]
    have hnnφ : (0 : ℝ) ≤ φ z * (Work.Spaces.w z) ^ 2 * |X| :=
      mul_nonneg (mul_nonneg (hφ0 z) (sq_nonneg (Work.Spaces.w z))) (abs_nonneg X)
    rw [Real.norm_eq_abs, abs_of_nonneg hnnφ]
    calc φ z * (Work.Spaces.w z) ^ 2 * |X|
        ≤ (Work.Spaces.w z) ^ 2 * |X| := hstep1
      _ ≤ (Work.Spaces.w z) ^ 2
          * (|G z θ| * |u z θ| + α ^ 2 * (|z ^ 2 * Work.Spaces.pzIter 2 u z θ| * |u z θ|)
            + (α * (5 + α)) * (|z * Work.Spaces.pz u z θ| * |u z θ|)) :=
          mul_le_mul_of_nonneg_left hdec (sq_nonneg (Work.Spaces.w z))
      _ = (Work.Spaces.w z) ^ 2 * |G z θ| * |u z θ|
          + α ^ 2 * ((Work.Spaces.w z) ^ 2 * |z ^ 2 * Work.Spaces.pzIter 2 u z θ| * |u z θ|)
          + (α * (5 + α))
            * ((Work.Spaces.w z) ^ 2 * |z * Work.Spaces.pz u z θ| * |u z θ|) := by ring
      _ ≤ (Work.Spaces.HkIntegrand α 0 G z θ + Work.Spaces.HkIntegrand α 0 u z θ) / 2
          + α ^ 2 * ((Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ) / 2)
          + (α * (5 + α))
            * ((Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ) / 2) := by
          have h1 := mul_le_mul_of_nonneg_left hRterm (sq_nonneg α)
          have h2 := mul_le_mul_of_nonneg_left hXterm hα5
          linarith [hGterm, h1, h2]
      _ = (1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ + Work.Spaces.HkIntegrand α 0 u z θ)
          + (α ^ 2 / 2) * (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ)
          + ((α * (5 + α) / 2)
            * (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ)) := by ring
  -- ## joint integrability of the decomposed integrand
  have hIntDec : MeasureTheory.Integrable (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2
      * |G p.1 p.2 * u p.1 p.2
        + α ^ 2 * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)
        + (α * (5 + α)) * ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)|) Dispatch.nuFts :=
    hMajInt'.mono' haesmZ hbound
  -- ## the a.e. identity `Lzero u = G + α²z²∂_z²u + α(5+α)z∂_zu` on the quadrant
  have hae : (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2
        * |Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2|)
      =ᵐ[Dispatch.nuFts] (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2
        * |G p.1 p.2 * u p.1 p.2
          + α ^ 2 * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)
          + (α * (5 + α)) * ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)|) := by
    filter_upwards [Dispatch.ae_mem_Ioi_nu, Dispatch.ae_mem_Ioo_nu] with p hpz hpθ
    obtain ⟨z, θ⟩ := p
    have heq := h.eq z hpz θ hpθ.1 hpθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hL : Work.Elliptic.Lzero u z θ
        = G z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + α * (5 + α) * (z * Work.Spaces.pz u z θ) := by linarith
    have hinner : (G z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + α * (5 + α) * (z * Work.Spaces.pz u z θ)) * u z θ
        = G z θ * u z θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
          + (α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ) := by ring
    rw [hL, hinner]
  have hInt : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => φ z * (Work.Spaces.w z) ^ 2
        * |Work.Elliptic.Lzero u z θ * u z θ|)) Dispatch.nuFts :=
    hIntDec.congr hae.symm
  -- ## integrability of the outer `z`-profile integral by Fubini
  have hIntIz : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => φ z * (Work.Spaces.w z) ^ 2
        * |Work.Elliptic.Lzero u z θ * u z θ|))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [restrict_Iz_eq_Ioi]
    exact hInt
  refine hIntIz.integral_prod_left.congr (Filter.Eventually.of_forall fun z => ?_)
  show (∫ θ in Work.Spaces.Iθ, φ z * (Work.Spaces.w z) ^ 2
        * |Work.Elliptic.Lzero u z θ * u z θ|)
      = φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, |Work.Elliptic.Lzero u z θ * u z θ|)
  rw [MeasureTheory.integral_const_mul]

end

end Work.FTS.EllipticEst.Prop.CutEnergyAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.WProd6

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `HgInt6 α g z = ∫_θ HkIntegrand α 6 g z θ`, the angular integral of the `ℋ⁶`-integrand of
`g` at fixed radius.  (Its `z`-integral is `HkSq α 6 g` by definition.) -/
def HgInt6 (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, HkIntegrand α 6 g z θ

/-- **The pointwise majorant of the `𝒲^{6,∞}`-priced product rule**: the `ℋ⁶`-integrand of `g`
plus the angular contribution of the mean-term bound for the radial slots of `g` (`HgInt6`) and
of the angular `L²`-norms `Aang` of the mixed slots of `g`, multiplied by the surviving angular
factor `TW`. -/
def GmajW6 (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  HkIntegrand α 6 g z θ
    + (HgInt6 α g z
        + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z)
      * Work.FTS.OpenPkg.WProdWin.TW α θ

/-! ## Elementary properties -/

theorem HgInt6_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ HgInt6 α g z :=
  integral_nonneg fun θ => HkIntegrand_nonneg α 6 g z θ

theorem Aang_nonneg6 (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ) (z : ℝ) :
    0 ≤ Work.FTS.H2.WPQ.Aang α g d z :=
  setIntegral_nonneg measurableSet_Icc fun σ _ => sq_nonneg _

theorem sum_Aang_nonneg6 (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z :=
  Finset.sum_nonneg fun d _ => Aang_nonneg6 α g d z

theorem GmajW6_nonneg {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    0 ≤ GmajW6 α g z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  refine add_nonneg (HkIntegrand_nonneg α 6 g z θ)
    (mul_nonneg (add_nonneg (HgInt6_nonneg α g z)
      (mul_nonneg (inv_nonneg.mpr hγ1.le) (sum_Aang_nonneg6 α g z)))
      (Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθ))

/-- The `ℋ⁶`-integrand of `g` is dominated by the majorant. -/
theorem HkIntegrand_le_GmajW6 {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Iθ) :
    HkIntegrand α 6 g z θ ≤ GmajW6 α g z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  refine le_add_of_nonneg_right (mul_nonneg (add_nonneg (HgInt6_nonneg α g z)
    (mul_nonneg (inv_nonneg.mpr hγ1.le) (sum_Aang_nonneg6 α g z)))
    (Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθ))

/-- The `ℋ⁶`-integrand vanishes whenever `sin(2θ) = 0` (the level-six instance of
`Work.FTS.H2.WPQ.HkIntegrand_eq_zero_of_sin_two_eq_zero`). -/
theorem HkIntegrand6_eq_zero_of_sin_two_eq_zero {α : ℝ} (hα : gam α ≠ 0)
    {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    HkIntegrand α 6 F z θ = 0 := by
  have hη : (eta / 2 : ℝ) ≠ 0 := by norm_num [eta]
  have hg : -(gam α / 2) ≠ 0 := by
    intro hc
    exact hα (by linarith [neg_eq_zero.mp hc])
  simp only [HkIntegrand, Wt, wTheta]
  rw [h, Real.zero_rpow hη, Real.zero_rpow hg]
  simp

/-- The sum of the angular `L²`-norms of the mixed slots of `g` is dominated by the mean term. -/
theorem sum_Aang_le_HgInt6 {α : ℝ} {g : ℝ → ℝ → ℝ} (hgm : HkMem α 6 g) {z : ℝ}
    (hz : z ∈ Iz) :
    ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z ≤ 6 * HgInt6 α g z := by
  have hd : ∀ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z ≤ HgInt6 α g z := by
    intro d hd6
    have hd5 : d ≤ 5 := Nat.le_of_lt_succ (Finset.mem_range.mp hd6)
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hgm.1 z hz)
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ _ =>
        sq_le_HkIntegrand_mixed α 6 g z θ 1 d le_rfl (by omega))
  calc ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z
      ≤ ∑ _d ∈ Finset.range 6, HgInt6 α g z := Finset.sum_le_sum hd
    _ = 6 * HgInt6 α g z := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num

/-- **The mean term controls the radial slots of `g`**:
`w(z)² ∫_σ (D_z^d g(z,σ))² ≤ HgInt6 α g z` for `d ≤ 6`. -/
theorem w_sq_mul_slice_le_HgInt6 {α : ℝ} {g : ℝ → ℝ → ℝ} (hgm : HkMem α 6 g) {d : ℕ}
    (hd : d ≤ 6) {z : ℝ} (hz : 0 < z) :
    (w z) ^ 2 * (∫ σ in Iθ, (DzIter d g z σ) ^ 2) ≤ HgInt6 α g z := by
  have hzI : z ∈ Iz := le_of_lt hz
  have hdiv : (w z) ^ 2 * (∫ σ in Iθ, (DzIter d g z σ) ^ 2)
      = ∫ σ in Iθ, (w z) ^ 2 * (DzIter d g z σ) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
  rw [hdiv]
  refine integral_mono_of_nonneg
    (Eventually.of_forall fun σ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hgm.1 z hzI) ?_
  filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
  have hs : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  have hspos : 0 < (Real.sin (2 * σ)) ^ (eta / 2) := Real.rpow_pos_of_pos hs _
  have hkey : DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))
        * (Real.sin (2 * σ)) ^ (eta / 2) = DzIter d g z σ * w z := by
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hspos)]
  have hsq : ((Real.sin (2 * σ)) ^ (eta / 2)) ^ (2 : ℕ) = (Real.sin (2 * σ)) ^ eta := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    rw [eta]; ring
  calc (w z) ^ 2 * (DzIter d g z σ) ^ 2
      = (DzIter d g z σ * w z) ^ 2 := by ring
    _ = (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))
          * (Real.sin (2 * σ)) ^ (eta / 2)) ^ 2 := by rw [hkey]
    _ = (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))) ^ 2
          * (Real.sin (2 * σ)) ^ eta := by
        rw [mul_pow, hsq]
    _ ≤ (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))) ^ 2 * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact Real.rpow_le_one hs.le (Real.sin_le_one _) (by norm_num [eta])
    _ ≤ HkIntegrand α 6 g z σ := by
        rw [mul_one]
        exact sq_le_HkIntegrand_z α 6 g z σ d hd

/-- `HgInt6` integrates to `HkSq α 6 g` (definitional). -/
theorem HgInt6_z_integral (α : ℝ) (g : ℝ → ℝ → ℝ) :
    (∫ z in Iz, HgInt6 α g z) = HkSq α 6 g := rfl

/-- The angular slice of the majorant is integrable, for every `z ∈ Iz`. -/
theorem GmajW6_integrableOn_theta {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 6 g) {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => GmajW6 α g z θ) Iθ := by
  have h2 : IntegrableOn (fun θ => (HgInt6 α g z
      + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z)
        * Work.FTS.OpenPkg.WProdWin.TW α θ) Iθ :=
    (Work.FTS.OpenPkg.WProdWin.TW_integrable hα hα1).const_mul _
  refine Integrable.congr ((hgm.1 z hz).add h2) ?_
  filter_upwards with θ
  simp only [Pi.add_apply, GmajW6]

/-- The angular integral of the majorant at a fixed radius. -/
theorem GmajW6_theta_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 6 g) {z : ℝ} (hz : z ∈ Iz) :
    (∫ θ in Iθ, GmajW6 α g z θ) ≤ (1 + 700 * (1 + 6 * (gam α - 1)⁻¹)) * HgInt6 α g z := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hhg : IntegrableOn (fun θ => HkIntegrand α 6 g z θ) Iθ := hgm.1 z hz
  have hsum : ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z ≤ 6 * HgInt6 α g z :=
    sum_Aang_le_HgInt6 hgm hz
  have h2 : IntegrableOn (fun θ => (HgInt6 α g z
      + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z)
        * Work.FTS.OpenPkg.WProdWin.TW α θ) Iθ :=
    (Work.FTS.OpenPkg.WProdWin.TW_integrable hα hα1).const_mul _
  have hsplit : (∫ θ in Iθ, GmajW6 α g z θ)
      = HgInt6 α g z + (HgInt6 α g z
          + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z)
            * (∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ) := by
    have hfun : (fun θ : ℝ => GmajW6 α g z θ)
        = fun θ : ℝ => HkIntegrand α 6 g z θ
            + (HgInt6 α g z + (gam α - 1)⁻¹
                * ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z)
              * Work.FTS.OpenPkg.WProdWin.TW α θ := by
      funext θ; rw [GmajW6]
    rw [hfun, MeasureTheory.integral_add hhg h2, MeasureTheory.integral_const_mul]
    rfl
  rw [hsplit]
  have hT := Work.FTS.OpenPkg.WProdWin.TW_integral_le hα hα1
  have hTnn : 0 ≤ ∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθ)
  have hbr : HgInt6 α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6,
        Work.FTS.H2.WPQ.Aang α g d z
      ≤ HgInt6 α g z + (gam α - 1)⁻¹ * (6 * HgInt6 α g z) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hγinv)
  have hmain : (HgInt6 α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6,
        Work.FTS.H2.WPQ.Aang α g d z) * (∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ)
      ≤ (HgInt6 α g z + (gam α - 1)⁻¹ * (6 * HgInt6 α g z)) * 700 :=
    mul_le_mul hbr hT hTnn
      (add_nonneg (HgInt6_nonneg α g z) (mul_nonneg hγinv (mul_nonneg (by norm_num)
        (HgInt6_nonneg α g z))))
  calc HgInt6 α g z + (HgInt6 α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6,
        Work.FTS.H2.WPQ.Aang α g d z) * (∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ)
      ≤ HgInt6 α g z + (HgInt6 α g z + (gam α - 1)⁻¹ * (6 * HgInt6 α g z)) * 700 :=
        add_le_add le_rfl hmain
    _ = (1 + 700 * (1 + 6 * (gam α - 1)⁻¹)) * HgInt6 α g z := by ring


end Work.FTS.StrongPersist.H6Rows.WProd6
end
end
