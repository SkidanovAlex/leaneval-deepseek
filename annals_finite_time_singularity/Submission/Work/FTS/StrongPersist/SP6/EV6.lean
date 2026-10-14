import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSix
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.StrongPersist.SP6.PthEVzR
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3BadAux.slot_slice_le
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.MismatchHardSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-slice bound for the `b = 5` crux

See `MismatchHardAux` for the Agmon input and `MismatchHardB5` for the assembly.
-/
namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

theorem mh_slice_bound {α : ℝ} {A f : ℝ → ℝ → ℝ} {K4 Cmz : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hAsm : Work.FTS.EllipticEst.SmoothOpen A) (hfsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hA6 : Work.Spaces.HkMem α 6 A) (hf6 : Work.Spaces.HkMem α 6 f)
    (hAsl : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth A z θ) ^ 2) ≤ Cmz * K4 ^ 2)
    (hAgmon : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter 5 f z θ) ^ 2
        ≤ (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ') ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ' in Work.Spaces.Iθ, (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'')) θ' ^ 2
                * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α))) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.Integrable (fun θ : ℝ => |Work.FTS.TransportS.leafGam α z θ
          * Work.Spaces.mixed 0 1 A z θ * Work.Spaces.DzIter 5 f z θ
          * Work.Spaces.mixed 5 1 f z θ|) (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∫ θ in Work.Spaces.Iθ, |Work.FTS.TransportS.leafGam α z θ
          * Work.Spaces.mixed 0 1 A z θ * Work.Spaces.DzIter 5 f z θ
          * Work.Spaces.mixed 5 1 f z θ|)
        ≤ Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
            * ((Work.Spaces.w z) ^ 2
                * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ) ^ 2)
                  + (∫ θ in Work.Spaces.Iθ,
                      (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'')) θ ^ 2
                        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) := by
    set mm : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ) ^ 2 with hmm
    set IIz : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
        (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'')) θ ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hII
    have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have hγeq : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
    have hcontG : ContinuousOn (fun p : ℝ × ℝ => |Work.FTS.TransportS.leafGam α p.1 p.2
        * Work.Spaces.mixed 0 1 A p.1 p.2 * Work.Spaces.DzIter 5 f p.1 p.2
        * Work.Spaces.mixed 5 1 f p.1 p.2|) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.contOn_leafGam α).mul
        (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hAsm.mixed 0 1))).mul
        (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hfsm.DzIter 5))).mul
        (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hfsm.mixed 5 1))).abs
    intro z hz
    set Ag : ℝ := Real.sqrt ((4 / Real.pi) * mm z + (200 / (Work.Spaces.gam α - 1)) * IIz z)
      with hAg
    have hAgnn : 0 ≤ Ag := Real.sqrt_nonneg _
    -- (1) the pointwise majorant
    have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 0 1 A z θ
            * Work.Spaces.DzIter 5 f z θ * Work.Spaces.mixed 5 1 f z θ|
          ≤ (Work.Spaces.w z) ^ 2 * Ag * ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
              * (|Work.Spaces.pth A z θ|
                * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ|)) := by
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
      have hσ : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := Real.rpow_nonneg hσ.le _
      have hwnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hV : |Work.Spaces.DzIter 5 f z θ| ≤ Ag := by
        rw [← Real.sqrt_sq_eq_abs, hAg]
        exact Real.sqrt_le_sqrt (hAgmon z θ hz hθ0 hθ1)
      have hid : Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 0 1 A z θ
            * Work.Spaces.DzIter 5 f z θ * Work.Spaces.mixed 5 1 f z θ
          = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
              * Work.Spaces.pth A z θ * Work.Spaces.DzIter 5 f z θ
              * (Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) := by
        have h1 : Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 0 1 A z θ
            = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
              * Work.Spaces.pth A z θ := by
          have h := leafGam_mul_Dth_eq (α := α) (z := z) (θ := θ) hσ A
          simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
            Work.Spaces.DthIter_zero] using h
        have h2 : Work.Spaces.mixed 5 1 f z θ
            = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ :=
          Work.FTS.TransportS.SlotT2.supOpen_mixed_eq_sin_pth hfsm 5 hz ⟨hθ0, hθ1⟩
        rw [h1, h2]
      have hrew : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
            * Work.Spaces.pth A z θ * Work.Spaces.DzIter 5 f z θ
            * (Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ)
          = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
              * Work.Spaces.pth A z θ * Work.Spaces.DzIter 5 f z θ
              * Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ := by
        rw [show (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
              * Work.Spaces.pth A z θ * Work.Spaces.DzIter 5 f z θ
              * (Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ)
            = (Work.Spaces.w z) ^ 2
              * ((Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * Real.sin (2 * θ))
              * Work.Spaces.pth A z θ * Work.Spaces.DzIter 5 f z θ
              * Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ from by ring,
          mh_one_sub_gam_mul (γ := Work.Spaces.gam α) hσ]
      have habs : |(Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            * Work.Spaces.pth A z θ * Work.Spaces.DzIter 5 f z θ
            * Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ|
          = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            * |Work.Spaces.pth A z θ| * |Work.Spaces.DzIter 5 f z θ|
            * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hwnn, abs_of_nonneg hσnn]
      calc |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 0 1 A z θ
            * Work.Spaces.DzIter 5 f z θ * Work.Spaces.mixed 5 1 f z θ|
          = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            * |Work.Spaces.pth A z θ| * |Work.Spaces.DzIter 5 f z θ|
            * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ| := by rw [hid, hrew, habs]
        _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            * |Work.Spaces.pth A z θ| * Ag
            * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ| := by
            refine mul_le_mul_of_nonneg_right ?_
              (abs_nonneg (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ))
            refine mul_le_mul_of_nonneg_left hV ?_
            positivity
        _ = (Work.Spaces.w z) ^ 2 * Ag * ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
              * (|Work.Spaces.pth A z θ|
                * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ|)) := by ring
    -- (2) the Cauchy–Schwarz at the bounded weight
    have hAnn : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth A z θ) ^ 2 := by
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
      show (0 : ℝ) ≤ Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth A z θ) ^ 2
      exact mul_nonneg (Real.rpow_nonneg
        (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le _) (sq_nonneg _)
    have hBnn : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) ^ 2 := by
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
      show (0 : ℝ) ≤ Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) ^ 2
      exact mul_nonneg (Real.rpow_nonneg
        (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le _) (sq_nonneg _)
    have hAint : MeasureTheory.Integrable (fun θ : ℝ =>
        (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth A z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine MeasureTheory.Integrable.congr
        (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
          (α := α) (f := A) (b := 0) (a := 1) hα0 hAsm hA6 (by norm_num) (by norm_num) hz) ?_
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
      show Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 0 1 A z θ) ^ 2
        = Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth A z θ) ^ 2
      have hσ : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hm := Work.FTS.TransportS.SlotT2.supOpen_mixed_eq_sin_pth hAsm 0 hz ⟨hθ0, hθ1⟩
      rw [hm, mul_pow, ← mul_assoc, mh_neg_gam_mul_sq (γ := Work.Spaces.gam α) hσ]
      simp only [Work.Spaces.DzIter_zero]
    have hBint : MeasureTheory.Integrable (fun θ : ℝ =>
        (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine MeasureTheory.Integrable.congr
        (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
          (α := α) (f := f) (b := 5) (a := 1) hα0 hfsm hf6 (by norm_num) (by norm_num) hz) ?_
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
      show Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 5 1 f z θ) ^ 2
        = Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) ^ 2
      have hdw : (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'')) θ ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          = (Work.Spaces.mixed 5 1 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        Work.FTS.OpenPkg.ProdOpen.deriv_mixed_weight α hfsm 5 0 hz ⟨hθ0, hθ1⟩
      calc Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 5 1 f z θ) ^ 2
          = (Work.Spaces.mixed 5 1 f z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by ring
        _ = (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'')) θ ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := hdw.symm
        _ = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) ^ 2 := by
            simp only [Work.Spaces.pth]; ring
    obtain ⟨hcs_int, hcs_le⟩ := cs_sqrt_int (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      hAint hBint hAnn hBnn
    have hprod : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.pth A z θ) ^ 2)
          * Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) ^ 2)
        = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (|Work.Spaces.pth A z θ| * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ|) := by
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
      have hσ : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := Real.rpow_nonneg hσ.le _
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_mul' _ (sq_nonneg _),
        Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
      rw [show Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
              * |Work.Spaces.pth A z θ|
              * (Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
                * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ|)
            = (Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
                * Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
              * (|Work.Spaces.pth A z θ|
                * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ|) from by ring,
        Real.mul_self_sqrt hσnn]
    have hRHSint : MeasureTheory.Integrable (fun θ : ℝ => (Work.Spaces.w z) ^ 2 * Ag
        * ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (|Work.Spaces.pth A z θ|
            * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ|)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.Integrable.congr (hcs_int.const_mul ((Work.Spaces.w z) ^ 2 * Ag))
        (hprod.mono (fun θ hθ => by simp only [hθ]))
    have hGaesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ =>
        |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 0 1 A z θ
          * Work.Spaces.DzIter 5 f z θ * Work.Spaces.mixed 5 1 f z θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _
        (by simpa only [Function.uncurry_apply_pair] using hcontG) hz
    refine ⟨MeasureTheory.Integrable.mono' hRHSint hGaesm
      (hpt.mono (fun θ hθ => by rwa [Real.norm_of_nonneg (abs_nonneg _)])), ?_⟩
    -- (3) the chain
    have hstep1 := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hRHSint hpt
    have hstep2 := MeasureTheory.integral_const_mul
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) ((Work.Spaces.w z) ^ 2 * Ag)
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (|Work.Spaces.pth A z θ| * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ|))
    have hstep3 : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            * (|Work.Spaces.pth A z θ|
              * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ|))
        = ∫ θ in Work.Spaces.Iθ, Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.pth A z θ) ^ 2)
            * Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) ^ 2) :=
      MeasureTheory.integral_congr_ae (hprod.mono (fun θ hθ => hθ.symm))
    have hBval : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) ^ 2) = IIz z := by
      rw [hII]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [Work.Spaces.pth]
      ring
    have hstep4 : (∫ θ in Work.Spaces.Iθ,
          Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.pth A z θ) ^ 2)
            * Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) ^ 2))
        ≤ Real.sqrt (Cmz * K4 ^ 2) * Real.sqrt (IIz z) := by
      refine hcs_le.trans ?_
      rw [hBval]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hAsl z hz)) (Real.sqrt_nonneg _)
    have hstep5 : (Work.Spaces.w z) ^ 2 * Ag * (Real.sqrt (Cmz * K4 ^ 2) * Real.sqrt (IIz z))
        ≤ Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
            * ((Work.Spaces.w z) ^ 2 * (mm z + IIz z)) := by
      have hmmnn : 0 ≤ mm z := MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
      have hIInn : 0 ≤ IIz z := by
        rw [← hBval]
        refine MeasureTheory.integral_nonneg_of_ae ?_
        refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
        show (0 : ℝ) ≤ Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) ^ 2
        exact mul_nonneg (Real.rpow_nonneg
          (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le _) (sq_nonneg _)
      have hCnn : 0 ≤ Real.sqrt (Cmz * K4 ^ 2) := Real.sqrt_nonneg _
      have hkey : Ag * Real.sqrt (IIz z)
          ≤ Real.sqrt (201 / (Work.Spaces.gam α - 1)) * (mm z + IIz z) := by
        have h1 : (1 : ℝ) / (Work.Spaces.gam α - 1) = 10 / α := by rw [hγeq]; ring
        have h2 : (4 : ℝ) / Real.pi ≤ 1 / (Work.Spaces.gam α - 1) := by
          rw [h1]
          have h3 : (4 : ℝ) / Real.pi ≤ 10 := by
            rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
          have h4 : (10 : ℝ) ≤ 10 / α := by
            rw [le_div_iff₀ hα0]; nlinarith
          linarith
        have h5 : (4 / Real.pi) * mm z + (200 / (Work.Spaces.gam α - 1)) * IIz z
            ≤ (201 / (Work.Spaces.gam α - 1)) * (mm z + IIz z) := by
          have h6 : (200 : ℝ) / (Work.Spaces.gam α - 1) ≤ 201 / (Work.Spaces.gam α - 1) := by
            rw [div_le_div_iff_of_pos_right hγ1]; norm_num
          have h7 : (1 : ℝ) / (Work.Spaces.gam α - 1) ≤ 201 / (Work.Spaces.gam α - 1) := by
            rw [div_le_div_iff_of_pos_right hγ1]; norm_num
          nlinarith [h2, h6, h7, hmmnn, hIInn]
        calc Ag * Real.sqrt (IIz z)
            = Real.sqrt ((4 / Real.pi) * mm z + (200 / (Work.Spaces.gam α - 1)) * IIz z)
              * Real.sqrt (IIz z) := by rw [hAg]
          _ ≤ Real.sqrt ((201 / (Work.Spaces.gam α - 1)) * (mm z + IIz z))
              * Real.sqrt (IIz z) :=
              mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h5) (Real.sqrt_nonneg _)
          _ = Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (mm z + IIz z)
              * Real.sqrt (IIz z) := by
              rw [Real.sqrt_mul' _ (by positivity)]
          _ ≤ Real.sqrt (201 / (Work.Spaces.gam α - 1)) * (mm z + IIz z) := by
              rw [show Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (mm z + IIz z)
                    * Real.sqrt (IIz z)
                  = Real.sqrt (201 / (Work.Spaces.gam α - 1))
                    * (Real.sqrt (mm z + IIz z) * Real.sqrt (IIz z)) from by ring]
              refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
              have h9 : Real.sqrt (mm z + IIz z) * Real.sqrt (IIz z)
                  ≤ (Real.sqrt (mm z + IIz z)) ^ 2 / 2 + (Real.sqrt (IIz z)) ^ 2 / 2 := by
                nlinarith [sq_nonneg (Real.sqrt (mm z + IIz z) - Real.sqrt (IIz z))]
              rw [Real.sq_sqrt (add_nonneg hmmnn hIInn), Real.sq_sqrt hIInn] at h9
              linarith
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      calc (Work.Spaces.w z) ^ 2 * Ag * (Real.sqrt (Cmz * K4 ^ 2) * Real.sqrt (IIz z))
          = (Work.Spaces.w z) ^ 2 * Real.sqrt (Cmz * K4 ^ 2) * (Ag * Real.sqrt (IIz z)) := by
            ring
        _ ≤ (Work.Spaces.w z) ^ 2 * Real.sqrt (Cmz * K4 ^ 2)
              * (Real.sqrt (201 / (Work.Spaces.gam α - 1)) * (mm z + IIz z)) :=
            mul_le_mul_of_nonneg_left hkey (mul_nonneg hw2 hCnn)
        _ = Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
              * ((Work.Spaces.w z) ^ 2 * (mm z + IIz z)) := by ring
    calc (∫ θ in Work.Spaces.Iθ, |Work.FTS.TransportS.leafGam α z θ
          * Work.Spaces.mixed 0 1 A z θ * Work.Spaces.DzIter 5 f z θ
          * Work.Spaces.mixed 5 1 f z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * Ag
            * ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
              * (|Work.Spaces.pth A z θ|
                * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ|)) := hstep1
      _ = (Work.Spaces.w z) ^ 2 * Ag
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
                * (|Work.Spaces.pth A z θ|
                  * |Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ|)) := hstep2
      _ = (Work.Spaces.w z) ^ 2 * Ag
            * (∫ θ in Work.Spaces.Iθ, Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
                  * (Work.Spaces.pth A z θ) ^ 2)
                * Real.sqrt ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
                  * (Work.Spaces.pth (Work.Spaces.DzIter 5 f) z θ) ^ 2)) := by rw [hstep3]
      _ ≤ (Work.Spaces.w z) ^ 2 * Ag * (Real.sqrt (Cmz * K4 ^ 2) * Real.sqrt (IIz z)) :=
          mul_le_mul_of_nonneg_left hstep4 (by positivity)
      _ ≤ Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
            * ((Work.Spaces.w z) ^ 2 * (mm z + IIz z)) := hstep5

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowDzWlInfFlat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `rowDzWlInfFlat`

The flat per-slot bound for the `A · D_z f` row of the level-six pairing, with the coefficient
priced by `𝒲^{6,∞}` and the three flat bounds on `∂_θA`.  The proof is the Leibniz expansion
(`RowDzRem.rowDz_leib`), the per-term bound (`RowDzTerms.rowDz_term_bound`), the radial transport
term (`T6Gen.fluxSix_noDecay`) and the angular Hardy inequality (`T6Gen.qDzLe`).
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg)

theorem rowDzWlInfFlat : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K M Kf : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dz (Work.Spaces.pth A) z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dth (Work.Spaces.pth A) z θ| ≤ Kf) →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Work.Spaces.Dz f z θ) f|
        ≤ C * α ^ (-(4 : ℝ)) * (1 + K + Kf) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Ch, hChpos, hhardy⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
  obtain ⟨Cfl, hCflpos, hflux⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.fluxSix_noDecay
  obtain ⟨Cr, hCrpos, hrem⟩ := rowDz_rem_pt
  refine ⟨(1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12, by positivity, ?_⟩
  intro α hα A f K M Kf a b ρ hAsm hAwl hAK hdat hKf0 hKf1 hKf2 hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hfsm : Work.FTS.EllipticEst.SmoothOpen f := hdat.sm
  have hf6 : Work.Spaces.HkMem α 6 f := hdat.h6
  have hf7 : Work.Spaces.HkMem α 7 f := hdat.h7
  have hKnn : 0 ≤ K :=
    le_trans (Work.Spaces.WlInf_nonneg α 6 A hAwl) hAK
  have hKfnn : 0 ≤ Kf := le_trans (abs_nonneg _)
    (hKf0 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  obtain ⟨q, hρeq, hq0, hqγ, hqη0⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.leafW_canon_cases hα0 hleaf
  have hqcases : q = Work.Spaces.eta ∨ q = 0 ∨ q = Work.Spaces.gam α := by
    rcases hleaf with h | h | ⟨_, h⟩
    · refine Or.inl (rowDz_canonW_eq_of hρeq ?_)
      rw [h]
      exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.1
    · refine Or.inr (Or.inl (rowDz_canonW_eq_of hρeq ?_))
      rw [h]
      exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.1
    · refine Or.inr (Or.inr (rowDz_canonW_eq_of hρeq ?_))
      rw [h]
      exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.2 α
  rw [hρeq]
  -- ## the angular Hardy slot
  set pm : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hpm
  set HH : ℝ → ℝ → ℝ := fun z θ => ∑ k ∈ Finset.range 6,
      canonW (1 - α / 10) z θ * (Work.Spaces.DzIter k f z θ) ^ 2 with hHH
  have hHHnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ HH z θ := by
    intro z θ hz hθ hθ2
    rw [hHH]
    exact Finset.sum_nonneg fun k hk =>
      mul_nonneg (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩) (sq_nonneg _)
  have hHHdom : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ k : ℕ, k ≤ 5 →
      canonW (1 - α / 10) z θ * (Work.Spaces.DzIter k f z θ) ^ 2 ≤ HH z θ := by
    intro z θ hz hθ hθ2 k hk
    rw [hHH]
    refine Finset.single_le_sum (f := fun k => canonW (1 - α / 10) z θ
      * (Work.Spaces.DzIter k f z θ) ^ 2) (fun k hk' =>
      mul_nonneg (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩) (sq_nonneg _)) ?_
    exact Finset.mem_range.mpr (by omega)
  have hHHint : MeasureTheory.Integrable (fun p : ℝ × ℝ => HH p.1 p.2) pm := by
    rw [hHH]
    exact MeasureTheory.integrable_finsetSum (Finset.range 6)
      (f := fun k => fun p : ℝ × ℝ =>
        canonW (1 - α / 10) p.1 p.2 * (Work.Spaces.DzIter k f p.1 p.2) ^ 2)
      (fun k hk => (hhardy α hα f k hfsm hf6 (by have := Finset.mem_range.mp hk; omega)).1)
  have hHHval : (∫ p, HH p.1 p.2 ∂pm)
      ≤ 6 * (Ch * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f)) := by
    rw [hHH]
    rw [MeasureTheory.integral_finsetSum (Finset.range 6)
      (f := fun k => fun p : ℝ × ℝ =>
        canonW (1 - α / 10) p.1 p.2 * (Work.Spaces.DzIter k f p.1 p.2) ^ 2)
      (fun k hk => (hhardy α hα f k hfsm hf6 (by have := Finset.mem_range.mp hk; omega)).1)]
    refine le_trans (Finset.sum_le_sum fun k hk =>
      (hhardy α hα f k hfsm hf6 (by have := Finset.mem_range.mp hk; omega)).2) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact le_of_eq (by ring)
  have hIH0 : 0 ≤ ∫ p, HH p.1 p.2 ∂pm := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
    exact hHHnn p.1 p.2 hp.1 hp.2.1 hp.2.2
  -- ## the pieces of the pairing
  set Z : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f with hZ
  set Uf : ℝ → ℝ → ℝ :=
    fun z θ => Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ with hUf
  set F : ℝ × ℝ → ℝ := fun p => canonW q p.1 p.2 * Uf p.1 p.2 * Z p.1 p.2 with hF
  set F0 : ℝ × ℝ → ℝ := fun p =>
    canonW q p.1 p.2 * A p.1 p.2 * Work.Spaces.Dz Z p.1 p.2 * Z p.1 p.2 with hF0
  set Fr : ℝ × ℝ → ℝ := fun p =>
    canonW q p.1 p.2 * (Uf p.1 p.2 - A p.1 p.2 * Work.Spaces.Dz Z p.1 p.2) * Z p.1 p.2 with hFr
  have hDZpt : ∀ z θ : ℝ, Work.Spaces.Dz Z z θ = Work.Spaces.mixed (b + 1) a f z θ := by
    intro z θ; rw [hZ]; rfl
  have hHki : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 f p.1 p.2) pm :=
    (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hfsm hf6).1
  have hHki7 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 7 f p.1 p.2) pm :=
    (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hfsm hf7).1
  -- ## integrability of the remainder
  have hZaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Z p.1 p.2) pm := by
    rw [hZ]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hfsm b a)
  have hDZaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Dz Z p.1 p.2) pm := by
    simp only [hDZpt]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hfsm (b + 1) a)
  have hAaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1 p.2) pm :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hAsm.continuousOn
  have hcanonAesm : AEStronglyMeasurable (fun p : ℝ × ℝ => canonW q p.1 p.2) pm :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.TransportS.SlotT2.continuousOn_canonW q)
  have hUfaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Uf p.1 p.2) pm :=
    rowDz_Uf_aesm hAsm hfsm a b
  have hmaj_int : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Cr * (1 + K + Kf) * (HH p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2)) pm :=
    ((hHHint.add hHki).const_mul (Cr * (1 + K + Kf)))
  have hFr_int : MeasureTheory.Integrable Fr pm := by
    refine MeasureTheory.Integrable.mono' hmaj_int ?_ ?_
    · exact (hcanonAesm.mul (hUfaesm.sub (hAaesm.mul hDZaesm))).mul hZaesm
    · filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
      rw [Real.norm_eq_abs, hFr]
      have h := hrem α hα A f K Kf a b q HH hAsm hAwl hAK hKfnn hKf0 hKf1 hKf2 hfsm hab hq0
        hqγ hqη0 hqcases hHHdom hHHnn p.1 p.2 hp.1 hp.2.1 hp.2.2
      simp only [hUf, hZ]
      exact h
  -- ## integrability of the transport piece
  have hF0_pt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F0 (z, θ)| ≤ K * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
    intro z θ hz hθ hθ2
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
    have hσ : 0 ≤ Real.sin (2 * θ) := le_of_lt (rowDz_sin2_pos hθI)
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩
    have hAg : canonW q z θ * |A z θ| ≤ K * canonW q z θ := by
      calc canonW q z θ * |A z θ| ≤ canonW q z θ * K :=
            mul_le_mul_of_nonneg_left (rowDz_A_le hAwl hAK z θ hz hθ hθ2) hcw
        _ = K * canonW q z θ := by ring
    have h2 : canonW q z θ * |A z θ| * |Work.Spaces.Dz Z z θ| * |Z z θ|
        ≤ K * (canonW q z θ * (Work.Spaces.Dz Z z θ) ^ 2 + canonW q z θ * (Z z θ) ^ 2) := by
      have h1 : canonW q z θ * |A z θ| * |Work.Spaces.Dz Z z θ|
          ≤ K * (canonW q z θ * |Work.Spaces.Dz Z z θ|) := by
        calc canonW q z θ * |A z θ| * |Work.Spaces.Dz Z z θ|
            ≤ (K * canonW q z θ) * |Work.Spaces.Dz Z z θ| :=
              mul_le_mul_of_nonneg_right hAg (abs_nonneg _)
          _ = K * (canonW q z θ * |Work.Spaces.Dz Z z θ|) := by ring
      calc canonW q z θ * |A z θ| * |Work.Spaces.Dz Z z θ| * |Z z θ|
          ≤ (K * (canonW q z θ * |Work.Spaces.Dz Z z θ|)) * |Z z θ| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = K * (canonW q z θ * |Work.Spaces.Dz Z z θ| * |Z z θ|) := by ring
        _ ≤ K * (canonW q z θ * (Work.Spaces.Dz Z z θ) ^ 2 + canonW q z θ * (Z z θ) ^ 2) :=
            mul_le_mul_of_nonneg_left (rowDz_canonW_abs_mul_le hσ _ _) hKnn
    rw [hF0, abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]
    refine le_trans h2 ?_
    have h3 : canonW q z θ * (Work.Spaces.Dz Z z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
      simp only [hDZpt]
      exact rowDz_DZ_maj hqγ hqη0 hab z θ hz hθ hθ2
    have h4 : canonW q z θ * (Z z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      rw [hZ]
      exact rowDz_Z_maj hqγ hqη0 hab z θ hz hθ hθ2
    exact mul_le_mul_of_nonneg_left (add_le_add h3 h4) hKnn
  have hF0_int : MeasureTheory.Integrable F0 pm := by
    have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        K * (Work.Spaces.HkIntegrand α 7 f p.1 p.2
          + Work.Spaces.HkIntegrand α 6 f p.1 p.2)) pm :=
      ((hHki7.add hHki).const_mul K)
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · refine AEStronglyMeasurable.congr
        (((hcanonAesm.mul hAaesm).mul hDZaesm).mul hZaesm) ?_
      filter_upwards with p
      simp only [Pi.mul_apply]
      ring
    · filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
      rw [Real.norm_eq_abs]
      exact hF0_pt p.1 p.2 hp.1 hp.2.1 hp.2.2
  have hF_int : MeasureTheory.Integrable F pm := by
    have hsplit : F =ᵐ[pm] fun p => F0 p + Fr p := by
      filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
      show F p = F0 p + Fr p
      rw [hF, hF0, hFr]
      ring
    exact (hF0_int.add hFr_int).congr hsplit.symm
  -- ## Fubini
  have hFub : Work.FTS.TransportS.slotPairing (canonW q) a b
        (fun z θ => A z θ * Work.Spaces.Dz f z θ) f = ∫ p, F p ∂pm := by
    rw [Work.FTS.TransportS.slotPairing]
    exact MeasureTheory.integral_integral hF_int
  -- ## the two integral bounds
  have hflux0 : |∫ p, F0 p ∂pm| ≤ Cfl * K * Work.Spaces.HkSq α 6 f := by
    have hfab : (∫ p, F0 p ∂pm)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F0 (z, θ) := by
      have h := MeasureTheory.integral_integral
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun z θ => F0 (z, θ)) hF0_int
      rw [hpm]
      exact h.symm
    have hfab2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F0 (z, θ))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            canonW q z θ * A z θ * Work.Spaces.Dz (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [hF0, hZ]
    rw [hfab, hfab2]
    exact hflux α A f a b q K hα0 hα1 hq0 hqγ hqη0 hab hAsm hfsm hf6 hf7
      (fun z θ hz hθ hθ2 => rowDz_A_le hAwl hAK z θ hz hθ hθ2)
      (fun z θ hz hθ hθ2 => rowDz_DzA_le hAwl hAK z θ hz hθ hθ2)
  have hFr_bd : |∫ p, Fr p ∂pm| ≤ Cr * (1 + K + Kf)
      * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm)) := by
    refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
    have hmono : (∫ p, ‖Fr p‖ ∂pm)
        ≤ ∫ p, Cr * (1 + K + Kf)
            * (HH p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2) ∂pm := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun p => norm_nonneg _) hmaj_int ?_
      filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
      rw [Real.norm_eq_abs, hFr]
      have h := hrem α hα A f K Kf a b q HH hAsm hAwl hAK hKfnn hKf0 hKf1 hKf2 hfsm hab hq0
        hqγ hqη0 hqcases hHHdom hHHnn p.1 p.2 hp.1 hp.2.1 hp.2.2
      simp only [hUf, hZ]
      exact h
    refine le_trans hmono ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hHHint hHki,
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hfsm hf6).2]
    ring_nf
    exact le_refl _
  -- ## the final estimate
  have hfinal : Cfl * K * Work.Spaces.HkSq α 6 f
      + Cr * (1 + K + Kf) * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm))
      ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ))
        * (1 + K + Kf) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
    have hα4 : (1 : ℝ) ≤ α ^ (-(4 : ℝ)) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(4 : ℝ) ≤ 0 by norm_num)
    have hα24 : α ^ (-(2 : ℝ)) ≤ α ^ (-(4 : ℝ)) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(4 : ℝ) ≤ -(2 : ℝ) by norm_num)
    have hS : 0 ≤ Work.Spaces.HkSq α 6 f := hSq0
    have hA4 : 0 ≤ α ^ (-(4 : ℝ)) := Real.rpow_nonneg hα0.le _
    -- ### the Hardy slot: `S + ∫HH ≤ (1+6Ch) α^{-4} (1+S)`
    have h2 : Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm)
        ≤ (1 + 6 * Ch) * α ^ (-(4 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f) := by
      have h := hHHval
      have h6 : 6 * (Ch * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f))
          ≤ 6 * (Ch * α ^ (-(4 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hα24 hChpos.le) (by linarith)
      nlinarith [h, h6, hS, hIH0, hChpos.le, hα4]
    -- ### the coefficient comparison
    have hc : Cfl + Cr * (1 + 6 * Ch) ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 := by
      have h1 : Cr * (1 + 6 * Ch) ≤ 7 * (1 + Cr) * (1 + Ch) := by nlinarith
      have h2 : Cfl + 7 * (1 + Cr) * (1 + Ch) ≤ 8 * (1 + Cfl) * (1 + Ch) * (1 + Cr) := by
        have hCh0 : 0 ≤ Ch := hChpos.le
        have hCr0 : 0 ≤ Cr := hCrpos.le
        have hCC : 0 ≤ Ch * Cr := mul_nonneg hCh0 hCr0
        have h6 : 1 ≤ (1 + Ch) * (1 + Cr) := by nlinarith [hCh0, hCr0, hCC]
        have h60 : 0 ≤ (1 + Ch) * (1 + Cr) := mul_nonneg (by linarith) (by linarith)
        have hA : Cfl * 1 ≤ Cfl * ((1 + Ch) * (1 + Cr)) :=
          mul_le_mul_of_nonneg_left h6 hCflpos.le
        have hA' : Cfl ≤ Cfl * ((1 + Ch) * (1 + Cr)) := by simpa using hA
        have hB : Cfl + 7 ≤ 8 * (1 + Cfl) := by linarith [hCflpos.le]
        calc Cfl + 7 * (1 + Cr) * (1 + Ch)
            = Cfl + 7 * ((1 + Ch) * (1 + Cr)) := by ring
          _ ≤ Cfl * ((1 + Ch) * (1 + Cr)) + 7 * ((1 + Ch) * (1 + Cr)) := by linarith [hA']
          _ = (Cfl + 7) * ((1 + Ch) * (1 + Cr)) := by ring
          _ ≤ (8 * (1 + Cfl)) * ((1 + Ch) * (1 + Cr)) :=
              mul_le_mul_of_nonneg_right hB h60
          _ = 8 * (1 + Cfl) * (1 + Ch) * (1 + Cr) := by ring
      have h3 : (8 : ℝ) * (1 + Cfl) * (1 + Ch) * (1 + Cr)
          ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 := by
        have h4 : 0 ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) := by positivity
        nlinarith
      linarith [h1, h2, h3]
    have hcc : Cr * (1 + 6 * Ch) ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 :=
      le_trans (by nlinarith [hCflpos.le]) hc
    have hc0 : 0 ≤ Cfl + Cr * (1 + 6 * Ch) := by nlinarith [hCflpos.le, hCrpos.le, hChpos.le]
    have hk : K ≤ α ^ (-(4 : ℝ)) * (1 + K + Kf) := by nlinarith [hKnn, hKfnn, hα4]
    have hA : Cfl * K + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ)))
        ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ)) * (1 + K + Kf) := by
      have ha : Cfl * K ≤ Cfl * (α ^ (-(4 : ℝ)) * (1 + K + Kf)) :=
        mul_le_mul_of_nonneg_left hk hCflpos.le
      have hb : Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ)))
          = Cr * (1 + 6 * Ch) * α ^ (-(4 : ℝ)) * (1 + K + Kf) := by ring
      calc Cfl * K + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ)))
          ≤ Cfl * (α ^ (-(4 : ℝ)) * (1 + K + Kf))
              + Cr * (1 + 6 * Ch) * α ^ (-(4 : ℝ)) * (1 + K + Kf) := by
            rw [hb]; exact add_le_add ha le_rfl
        _ = (Cfl + Cr * (1 + 6 * Ch)) * (α ^ (-(4 : ℝ)) * (1 + K + Kf)) := by ring
        _ ≤ ((1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12) * (α ^ (-(4 : ℝ)) * (1 + K + Kf)) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ)) * (1 + K + Kf) := by ring
    have hB : (1 + Work.Spaces.HkSq α 6 f)
        ≤ (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by nlinarith [hM0, hS]
    have hpart1 : Cfl * K * Work.Spaces.HkSq α 6 f
        ≤ Cfl * K * (1 + Work.Spaces.HkSq α 6 f) := by
      nlinarith [hS, mul_nonneg hCflpos.le hKnn]
    have hpart2 : Cr * (1 + K + Kf) * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm))
        ≤ Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ)))
            * (1 + Work.Spaces.HkSq α 6 f) := by
      have hc' : 0 ≤ Cr * (1 + K + Kf) := by nlinarith [hCrpos.le, hKnn, hKfnn]
      have h := mul_le_mul_of_nonneg_left h2 hc'
      simpa only [mul_assoc] using h
    have hS1 : 0 ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
    have hK1 : 0 ≤ 1 + K + Kf := by linarith
    have hmid : Cfl * K * Work.Spaces.HkSq α 6 f
          + Cr * (1 + K + Kf) * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm))
        ≤ (Cfl * K + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ))))
            * (1 + Work.Spaces.HkSq α 6 f) := by
      have hrn : (Cfl * K + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ))))
            * (1 + Work.Spaces.HkSq α 6 f)
          = Cfl * K * (1 + Work.Spaces.HkSq α 6 f)
            + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ)))
              * (1 + Work.Spaces.HkSq α 6 f) := by ring
      rw [hrn]
      exact add_le_add hpart1 hpart2
    calc Cfl * K * Work.Spaces.HkSq α 6 f
          + Cr * (1 + K + Kf) * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm))
        ≤ (Cfl * K + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ))))
            * (1 + Work.Spaces.HkSq α 6 f) := hmid
      _ ≤ ((1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ)) * (1 + K + Kf))
            * ((1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul hA hB hS1 (by positivity)
      _ = (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ))
            * (1 + K + Kf) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by ring

  calc |Work.FTS.TransportS.slotPairing (canonW q) a b
        (fun z θ => A z θ * Work.Spaces.Dz f z θ) f|
      = |∫ p, F p ∂pm| := by rw [hFub]
    _ = |∫ p, (F0 p + Fr p) ∂pm| := by
        rw [MeasureTheory.integral_congr_ae (by
          filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
          show F p = F0 p + Fr p
          rw [hF, hF0, hFr]; ring)]
    _ = |∫ p, F0 p ∂pm + ∫ p, Fr p ∂pm| := by
        rw [MeasureTheory.integral_add hF0_int hFr_int]
    _ ≤ |∫ p, F0 p ∂pm| + |∫ p, Fr p ∂pm| := abs_add_le _ _
    _ ≤ Cfl * K * Work.Spaces.HkSq α 6 f
        + Cr * (1 + K + Kf) * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm)) :=
        add_le_add hflux0 hFr_bd
    _ ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ))
        * (1 + K + Kf) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := hfinal

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.EV6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false

/-!
# `FTS/StrongPersist/SP6/EV6.lean` — the order-six flat bound of the `EV`-field

`EV Y = (z/(z+1))·EVz Y = (z/(z+1))·(2(cos²θ − 2 sin²θ)·Y + sin(2θ)·∂_θY)` is the fourth of the
five fields of the `SP6` flat package.  This file proves

`FlatW 6 (EV Y) (C·(α+1)·(K + KY + KD))`

from `SmoothOpen Y`, `FlatW 7 Y K`, `Fb 6 KY Y`, `F0 6 KD (Yblk Y)`.

## The route

`FlatW 6 f M` is the pair `F0 6 M f`, `F0 5 M (∂_θf)` (`flatW6_of_F0`), so it suffices to bound
the two blocks

* `F0 6 (64·A·B₁) (EV Y)`   (`B₁` the constant of the `EVz`-block `EVzR Y`),
* `F0 5 (32·A·B₂) (∂_θ(EV Y))` (`B₂` the constant of `EVzD Y`, the candidate `∂_θ`-derivative of
  `EVzR Y`),

where `A` is the constant of `CoefBundle6s` (the radial coefficient `z/(1+z)` is `F0 6 A` and
smooth).  Both are one application of the Leibniz estimate `F0_mul` with the *radial factor*
`r = z/(1+z)`, which is `θ`-free — this is also why `∂_θ(EV Y) = r·∂_θ(EVz Y)`, the identity
`pth (EVR Y) = fun z θ => r·EVzD Y` proved below (`ev_six_pth_EVR`).

The two `EVz`-blocks are exactly the estimates of the sibling tasks, already in the workspace:
`F0SixEVzR` (`F0 6 (C₁·(K+KY)) (EVzR Y)`) and `F0FiveEVzD` (`F0 5 (C₂·(K+KY)) (EVzD Y)`), and
the product-rule identity `PthEVzR` (`∂_θ(EVzR Y) = EVzD Y`) — the `EVz`-fields are *linear* in
the two blocks `Y`, `∂_θY`, so those constants are linear in `K + KY`.

The constant bookkeeping is the elementary Lemma `ev_six_const_bound`: the `EVz`-slot constants
are evaluated at `(K, KY) ↦ (KY, K+KY)` (so that `K + KY ↦ K + 2KY ≤ 2(K+KY+KD)`), giving the
final linear constant.  Since `∃ C` is quantified before the data, `C` absorbs both `A` and the
two numerical constants `C₁`, `C₂` (through their absolute values).
-/

/-- **The constant comparison.**  If `c ≤ 128` and `256·A·(|C|+1) ≤ Cs` (with `A ≥ 0` and the
three block bounds nonnegative), then the `EVz`-slot constant `c·A·(C·(KY + (K+KY)))` is
dominated by the target constant `Cs·(α+1)·(K+KY+KD)`.  Here `KY + (K+KY) = K + 2KY ≤ 2(K+KY+KD)`
is the point where the third block `KD` enters. -/
private theorem ev_six_const_bound {A c C α K KY KD Cs : ℝ} (hA0 : 0 ≤ A) (hα : 0 ≤ α)
    (hK : 0 ≤ K) (hKY : 0 ≤ KY) (hKD : 0 ≤ KD) (hc0 : 0 ≤ c) (hc : c ≤ 128)
    (hCs : 256 * A * (|C| + 1) ≤ Cs) :
    c * A * (C * (KY + (K + KY))) ≤ Cs * (α + 1) * (K + KY + KD) := by
  have hS0 : (0 : ℝ) ≤ K + KY + KD := by linarith
  have hCabs0 : (0 : ℝ) ≤ |C| := abs_nonneg C
  have hCs0 : (0 : ℝ) ≤ Cs :=
    le_trans (mul_nonneg (mul_nonneg (by norm_num) hA0) (by linarith)) hCs
  have hX : C * (KY + (K + KY)) ≤ |C| * (2 * (K + KY + KD)) := by
    have hX1 : C * (KY + (K + KY)) ≤ |C| * (KY + (K + KY)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    have hX2 : KY + (K + KY) ≤ 2 * (K + KY + KD) := by linarith
    exact le_trans hX1 (mul_le_mul_of_nonneg_left hX2 hCabs0)
  have h2S0 : (0 : ℝ) ≤ |C| * (2 * (K + KY + KD)) := mul_nonneg hCabs0 (by linarith)
  have hA0' : (0 : ℝ) ≤ 256 * A := mul_nonneg (by norm_num) hA0
  calc c * A * (C * (KY + (K + KY)))
      ≤ c * A * (|C| * (2 * (K + KY + KD))) := mul_le_mul_of_nonneg_left hX (mul_nonneg hc0 hA0)
    _ ≤ 128 * A * (|C| * (2 * (K + KY + KD))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hA0) h2S0
    _ = 256 * A * |C| * (K + KY + KD) := by ring
    _ ≤ 256 * A * (|C| + 1) * (K + KY + KD) := by
        have hle2 : |C| * (K + KY + KD) ≤ (|C| + 1) * (K + KY + KD) :=
          mul_le_mul_of_nonneg_right (by linarith) hS0
        calc 256 * A * |C| * (K + KY + KD) = (256 * A) * (|C| * (K + KY + KD)) := by ring
          _ ≤ (256 * A) * ((|C| + 1) * (K + KY + KD)) :=
              mul_le_mul_of_nonneg_left hle2 hA0'
          _ = 256 * A * (|C| + 1) * (K + KY + KD) := by ring
    _ ≤ Cs * (K + KY + KD) := mul_le_mul_of_nonneg_right hCs hS0
    _ ≤ Cs * (α + 1) * (K + KY + KD) := by
        have h1α : (1 : ℝ) ≤ α + 1 := by linarith
        calc Cs * (K + KY + KD) ≤ (Cs * (α + 1)) * (K + KY + KD) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCs0 h1α) hS0
          _ = Cs * (α + 1) * (K + KY + KD) := by ring

/-- **`∂_θ(EVR Y) = (z/(1+z))·EVzD Y` on the open quadrant.**  The radial factor `z/(1+z)` is
`θ`-free, so the product rule degenerates to `∂_θ(r·EVzR Y) = r·∂_θ(EVzR Y)`, and the second
factor is `EVzD Y` by `PthEVzR`. -/
private theorem ev_six_pth_EVR {Y : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hSmoothZ : Work.FTS.EllipticEst.SmoothOpen (EVzR Y))
    (hrhos : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z))) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EVR Y) z θ = (z / (1 + z)) * EVzD Y z θ := by
  intro z θ hz hθ hθ'
  show Work.Spaces.pth (fun z θ : ℝ => z / (1 + z) * EVzR Y z θ) z θ
    = z / (1 + z) * EVzD Y z θ
  rw [Work.FTS.PhiStar.CoreAux.Fbq_pth_mul
    (f := fun z _ : ℝ => z / (1 + z)) (g := EVzR Y) hrhos hSmoothZ z θ hz hθ hθ']
  have hr : Work.Spaces.pth (fun z _ : ℝ => z / (1 + z)) z θ = 0 := by
    show deriv (fun _ : ℝ => z / (1 + z)) θ = 0
    rw [deriv_const]
  rw [hr, zero_mul, zero_add, PthEVzR Y hsm z θ hz hθ hθ']

/-- **The order-six flat bound of the `EV`-star-field**, `EV Y = (z/(z+1))·EVz Y`.

Prove `FlatW 6 (EV Y) M` with `M := C·(α+1)·(K+KY+KD)` from `SmoothOpen Y`, `FlatW 7 Y K`,
`Fb 6 KY Y`, `F0 6 KD (Yblk Y)`; the constant must stay **linear** in `K + KY + KD`.

Import `Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`: `CoefBundle6s`, `atomData`,
`EVzR`/`EVzD`, `EVR`/`EVD` and `evEVR_eq`, `flatW6_of_F0`, `FlatW_mono6`, `mono_const`,
`pth_thetaOnly`. Recommended route: prove the strong pair `F0 6 (EVR Y)` and
`F0 5 (pth (EVR Y))` (the second is `F0 5 (EVD Y)` since `z/(z+1)` is `θ`-free), where the
`EVz R`-parts are the same estimates as in the `EVz`-task (you may redo them here, or reduce to
a generic radial-factor lemma: if `F0 6 r A`, `F0 5 r A` for `r = fun z θ => z/(1+z)` and
`F0 6 (EVzR Y) B`, `F0 5 (EVzD Y) B`, then `F0_mul` gives `F0 6 (EVR Y) (32·A·B)` and
`F0 5 (EVD Y) (32·A·B)`). Then `F0_congr` + `flatW6_of_F0`. The sibling
`Submission/Work/FTS/PhiStar/CoreAux/Fb_EV_bound.lean` proves the order-**four** version of the
joint statement for `EVz` and `EV`. -/
theorem EV6 : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y →
    Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EV Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA1
  obtain ⟨C₁, _hC₁pos, hC₁⟩ := F0SixEVzR
  obtain ⟨C₂, _hC₂pos, hC₂⟩ := F0FiveEVzD
  refine ⟨max 1 (256 * A * (|C₁| + |C₂| + 1)), lt_max_of_lt_left (by norm_num), ?_⟩
  intro α K KY KD Y hα hK hKY hKD hsm hW hFb _hD
  -- the two block bounds
  have hY : Work.FTS.PhiStar.F0 6 KY Y := hFb.f0
  have hPY : Work.FTS.PhiStar.F0 6 (K + KY) (Work.Spaces.pth Y) :=
    (Work.FTS.PhiStar.CoreAux.F0_six_pth_of_FlatW hW).mono le_rfl (by linarith)
  have hK0 : (0 : ℝ) ≤ K + KY := by linarith
  -- the two `EVz`-bounds (the estimates of the sibling `EVz`-tasks)
  have hZ : Work.FTS.PhiStar.F0 6 (C₁ * (KY + (K + KY))) (EVzR Y) :=
    hC₁ KY (K + KY) Y hKY hK0 hsm hY hPY
  have hZd : Work.FTS.PhiStar.F0 5 (C₂ * (KY + (K + KY))) (EVzD Y) :=
    hC₂ KY (K + KY) Y hKY hK0 hsm hY hPY
  have hZ0 : (0 : ℝ) ≤ C₁ * (KY + (K + KY)) := Work.FTS.PhiStar.CoreAux.Fbq_nonneg_of_F0 hZ
  have hZd0 : (0 : ℝ) ≤ C₂ * (KY + (K + KY)) := Work.FTS.PhiStar.CoreAux.Fbq_nonneg_of_F0 hZd
  -- the radial coefficient `z/(1+z)`
  have hrho := hcoef (fun z _ : ℝ => z / (1 + z)) (by simp [coefFun])
  have hrhos : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := hrho.2
  have hrho5 : Work.FTS.PhiStar.F0 5 A (fun z _ : ℝ => z / (1 + z)) :=
    hrho.1.mono (by norm_num) le_rfl
  -- smoothness of the two `EVz`-blocks
  have hφs : Work.FTS.EllipticEst.SmoothOpen
      (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) :=
    (hcoef (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by simp [coefFun])).2
  have hσs : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) :=
    (hcoef (fun _ θ : ℝ => Real.sin (2 * θ)) (by simp [coefFun])).2
  have hSmoothZ : Work.FTS.EllipticEst.SmoothOpen (EVzR Y) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add
      (Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul
        (Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hφs 2) hsm)
      (Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul hσs hsm.pth)
  have hSmoothD : Work.FTS.EllipticEst.SmoothOpen (EVzD Y) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.congr hSmoothZ.pth (PthEVzR Y hsm)
  -- `F0 6` of `EV Y`: multiply the `EVzR`-block by the radial factor
  have h1 : Work.FTS.PhiStar.F0 6 ((2 : ℝ) ^ 6 * A * (C₁ * (KY + (K + KY))))
      (fun z θ : ℝ => (z / (1 + z)) * EVzR Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA0 hZ0 hrhos hSmoothZ hrho.1 hZ
  have h1a : Work.FTS.PhiStar.F0 6 (64 * A * (C₁ * (KY + (K + KY))))
      (fun z θ : ℝ => (z / (1 + z)) * EVzR Y z θ) := h1.mono le_rfl (by norm_num)
  have h1b : Work.FTS.PhiStar.F0 6 (64 * A * (C₁ * (KY + (K + KY))))
      (Work.FTS.PhiStar.EV Y) :=
    Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => evEVR_eq Y z θ) h1a
  -- `F0 5` of `∂_θ(EV Y)`: multiply the `EVzD`-block by the radial factor
  have h2 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * A * (C₂ * (KY + (K + KY))))
      (fun z θ : ℝ => (z / (1 + z)) * EVzD Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA0 hZd0 hrhos hSmoothD hrho5 hZd
  have h2a : Work.FTS.PhiStar.F0 5 (32 * A * (C₂ * (KY + (K + KY))))
      (fun z θ : ℝ => (z / (1 + z)) * EVzD Y z θ) := h2.mono le_rfl (by norm_num)
  have h2b : Work.FTS.PhiStar.F0 5 (32 * A * (C₂ * (KY + (K + KY))))
      (Work.Spaces.pth (EVR Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (fun z θ => ev_six_pth_EVR hsm hSmoothZ hrhos z θ) h2a
  have h2c : Work.FTS.PhiStar.F0 5 (32 * A * (C₂ * (KY + (K + KY))))
      (Work.Spaces.pth (Work.FTS.PhiStar.EV Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (pth_congr6 (fun z θ _ _ _ => evEVR_eq Y z θ)) h2b
  -- the two constant comparisons
  have hCs1 : 256 * A * (|C₁| + 1) ≤ max 1 (256 * A * (|C₁| + |C₂| + 1)) := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hA0))
      (le_max_right _ _)
    have h2' := abs_nonneg C₂
    linarith
  have hCs2 : 256 * A * (|C₂| + 1) ≤ max 1 (256 * A * (|C₁| + |C₂| + 1)) := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hA0))
      (le_max_right _ _)
    have h1' := abs_nonneg C₁
    linarith
  have hb1 := ev_six_const_bound (c := 64) (C := C₁) hA0 hα hK hKY hKD (by norm_num)
    (by norm_num) hCs1
  have hb2 := ev_six_const_bound (c := 32) (C := C₂) hA0 hα hK hKY hKD (by norm_num)
    (by norm_num) hCs2
  refine flatW6_of_F0 ?_ ?_
  · exact h1b.mono le_rfl hb1
  · exact h2c.mono le_rfl hb2

end Work.FTS.StrongPersist.SP6
end
