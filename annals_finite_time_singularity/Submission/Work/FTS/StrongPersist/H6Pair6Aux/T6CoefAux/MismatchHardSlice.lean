import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.slotAmgm
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.slotArith
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.cs_sqrt_int
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.MismatchHardAux

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
