import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.MismatchHardSlice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `b = 5` crux of the mismatch coefficient estimate

See the module docstring of the assigned file `mismatchCaseHard`.
-/
namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

theorem mh_hard_b5 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      Work.Spaces.HkMem α 6 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed 0 1 A p.1 p.2 * Work.Spaces.mixed 5 0 f p.1 p.2
          * Work.Spaces.mixed 5 1 f p.1 p.2) pm ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed 0 1 A p.1 p.2 * Work.Spaces.mixed 5 0 f p.1 p.2
            * Work.Spaces.mixed 5 1 f p.1 p.2 ∂pm|
        ≤ C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨Cmz, hCmz0, hmz⟩ := Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform
  have hCmznn : 0 ≤ Cmz := hCmz0.le
  refine ⟨300 * (Real.sqrt Cmz + 1), by positivity, ?_⟩
  intro α hα A f K0 K4 hAsm hA4 hA6 hAbdd hXn hfsm hf6
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγeq : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have hgam : 1 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hXn
  have hK0 : 0 ≤ K0 := by
    have h := hAbdd 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    linarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hH : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- ## the two `z`-marginals of the `f`-side
  set mm : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ) ^ 2 with hmm
  set IIz : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (deriv (fun θ' : ℝ => Work.Spaces.DzIter 5 f z θ')) θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hII
  have hm_int : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * mm z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [hmm] using (mh_pureZ_eta_slot_l2 α hα f hfsm hf6).1
  have hm_val : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * mm z)
      ≤ Work.Spaces.HkSq α 6 f := by
    simpa only [hmm] using (mh_pureZ_eta_slot_l2 α hα f hfsm hf6).2
  have hII_eq : IIz =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 5 1 f z θ) ^ 2) := by
    rw [show MeasureTheory.volume.restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [hII]
    refine MeasureTheory.integral_congr_ae ?_
    refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
    show (deriv (fun θ' : ℝ => Work.Spaces.DzIter 5 f z θ')) θ ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 5 1 f z θ) ^ 2
    have hdw : (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'')) θ ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        = (Work.Spaces.mixed 5 1 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Work.FTS.OpenPkg.ProdOpen.deriv_mixed_weight α hfsm 5 0 hz ⟨hθ0, hθ1⟩
    calc (deriv (fun θ' : ℝ => Work.Spaces.DzIter 5 f z θ')) θ ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        = (Work.Spaces.mixed 5 1 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hdw
      _ = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 5 1 f z θ) ^ 2 := by ring
  have hIzs := Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe α f hα0 hα1 hfsm hf6
  have hIIprod : (fun z : ℝ => (Work.Spaces.w z) ^ 2 * IIz z)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 5 1 f z θ) ^ 2) :=
    hII_eq.mono (fun z hz => by simp only [hz])
  have hI_int : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * IIz z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hIzs.1.congr hIIprod.symm
  have hI_val : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * IIz z)
      ≤ Work.Spaces.HkSq α 6 f := by
    rw [MeasureTheory.integral_congr_ae hIIprod]
    exact hIzs.2
  -- ## the `A`-side slice bound, uniform in `z`
  have hAsl : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth A z θ) ^ 2) ≤ Cmz * K4 ^ 2 := by
    intro z hz
    have h := hmz α A hα0 hα1 hAsm hA4 0 1 (by norm_num) (by norm_num) z hz
    have hpt2 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth A z θ) ^ 2
          = (Work.Spaces.mixed 0 1 A z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
      show (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth A z θ) ^ 2
        = (Work.Spaces.mixed 0 1 A z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      have hσ : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hm := Work.FTS.TransportS.SlotT2.supOpen_mixed_eq_sin_pth hAsm 0 hz ⟨hθ0, hθ1⟩
      rw [hm, mul_pow,
        show (Real.sin (2 * θ)) ^ (2 : ℕ)
              * (Work.Spaces.pth (Work.Spaces.DzIter 0 A) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            = ((Real.sin (2 * θ)) ^ (2 : ℕ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
              * (Work.Spaces.pth (Work.Spaces.DzIter 0 A) z θ) ^ 2 from by ring,
        mh_sq_mul_neg_gam (γ := Work.Spaces.gam α) hσ,
        Work.Spaces.DzIter_zero]
    have hA4 : Work.Spaces.HkSq α 4 A = (Work.FTS.Nonlin.Xn α A) ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 A)]
    have h2 : (Work.FTS.Nonlin.Xn α A) ^ 2 ≤ K4 ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 A) hXn 2
    have heq := MeasureTheory.integral_congr_ae hpt2
    calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth A z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1 A z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := heq
      _ ≤ Cmz * Work.Spaces.HkSq α 4 A := h
      _ = Cmz * (Work.FTS.Nonlin.Xn α A) ^ 2 := by rw [hA4]
      _ ≤ Cmz * K4 ^ 2 := mul_le_mul_of_nonneg_left h2 hCmznn

  have hAgmon : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter 5 f z θ) ^ 2
        ≤ (4 / Real.pi) * mm z + (200 / (Work.Spaces.gam α - 1)) * IIz z :=
    mh_agmon hα0 hα1 hfsm hf6

  -- ## continuity of the integrand on the open quadrant
  have hcontG : ContinuousOn (fun p : ℝ × ℝ => |Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 0 1 A p.1 p.2 * Work.Spaces.DzIter 5 f p.1 p.2
      * Work.Spaces.mixed 5 1 f p.1 p.2|) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.contOn_leafGam α).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hAsm.mixed 0 1))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hfsm.DzIter 5))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hfsm.mixed 5 1))).abs
  have hcontGQ : ContinuousOn (fun p : ℝ × ℝ => |Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 0 1 A p.1 p.2 * Work.Spaces.DzIter 5 f p.1 p.2
      * Work.Spaces.mixed 5 1 f p.1 p.2|) Work.FTS.EllipticEst.Q0 := hcontG
  -- ## the slice bound
  have hslice := mh_slice_bound (α := α) (A := A) (f := f) (K4 := K4) (Cmz := Cmz)
    hα0 hα1 hAsm hfsm hA6 hf6 hAsl hAgmon

  -- ## the radial majorant and the outer integrability
  have hFaesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, |Work.FTS.TransportS.leafGam α z θ
        * Work.Spaces.mixed 0 1 A z θ * Work.Spaces.DzIter 5 f z θ
        * Work.Spaces.mixed 5 1 f z θ|) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.aesm_sliceIntegral
      (G := fun z θ => |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 0 1 A z θ
        * Work.Spaces.DzIter 5 f z θ * Work.Spaces.mixed 5 1 f z θ|)
      hcontGQ
  have hmaj_int : MeasureTheory.Integrable (fun z : ℝ =>
      Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
        * ((Work.Spaces.w z) ^ 2 * (mm z + IIz z)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine ((hm_int.add hI_int).const_mul
      (Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2))).congr ?_
    filter_upwards with z
    show Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
        * ((Work.Spaces.w z) ^ 2 * mm z + (Work.Spaces.w z) ^ 2 * IIz z)
      = Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
        * ((Work.Spaces.w z) ^ 2 * (mm z + IIz z))
    ring
  have hslice_int : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => |Work.FTS.TransportS.leafGam α z θ
        * Work.Spaces.mixed 0 1 A z θ * Work.Spaces.DzIter 5 f z θ
        * Work.Spaces.mixed 5 1 f z θ|) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [show MeasureTheory.volume.restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => (hslice z hz).1)
  have houter_le : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ‖∫ θ in Work.Spaces.Iθ, |Work.FTS.TransportS.leafGam α z θ
        * Work.Spaces.mixed 0 1 A z θ * Work.Spaces.DzIter 5 f z θ
        * Work.Spaces.mixed 5 1 f z θ|‖
        ≤ Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
            * ((Work.Spaces.w z) ^ 2 * (mm z + IIz z)) := by
    rw [show MeasureTheory.volume.restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg (fun θ => abs_nonneg _))]
    exact (hslice z hz).2
  have houter : MeasureTheory.Integrable (fun z : ℝ =>
      ∫ θ in Work.Spaces.Iθ, |Work.FTS.TransportS.leafGam α z θ
        * Work.Spaces.mixed 0 1 A z θ * Work.Spaces.DzIter 5 f z θ
        * Work.Spaces.mixed 5 1 f z θ|) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.Integrable.mono' hmaj_int hFaesm houter_le
  -- ## Fubini
  obtain ⟨hGint, hGval⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 0 1 A z θ
      * Work.Spaces.DzIter 5 f z θ * Work.Spaces.mixed 5 1 f z θ|)
    (fun z θ => abs_nonneg _)
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcontG)
    hslice_int houter
  -- ## the numerical bound
  have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 0 1 A z θ
          * Work.Spaces.DzIter 5 f z θ * Work.Spaces.mixed 5 1 f z θ|)
      ≤ 300 * (Real.sqrt Cmz + 1) * α ^ (-(3 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
    have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 0 1 A z θ
            * Work.Spaces.DzIter 5 f z θ * Work.Spaces.mixed 5 1 f z θ|)
        ≤ Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
            * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (mm z + IIz z)) := by
      have hmono := MeasureTheory.integral_mono_ae houter hmaj_int (by
        filter_upwards [houter_le] with z hz
        rwa [Real.norm_of_nonneg (MeasureTheory.integral_nonneg (fun θ => abs_nonneg _))] at hz)
      exact hmono.trans_eq (MeasureTheory.integral_const_mul _ _)
    have h2 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (mm z + IIz z))
        ≤ 2 * Work.Spaces.HkSq α 6 f := by
      rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (mm z + IIz z))
          = (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * mm z)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * IIz z) from by
        rw [← MeasureTheory.integral_add hm_int hI_int]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))]
      linarith
    have h3 : Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
        = Real.sqrt 2010 * α ^ (-(1 / 2 : ℝ)) * Real.sqrt Cmz * K4 := by
      have hgl : (201 : ℝ) / (Work.Spaces.gam α - 1) = 2010 / α := by rw [hγeq]; ring
      have hs1 : Real.sqrt (2010 / α) = Real.sqrt 2010 * α ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_div' _ hα0.le,
          show Real.sqrt α = α ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow α,
          div_eq_mul_inv, ← Real.rpow_neg hα0.le]
      have hs2 : Real.sqrt (Cmz * K4 ^ 2) = Real.sqrt Cmz * K4 := by
        rw [Real.sqrt_mul' _ (sq_nonneg K4), Real.sqrt_sq hK4]
      rw [hgl, hs1, hs2]
      ring
    have h5 : Real.sqrt 2010 * α ^ (-(1 / 2 : ℝ)) * Real.sqrt Cmz * K4
          * (2 * Work.Spaces.HkSq α 6 f)
        ≤ 300 * (Real.sqrt Cmz + 1) * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
      have hCmz1 : Real.sqrt Cmz ≤ Real.sqrt Cmz + 1 := by linarith [Real.sqrt_nonneg Cmz]
      have hαinv : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
      have haux : Real.sqrt 2010 * Real.sqrt Cmz ≤ 150 * (Real.sqrt Cmz + 1) := by
        have h45 : Real.sqrt 2010 ≤ 45 := by
          rw [Real.sqrt_le_iff]; norm_num
        have hs : Real.sqrt 2010 * Real.sqrt Cmz ≤ 45 * Real.sqrt Cmz :=
          mul_le_mul_of_nonneg_right h45 (Real.sqrt_nonneg _)
        nlinarith [hs, Real.sqrt_nonneg Cmz]
      have hcore : α ^ (-(1 / 2 : ℝ)) * K4 * Work.Spaces.HkSq α 6 f
          ≤ α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
        have h1' : K4 ≤ 1 + K0 + K4 := by linarith
        have h2' : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
        have h3' : 0 ≤ α ^ (-(3 : ℝ)) := Real.rpow_nonneg hα0.le _
        have h6 : 0 ≤ (1 : ℝ) + K0 + K4 := by linarith
        have h7 : 0 ≤ (1 : ℝ) + Work.Spaces.HkSq α 6 f := by linarith
        calc α ^ (-(1 / 2 : ℝ)) * K4 * Work.Spaces.HkSq α 6 f
            = α ^ (-(1 / 2 : ℝ)) * (K4 * Work.Spaces.HkSq α 6 f) := by ring
          _ ≤ α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
              refine mul_le_mul hαinv ?_ (mul_nonneg hK4 hH) h3'
              exact mul_le_mul h1' h2' hH h6
      calc Real.sqrt 2010 * α ^ (-(1 / 2 : ℝ)) * Real.sqrt Cmz * K4
            * (2 * Work.Spaces.HkSq α 6 f)
          = 2 * (Real.sqrt 2010 * Real.sqrt Cmz) * (α ^ (-(1 / 2 : ℝ)) * K4
              * Work.Spaces.HkSq α 6 f) := by ring
        _ ≤ 2 * (150 * (Real.sqrt Cmz + 1))
              * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left haux (by norm_num)) hcore ?_ ?_
            · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _) hK4) hH
            · positivity
        _ = 300 * (Real.sqrt Cmz + 1) * α ^ (-(3 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by ring
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 0 1 A z θ
            * Work.Spaces.DzIter 5 f z θ * Work.Spaces.mixed 5 1 f z θ|)
        ≤ Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
            * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (mm z + IIz z)) := h1
      _ ≤ Real.sqrt (201 / (Work.Spaces.gam α - 1)) * Real.sqrt (Cmz * K4 ^ 2)
            * (2 * Work.Spaces.HkSq α 6 f) := by
          refine mul_le_mul_of_nonneg_left h2 ?_
          exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt 2010 * α ^ (-(1 / 2 : ℝ)) * Real.sqrt Cmz * K4
            * (2 * Work.Spaces.HkSq α 6 f) := by rw [h3]
      _ ≤ _ := h5
  -- ## conclusion
  have hHf : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 0 1 A p.1 p.2 * Work.Spaces.mixed 5 0 f p.1 p.2
      * Work.Spaces.mixed 5 1 f p.1 p.2) pm := by
    refine MeasureTheory.Integrable.mono' hGint ?_ ?_
    · exact Work.Spaces.aesm_of_continuousOn_Qd _ (by
        exact ((((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.contOn_leafGam α).mul
          (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hAsm.mixed 0 1))).mul
          (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hfsm.DzIter 5))).mul
          (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hfsm.mixed 5 1))))
    · filter_upwards with p
      rw [Real.norm_eq_abs]
      exact le_of_eq rfl
  refine ⟨hHf, ?_⟩
  exact MeasureTheory.abs_integral_le_integral_abs.trans (hGval.trans_le hmain)

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
