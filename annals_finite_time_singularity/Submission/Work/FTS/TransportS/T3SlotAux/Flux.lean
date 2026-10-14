import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.T3BadAux.slot_slice_le
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6Aux.excDz5Dth2Le4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6Aux

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0)
open Work.FTS.OpenPkg.ProdOpen (sin_two_pos ae_mem_Ioo_Iθ aesm_integral_right
  sin_neg_gam_nonneg continuousOn_sin_neg_gam continuousOn_w_sq continuousOn_Wt)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## Integrability of the `q`-side slice at level four -/

/-- The `θ`-slice of `(D_θ²q)² sin(2·)^{-γ}` is integrable, from the level-four membership
`HkMem α 4 q` (`D_θ²q = mixed 0 2 q` is a mixed slot of order two, and the level-four
integrand carries its `Wt`-weighted square). -/
theorem integrableOn_dth2_sq4 {α : ℝ} {q : ℝ → ℝ → ℝ} (hQ : SmoothOpen q)
    (hmemQ : HkMem α 4 q) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (mixed 0 2 q z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α))) Iθ := by
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (mixed 0 2 q z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α))) (volume.restrict Iθ) := by
    refine Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_
    have hbase : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
    refine ContinuousOn.mul (((hQ.mixed 0 2).curry_θ hz).continuousOn.pow 2)
      (hbase.continuousOn.rpow_const ?_)
    intro σ hσ
    exact Or.inl (ne_of_gt (sin_two_pos hσ))
  refine Integrable.mono' (hmemQ.1 z hz.le) hmeas ?_
  filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
  have hnn : 0 ≤ (mixed 0 2 q z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_pos hσ).le _)
  rw [Real.norm_of_nonneg hnn]
  have hw1 : (1 : ℝ) ≤ (w z) ^ 2 := one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  calc (mixed 0 2 q z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α))
      = (mixed 0 2 q z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)) * 1 := by ring
    _ ≤ (mixed 0 2 q z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)) * (w z) ^ 2 :=
        mul_le_mul_of_nonneg_left hw1
          (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_pos hσ).le _))
    _ = (mixed 0 2 q z σ * Wt α z σ) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z σ (sin_two_pos hσ)]
        ring
    _ ≤ HkIntegrand α 4 q z σ :=
        sq_le_HkIntegrand_mixed α 4 q z σ 2 0 (by norm_num) (by norm_num)

/-! ## The exceptional term -/

theorem excDz5Dth2Le4 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (p q : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen p → Work.Spaces.HkMem α 6 p →
    Work.FTS.EllipticEst.SmoothOpen q → Work.Spaces.HkMem α 4 q → Work.Spaces.HkMem α 6 q →
    Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter 5 p z θ
        * Work.Spaces.mixed 0 2 q z θ * Work.Spaces.Wt α z θ) ∧
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 5 p z θ
        * Work.Spaces.mixed 0 2 q z θ * Work.Spaces.Wt α z θ)
        ≤ C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 p * Work.Spaces.HkSq α 4 q := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.excMeanSide6Aux
  obtain ⟨Cq, hCqpos, hCq⟩ := Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform
  have hMq : (0 : ℝ) < max Cq 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨2 * C1 * max Cq 1, by positivity, ?_⟩
  intro α p q hα hα1 hP hmemP hQ hmemQ4 hmemQ6
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγle : gam α - 1 ≤ 1 := by rw [gam_sub_one]; linarith
  have hHkP : 0 ≤ HkSq α 6 p := HkSq_nonneg α 6 p
  have hHkQ : 0 ≤ HkSq α 4 q := HkSq_nonneg α 4 q
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ.le
  set M1 : ℝ → ℝ := fun z => ∫ θ in Iθ, (DzIter 5 p z θ) ^ 2 with hM1def
  set M2 : ℝ → ℝ := fun z => ∫ θ in Iθ, (mixed 5 1 p z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) with hM2def
  set J : ℝ → ℝ := fun z => ∫ θ in Iθ, (mixed 0 2 q z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) with hJdef
  have hM1val : ∀ z : ℝ, M1 z = ∫ θ in Iθ, (DzIter 5 p z θ) ^ 2 := fun z => by
    simp only [hM1def]
  have hM2val : ∀ z : ℝ, M2 z = ∫ θ in Iθ, (mixed 5 1 p z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) := fun z => by simp only [hM2def]
  have hJval : ∀ z : ℝ, J z = ∫ θ in Iθ, (mixed 0 2 q z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) := fun z => by simp only [hJdef]
  have hM1nn : ∀ z, 0 ≤ M1 z := fun z => by
    rw [hM1val z]; exact integral_nonneg fun θ => sq_nonneg _
  have hM2nn : ∀ z, 0 ≤ M2 z := fun z => by
    rw [hM2val z]; exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sin_neg_gam_nonneg hθ)
  have hJnn : ∀ z, 0 ≤ J z := fun z => by
    rw [hJval z]; exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sin_neg_gam_nonneg hθ)
  -- (1) the `q`-side is uniformly bounded by the `ℋ⁴`-norm of `q`
  have hJbd : ∀ z : ℝ, 0 < z → J z ≤ max Cq 1 * HkSq α 4 q := by
    intro z hz
    have h := hCq α q hα hα1 hQ hmemQ4 0 2 (by norm_num) (by norm_num) z hz
    rw [hJval z]
    exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left Cq 1) hHkQ)
  -- (2) the angular mean-term estimate on the `p`-slice, at every `z > 0`
  have hsob : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (DzIter 5 p z θ) ^ 2 ≤ C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) := by
    intro z hz θ hθ
    have h := hC1 α p hα hα1 hP hmemP z hz θ hθ
    simpa only [hM1val z, hM2val z] using h
  -- (3) pointwise domination of the two slice integrals by the `ℋ⁶`-integrand of `p`
  have hM1dom : ∀ z : ℝ, 0 < z →
      M1 z * (w z) ^ 2 ≤ ∫ θ in Iθ, HkIntegrand α 6 p z θ := by
    intro z hz
    have hfeq : M1 z * (w z) ^ 2
        = ∫ θ in Iθ, (DzIter 5 p z θ) ^ 2 * (w z) ^ 2 := by
      rw [hM1val z]
      exact (integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (DzIter 5 p z θ) ^ 2)).symm
    rw [hfeq]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ _ =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hmemP.1 z hz.le) ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    exact Work.FTS.StrongPersist.N6.dzIter_sq_w_sq_le6 α hα p 5 hz hθ (by norm_num)
  have hM2dom : ∀ z : ℝ, 0 < z →
      M2 z * (w z) ^ 2 ≤ ∫ θ in Iθ, HkIntegrand α 6 p z θ := by
    intro z hz
    have hfeq : M2 z * (w z) ^ 2 = ∫ θ in Iθ, (mixed 5 1 p z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2 := by
      rw [hM2val z]
      have hfun : (fun θ : ℝ => (mixed 5 1 p z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2)
          = fun θ : ℝ => ((mixed 5 1 p z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(gam α))) * (w z) ^ 2 := rfl
      rw [hfun]
      exact (integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (mixed 5 1 p z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(gam α)))).symm
    rw [hfeq]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (sin_neg_gam_nonneg hθ)) (sq_nonneg _))
      (hmemP.1 z hz.le) ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hsin : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hkey : (mixed 5 1 p z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
          * (w z) ^ 2
        = (mixed 5 1 p z θ * Wt α z θ) ^ 2 := by
      rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hsin]; ring
    rw [hkey]
    exact sq_le_HkIntegrand_mixed α 6 p z θ 1 5 (by norm_num) (by norm_num)
  -- (4) a.e. strong measurability and `z`-integrability of the two slice integrals
  have hAESM1 : AEStronglyMeasurable (fun z : ℝ => M1 z * (w z) ^ 2)
      (volume.restrict Iz) := by
    have hcont : ContinuousOn (Function.uncurry
        (fun z θ : ℝ => (DzIter 5 p z θ) ^ 2 * (w z) ^ 2)) Q0 := by
      show ContinuousOn (fun u : ℝ × ℝ => (DzIter 5 p u.1 u.2) ^ 2
        * (w u.1) ^ 2) Q0
      exact ((hP.DzIter 5).continuousOn.pow 2).mul continuousOn_w_sq
    have h := aesm_integral_right (F := fun z θ =>
      (DzIter 5 p z θ) ^ 2 * (w z) ^ 2) hcont
    have h2 : (fun z : ℝ => ∫ θ in Iθ, (DzIter 5 p z θ) ^ 2 * (w z) ^ 2)
        = fun z : ℝ => M1 z * (w z) ^ 2 := by
      funext z
      rw [hM1val z]
      exact integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (DzIter 5 p z θ) ^ 2)
    rwa [h2] at h
  have hAESM2 : AEStronglyMeasurable (fun z : ℝ => M2 z * (w z) ^ 2)
      (volume.restrict Iz) := by
    have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
        (mixed 5 1 p z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2)) Q0 := by
      show ContinuousOn (fun u : ℝ × ℝ => (mixed 5 1 p u.1 u.2) ^ 2
        * (Real.sin (2 * u.2)) ^ (-(gam α)) * (w u.1) ^ 2) Q0
      exact (((hP.mixed 5 1).continuousOn.pow 2).mul (continuousOn_sin_neg_gam α)).mul
        continuousOn_w_sq
    have h := aesm_integral_right (F := fun z θ => (mixed 5 1 p z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2) hcont
    have h2 : (fun z : ℝ => ∫ θ in Iθ, (mixed 5 1 p z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2)
        = fun z : ℝ => M2 z * (w z) ^ 2 := by
      funext z
      rw [hM2val z]
      exact integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (mixed 5 1 p z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(gam α)))
    rwa [h2] at h
  have hAESMJ : AEStronglyMeasurable J (volume.restrict Iz) := by
    have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
        (mixed 0 2 q z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)))) Q0 := by
      show ContinuousOn (fun u : ℝ × ℝ => (mixed 0 2 q u.1 u.2) ^ 2
        * (Real.sin (2 * u.2)) ^ (-(gam α))) Q0
      exact ((hQ.mixed 0 2).continuousOn.pow 2).mul (continuousOn_sin_neg_gam α)
    have h := aesm_integral_right (F := fun z θ => (mixed 0 2 q z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α))) hcont
    exact h
  have hInt1 : Integrable (fun z : ℝ => M1 z * (w z) ^ 2) (volume.restrict Iz) := by
    refine Integrable.mono' hmemP.2 hAESM1 ?_
    filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (hM1nn z) (sq_nonneg _))]
    exact hM1dom z hz
  have hInt2 : Integrable (fun z : ℝ => M2 z * (w z) ^ 2) (volume.restrict Iz) := by
    refine Integrable.mono' hmemP.2 hAESM2 ?_
    filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (hM2nn z) (sq_nonneg _))]
    exact hM2dom z hz
  have hz1 : (∫ z in Iz, M1 z * (w z) ^ 2) ≤ HkSq α 6 p := by
    have h := integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (hM1nn z) (sq_nonneg _)) hmemP.2
      (by filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz; exact hM1dom z hz)
    exact h
  have hz2 : (∫ z in Iz, M2 z * (w z) ^ 2) ≤ HkSq α 6 p := by
    have h := integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (hM2nn z) (sq_nonneg _)) hmemP.2
      (by filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz; exact hM2dom z hz)
    exact h
  -- (5) the per-`z` bound on the angular integral of the exceptional integrand
  have hzpt : ∀ z : ℝ, 0 < z → (∫ θ in Iθ, (DzIter 5 p z θ
        * mixed 0 2 q z θ * Wt α z θ) ^ 2)
      ≤ C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2 * J z := by
    intro z hz
    have hGint := (integrableOn_dth2_sq4 hQ hmemQ4 hz).const_mul
      (C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2)
    have hpt : ∀ᵐ θ ∂(volume.restrict Iθ),
        (DzIter 5 p z θ * mixed 0 2 q z θ * Wt α z θ) ^ 2
        ≤ (C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2)
          * ((mixed 0 2 q z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      have hsin : 0 < Real.sin (2 * θ) := sin_two_pos hθ
      have h1 := hsob z hz θ hθ
      rw [show (DzIter 5 p z θ * mixed 0 2 q z θ * Wt α z θ) ^ 2
          = ((DzIter 5 p z θ) ^ 2 * (w z) ^ 2)
            * ((mixed 0 2 q z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) from by
          rw [mul_pow, mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hsin]; ring]
      have hstep : (DzIter 5 p z θ) ^ 2 * (w z) ^ 2
          ≤ C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hstep
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))
    refine le_trans (integral_mono_of_nonneg ?_ hGint hpt) ?_
    · exact ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => sq_nonneg _
    · rw [integral_const_mul, hJval z]
  -- (6) integrability of the `max`-majorant
  have hmajInt : Integrable (fun z : ℝ => C1 * (M1 z + (gam α - 1)⁻¹ * M2 z)
      * (w z) ^ 2 * (max Cq 1 * HkSq α 4 q)) (volume.restrict Iz) := by
    have hbase : Integrable (fun z : ℝ => C1 * (max Cq 1 * HkSq α 4 q) * (M1 z * (w z) ^ 2)
        + C1 * (max Cq 1 * HkSq α 4 q) * ((gam α - 1)⁻¹ * (M2 z * (w z) ^ 2)))
        (volume.restrict Iz) :=
      (hInt1.const_mul (C1 * (max Cq 1 * HkSq α 4 q))).add
        ((hInt2.const_mul (gam α - 1)⁻¹).const_mul (C1 * (max Cq 1 * HkSq α 4 q)))
    refine Integrable.mono' hbase ?_ ?_
    · have h1 : AEStronglyMeasurable (fun z : ℝ => C1 * (max Cq 1 * HkSq α 4 q)
          * (M1 z * (w z) ^ 2)
          + C1 * (max Cq 1 * HkSq α 4 q) * ((gam α - 1)⁻¹ * (M2 z * (w z) ^ 2)))
          (volume.restrict Iz) :=
        (hAESM1.const_mul _).add ((hAESM2.const_mul _).const_mul _)
      refine h1.congr ?_
      filter_upwards with z
      ring
    · filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC1pos.le
        (add_nonneg (hM1nn z) (mul_nonneg hγinv (hM2nn z)))) (sq_nonneg _))
        (mul_nonneg hMq.le hHkQ))]
      ring_nf
      nlinarith [hM1nn z, hM2nn z, sq_nonneg (w z), hγinv, hHkP, hHkQ, hMq]
  -- (7) the `L²`-square bound
  have hL2Sq : L2Sq (fun z θ => DzIter 5 p z θ * mixed 0 2 q z θ
        * Wt α z θ)
      ≤ 2 * C1 * max Cq 1 / (gam α - 1) * HkSq α 6 p * HkSq α 4 q := by
    rw [L2Sq]
    have hB : (∫ z in Iz, ∫ θ in Iθ, (DzIter 5 p z θ * mixed 0 2 q z θ
          * Wt α z θ) ^ 2)
        ≤ ∫ z in Iz, C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2
            * (max Cq 1 * HkSq α 4 q) := by
      refine integral_mono_of_nonneg ?_ hmajInt ?_
      · exact ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
          integral_nonneg fun θ => sq_nonneg _
      · filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
        exact le_trans (hzpt z hz) (mul_le_mul_of_nonneg_left (hJbd z hz) (mul_nonneg
          (mul_nonneg hC1pos.le (add_nonneg (hM1nn z) (mul_nonneg hγinv (hM2nn z))))
          (sq_nonneg _)))
    refine le_trans hB ?_
    have hC : (∫ z in Iz, C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2
          * (max Cq 1 * HkSq α 4 q))
        = C1 * (max Cq 1 * HkSq α 4 q) * ((∫ z in Iz, M1 z * (w z) ^ 2)
            + (gam α - 1)⁻¹ * (∫ z in Iz, M2 z * (w z) ^ 2)) := by
      have hfun1 : (fun z : ℝ => C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2
            * (max Cq 1 * HkSq α 4 q))
          = fun z : ℝ => (C1 * (max Cq 1 * HkSq α 4 q))
            * ((M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2) := by
        funext z; ring
      rw [hfun1, integral_const_mul]
      have hfun2 : (fun z : ℝ => (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2)
          = fun z : ℝ => M1 z * (w z) ^ 2
            + ((gam α - 1)⁻¹ * (M2 z * (w z) ^ 2)) := by
        funext z; ring
      rw [hfun2, integral_add hInt1 (hInt2.const_mul (gam α - 1)⁻¹)]
      rw [integral_const_mul]
    rw [hC]
    have hX : (∫ z in Iz, M1 z * (w z) ^ 2) + (gam α - 1)⁻¹
          * (∫ z in Iz, M2 z * (w z) ^ 2)
        ≤ 2 * (gam α - 1)⁻¹ * HkSq α 6 p := by
      have h1 : (1 : ℝ) ≤ (gam α - 1)⁻¹ := by
        rw [one_le_inv₀ hγ]; simpa using hγle
      have hA1 : (∫ z in Iz, M1 z * (w z) ^ 2) ≤ (gam α - 1)⁻¹ * HkSq α 6 p :=
        le_trans hz1 (le_mul_of_one_le_left hHkP h1)
      have hA2 : (gam α - 1)⁻¹ * (∫ z in Iz, M2 z * (w z) ^ 2)
          ≤ (gam α - 1)⁻¹ * HkSq α 6 p := mul_le_mul_of_nonneg_left hz2 hγinv
      linarith
    have hfac : 0 ≤ C1 * (max Cq 1 * HkSq α 4 q) :=
      mul_nonneg hC1pos.le (mul_nonneg hMq.le hHkQ)
    have hstep := mul_le_mul_of_nonneg_left hX hfac
    refine le_trans hstep (le_of_eq ?_)
    rw [div_eq_mul_inv]; ring
  refine ⟨⟨?_, ?_⟩, hL2Sq⟩
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      have hzero : (fun θ : ℝ => (DzIter 5 p 0 θ * mixed 0 2 q 0 θ
          * Wt α 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        have hw0 : w (0 : ℝ) = 0 := by simp [w]
        simp [Wt, hw0]
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono' ((integrableOn_dth2_sq4 hQ hmemQ4 hpos).const_mul
        (C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2)) ?_ ?_
      · have hcont : ContinuousOn (fun θ : ℝ => (DzIter 5 p z θ
            * mixed 0 2 q z θ * Wt α z θ) ^ 2)
            (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
          have h1 : ContinuousOn (fun θ : ℝ => DzIter 5 p z θ)
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hP.DzIter 5).curry_θ hpos).continuousOn
          have h2 : ContinuousOn (fun θ : ℝ => mixed 0 2 q z θ)
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hQ.mixed 0 2).curry_θ hpos).continuousOn
          have hb : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(gam α / 2)))
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
            (show Continuous fun θ : ℝ => Real.sin (2 * θ) from by fun_prop).continuousOn.rpow_const
              (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))
          have h3 : ContinuousOn (fun θ : ℝ => Wt α z θ)
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
            have hfun : (fun θ : ℝ => Wt α z θ)
                = fun θ : ℝ => w z
                  * (Real.sin (2 * θ)) ^ (-(gam α / 2)) := by
              funext θ; rw [Wt, wTheta]
            rw [hfun]
            exact continuousOn_const.mul hb
          exact ((h1.mul h2).mul h3).pow 2
        exact Work.H2.T1Q.aesm_Iθ_of_continuousOn hcont
      · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
        have hsin : 0 < Real.sin (2 * θ) := sin_two_pos hθ
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        rw [show (DzIter 5 p z θ * mixed 0 2 q z θ * Wt α z θ) ^ 2
            = ((DzIter 5 p z θ) ^ 2 * (w z) ^ 2)
              * ((mixed 0 2 q z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) from by
          rw [mul_pow, mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hsin]; ring]
        have hstep : (DzIter 5 p z θ) ^ 2 * (w z) ^ 2
            ≤ C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2 :=
          mul_le_mul_of_nonneg_right (hsob z hpos θ hθ) (sq_nonneg _)
        exact mul_le_mul_of_nonneg_right hstep
          (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))
  · have haesm : AEStronglyMeasurable (fun z : ℝ => ∫ θ in Iθ,
        (DzIter 5 p z θ * mixed 0 2 q z θ * Wt α z θ) ^ 2)
        (volume.restrict Iz) := by
      refine aesm_integral_right (F := fun z θ => (DzIter 5 p z θ
        * mixed 0 2 q z θ * Wt α z θ) ^ 2) ?_
      have hW := continuousOn_Wt (α := α)
      exact (((hP.DzIter 5).continuousOn.mul (hQ.mixed 0 2).continuousOn).mul hW).pow 2
    refine Integrable.mono' hmajInt haesm ?_
    filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact le_trans (hzpt z hz) (mul_le_mul_of_nonneg_left (hJbd z hz) (mul_nonneg
      (mul_nonneg hC1pos.le (add_nonneg (hM1nn z) (mul_nonneg hγinv (hM2nn z))))
      (sq_nonneg _)))

end Work.FTS.StrongPersist.H6Rows.Npair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.Hon

/-- The uncurried `ℋ^k`-integrand of a function which is `C^∞` on the open quadrant is
a.e. strongly measurable for the product of the two restricted Lebesgue measures: it is
continuous on the open quadrant, and that quadrant is conull inside `Iz ×ˢ Iθ`. -/
theorem aesm_HkIntegrand_prod_open {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hsg α k)

theorem HkProdOpen {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p, Work.Spaces.HkIntegrand α k g p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) = Work.Spaces.HkSq α k g := by
  obtain ⟨hint, hval⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => Work.Spaces.HkIntegrand α k g z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
    (aesm_HkIntegrand_prod_open hsg)
    ((MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iz from
      measurableSet_Ici)).mpr (Filter.Eventually.of_forall fun z hz => hmem.1 z hz))
    hmem.2
  exact ⟨hint, by rw [hval]; rfl⟩

end Work.FTS.StrongPersist.N6Trans.Hon
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_eta_eq canonW_gam_eq
  canonW_mono cs_sqrt_le)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The slot predicate at level six -/

/-- A function `X` is a canonical slot of `ℋ⁶` for the datum `f` with exponent `q` if its
`canonW q`-weighted square is dominated, pointwise on `Iz × Iθ`, by the `ℋ⁶`-integrand of
`f`.  This is the level-six analogue of `Work.FTS.TransportS.SlotT2.SlotW`, and it is the
only property of a slot that the Cauchy–Schwarz bound uses. -/
structure SlotW6 (α q : ℝ) (X : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  le : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
    canonW q z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ

/-- The pointwise domination of a pure `D_z`-slot `D_z^j h`, `j ≤ 6`, at the exponent `q ≤ η`. -/
theorem canonW_mul_z_le6 (α : ℝ) (h : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq : q ≤ Work.Spaces.eta) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (j : ℕ) (hj : j ≤ 6) :
    canonW q z θ * (Work.Spaces.DzIter j h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h z θ := by
  have hw : canonW q z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
    rw [← canonW_eta_eq z θ hθ]
    exact canonW_mono hq0 hq hθ
  calc canonW q z θ * (Work.Spaces.DzIter j h z θ) ^ 2
      ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter j h z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.DzIter j h z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 6 h z θ j hj

/-- The pointwise domination of a mixed slot `D_z^jD_θ^i h`, `1 ≤ i`, `i + j ≤ 6`, at the
exponent `q ≤ γ`. -/
theorem canonW_mul_mixed_le6 (α : ℝ) (h : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    canonW q z θ * (Work.Spaces.mixed j i h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h z θ := by
  have hw : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← canonW_gam_eq α z θ hθ]
    exact canonW_mono hq0 hqγ hθ
  calc canonW q z θ * (Work.Spaces.mixed j i h z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i h z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.mixed j i h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 6 h z θ i j hi hij

/-- A pure `D_z`-slot `D_z^j h`, `j ≤ 6`, priced with `q ≤ η`. -/
theorem slotW6_z (α : ℝ) {q : ℝ} (hq0 : 0 < q) (hq : q ≤ Work.Spaces.eta)
    (h : ℝ → ℝ → ℝ) (j : ℕ) (hj : j ≤ 6) :
    SlotW6 α q (Work.Spaces.DzIter j h) h := by
  refine ⟨fun z hz θ hθ => ?_⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [canonW_zero_z, zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 6 h 0 θ
  · exact canonW_mul_z_le6 α h hq0 hq hθ j hj

/-- A mixed slot `D_z^jD_θ^i h`, `1 ≤ i`, `i + j ≤ 6`, priced with `q ≤ γ`. -/
theorem slotW6_mixed (α : ℝ) {q : ℝ} (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α)
    (h : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    SlotW6 α q (Work.Spaces.mixed j i h) h := by
  refine ⟨fun z hz θ hθ => ?_⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [canonW_zero_z, zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 6 h 0 θ
  · exact canonW_mul_mixed_le6 α h hq0 hqγ hθ j i hi hij

/-! ## The two-level Cauchy–Schwarz engine at level six -/


/-! ## The energies of the slots -/



/-! ## The pointwise bound of order `≤ 4` with the `α^{-1/2}` loss -/

/-- **The pointwise bound at level six.**  For `h` of class `SmoothOpen` with honest
`HkMem α 6 h`, every `D_z^bD_θ^a h` with `a + b ≤ 4` is bounded on the open quadrant by
`C α^{-1/2} |h|_{ℋ⁶}`, with a universal `C`.

This is the square-root form of the proved level-six pointwise bound
`Work.FTS.StrongPersist.N6.PwAny6` (which gives the square with the factor `(γ-1)^{-1}` and
`γ - 1 = α/10`). -/
theorem supSix : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.HkMem α 6 h →
    ∀ b a : ℕ, a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a h z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 h := by
  obtain ⟨C, hC, hPw⟩ := Work.FTS.StrongPersist.N6.PwAny6
  refine ⟨Real.sqrt (C * 10), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α h hα hα1 hsm hmem b a hab z θ hz hθ hθ2
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγeq : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have hA : 0 ≤ Work.Spaces.HkSq α 6 h := Work.Spaces.HkSq_nonneg α 6 h
  have hsq : (Work.Spaces.mixed b a h z θ) ^ 2
      ≤ C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 h :=
    hPw α h b a hα hα1 hsm hmem hab z hz θ ⟨hθ, hθ2⟩
  have hfac : C / (Work.Spaces.gam α - 1) = C * 10 / α := by
    rw [hγeq, div_div_eq_mul_div]
  have hinv : (Real.sqrt α)⁻¹ = α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hα.le]
  have hsqrt : Real.sqrt (C / (Work.Spaces.gam α - 1))
      = Real.sqrt (C * 10) * α ^ (-(1 / 2 : ℝ)) := by
    rw [hfac, Real.sqrt_div (by positivity), div_eq_mul_inv, hinv]
  have hmain : Real.sqrt (C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 h)
      = Real.sqrt (C * 10) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 h := by
    rw [Real.sqrt_mul (div_nonneg (by positivity) hγ.le), hsqrt]
    rfl
  calc |Work.Spaces.mixed b a h z θ|
      = Real.sqrt ((Work.Spaces.mixed b a h z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 h) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (C * 10) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 h := hmain

end Work.FTS.StrongPersist.N6Trans.T1SixAux
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T3SlotAux.Flux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T3SlotAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Smoothness of the `sin(2θ)^r` factor -/

theorem contDiffOn_sin_rpow_Q0 (r : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ r) Work.FTS.EllipticEst.Q0 := by
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    ((Real.contDiff_sin.contDiffOn).comp (contDiffOn_const.mul contDiffOn_snd)
      (fun p _ => Set.mem_univ _)).of_le le_top
  refine hsmooth.rpow contDiffOn_const fun p hp => ?_
  have hp' : 0 < p.2 ∧ p.2 < Real.pi / 2 := by
    have h := hp
    simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at h
    exact h.2
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp'.1])
    (by linarith [hp'.2, Real.pi_pos]))

/-- The product of a `SmoothOpen` function with the smooth factor `sin(2θ)^r` is `SmoothOpen`
on the open quadrant. -/
theorem smoothOpen_sin_rpow_mul {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (r : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (Real.sin (2 * θ)) ^ r * f z θ) := by
  have h1 := contDiffOn_sin_rpow_Q0 r
  have h2 : Function.uncurry (fun z θ => (Real.sin (2 * θ)) ^ r * f z θ)
      = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ r * Function.uncurry f p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h2]
  exact h1.mul hf

/-- `sghard α k θ = sin(2θ)^{-qOf α a}` for `k.val = a`. -/
theorem sghard_eq_rpow {α : ℝ} {k : Fin 5} {a : ℕ} (hk : k.val = a) (θ : ℝ) :
    Work.FTS.H2.sghard α k θ = (Real.sin (2 * θ)) ^ (-(qOf α a)) := by
  rcases eq_or_ne a 0 with ha0 | ha
  · subst ha0
    have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Work.FTS.H2.sghard_apply_zero, qOf_zero]
  · have hkv : k.val ≠ 0 := by rw [hk]; exact ha
    rw [Work.FTS.H2.sghard_apply_ne α k hkv θ, qOf_of_ne ha]

/-! ## The identification of the exceptional term with `gK` -/

/-- The exceptional term of the slot `(a,b) = (a, 4-a)` with the leaf weight `ρ = canonW q`
is the `k`-th summand `gK α h g k` of `Hhard`, with `h = sin(2θ)^{qOf α a - q} · f`. -/
theorem flux_ident {α q r : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ} {k : Fin 5}
    (hk : k.val = a) (hab : a + b = 4) (hr : r = qOf α a - q)
    (hρeq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ = Work.FTS.TransportS.SlotT2.canonW q z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ z θ * f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
        * Work.Spaces.mixed b a g z θ
      = Work.FTS.TransportS.gK α (fun z θ => (Real.sin (2 * θ)) ^ r * f z θ) g k z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsub : 4 - k.val = b := by rw [hk]; omega
  have hThard : Work.FTS.H2.Thard g k = Work.Spaces.mixed b a g := by
    rw [Work.FTS.H2.Thard_eq_mixed]
    funext z' θ'
    rw [hsub, hk]
  have hcomb : (Real.sin (2 * θ)) ^ r * (Real.sin (2 * θ)) ^ (-(qOf α a))
      = (Real.sin (2 * θ)) ^ (-q) := by
    rw [hr, ← Real.rpow_add hs]
    congr 1
    ring
  have hw : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      = ((Real.sin (2 * θ)) ^ r * (Real.sin (2 * θ)) ^ (-(qOf α a)))
        * (Work.Spaces.w z) ^ 2 := by
    rw [hcomb]
    ring
  rw [hρeq z θ hz hθ.1 hθ.2, Work.FTS.TransportS.SlotT2.canonW,
    Work.FTS.TransportS.gK, hThard, sghard_eq_rpow hk θ]
  simp only [Work.Spaces.Dz]
  rw [hw]
  ring

/-! ## The bound on the exceptional term -/



end Work.FTS.TransportS.T3SlotAux
end
end
