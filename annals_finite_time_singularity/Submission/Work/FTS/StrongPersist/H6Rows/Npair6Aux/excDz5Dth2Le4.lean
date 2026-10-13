/-
# `Work.FTS.StrongPersist.H6Rows.Npair6Aux.excDz5Dth2Le4`

The **exceptional term** `D_z⁵p · D_θ²q` of the level-six product rule, with the `q`-side
priced by the *level-four* norm `|q|²_{ℋ⁴}`.

This is the sharper companion of `Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5Dth2Six`
(which prices the `q`-side by `|q|²_{ℋ⁶}`) and of `excDz5_mixed_pair_bound` (the general
`D_z⁵p · D_z^bD_θ^aq` with `1 ≤ a`, `a + b ≤ 5`).  The two factors are treated by the two
matching angular estimates:

* the `p`-side slot `D_z⁵p` is a *pure radial* slot, bounded pointwise by the angular
  mean-term inequality `T1SixAux.excMeanSide6Aux` (the slice form of
  `OpenPkg.ProdOpen.sob_theta_mean`) which prices it by the `ℋ⁶`-data of `p` with the
  factor `(γ-1)⁻¹`;
* the `q`-side slot `D_θ²q = mixed 0 2 q` is a mixed slot of order two, and the *uniform*
  slice bound `TransportS.T2SupB2.mixed_slice_z_uniform` (slot `(j,i) = (0,2)`, `i + j = 2 ≤ 3`)
  prices `∫_θ (D_θ²q(z,θ))² sin(2θ)^{-γ}` uniformly in `z` by `3 |q|²_{ℋ⁴}`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.ProductTools
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5Dth2Six
import Submission.Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform
import Submission.Work.FTS.StrongPersist.N6.PwOpen6

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
