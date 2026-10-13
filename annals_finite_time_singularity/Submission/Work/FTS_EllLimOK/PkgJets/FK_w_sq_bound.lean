import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS_EllLimOK.PkgJets.ThetaBoundBasic
import Submission.Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

/-- The pointwise (in `z`) identity behind the sharp `L²`-bound for the angular moment:
for `θ ∈ Iθ` the weighted datum `K · Sw · Gaz` is the radial weight times `g · K`. -/
private theorem FK_K_Sw_Gaz_eq {g : ℝ → ℝ → ℝ} (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ * Work.FTS.GalBasis.cc.Gaz g z θ
      = Work.Spaces.w z * (g z θ * Work.Spaces.K θ) := by
  rcases eq_or_ne (Work.FTS.GalBasis.cc.Sw θ) 0 with hS | hS
  · have hK : Work.Spaces.K θ = 0 :=
      Work.FTS.GalBasis.cc.sw_eq_zero_imp_K_eq_zero hθ hS
    rw [hS, hK]
    ring
  · rw [Work.FTS.GalBasis.cc.Gaz_apply, div_eq_mul_inv]
    field_simp

theorem FK_w_sq_bound {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.ClassC.ClassC α g) :
    MeasureTheory.IntegrableOn (fun z => (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g := by
  have hmem7 : Work.Spaces.HkMem α 7 g := hg.mem
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    HkMem_mono_le hg.reg (show (4 : ℕ) ≤ 7 by norm_num) hmem7
  -- the per-`z` sharp bound for the weighted angular moment
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ Work.FTS.GalBasis.cc.BK ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro z hz
    have hint : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 4 g z θ) Work.Spaces.Iθ := hmem4.1 z hz
    have hcs := Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le α g hint
    -- the weighted angular profile equals the radial weight times `FK`
    have hid : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ * Work.FTS.GalBasis.cc.Gaz g z θ)
        = Work.Spaces.w z * Work.Construction.FK g z := by
      have hcongr : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ * Work.FTS.GalBasis.cc.Gaz g z θ)
          = ∫ θ in Work.Spaces.Iθ, Work.Spaces.w z * (g z θ * Work.Spaces.K θ) := by
        refine MeasureTheory.integral_congr_ae ?_
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => FK_K_Sw_Gaz_eq z θ hθ)
      rw [hcongr, MeasureTheory.integral_const_mul, Work.Construction.FK]
    have hI0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ :=
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    have hBK0 : 0 ≤ Work.FTS.GalBasis.cc.BK := Work.FTS.GalBasis.cc.BK_nonneg
    have hs : |Work.Spaces.w z * Work.Construction.FK g z| ≤ Work.FTS.GalBasis.cc.BK
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
      rw [← hid]; exact hcs
    have hsq : (Work.Spaces.w z * Work.Construction.FK g z) ^ 2
        ≤ (Work.FTS.GalBasis.cc.BK
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (Work.Spaces.w z * Work.Construction.FK g z)) hs 2
      rwa [sq_abs] at h
    have hmain : (Work.Spaces.w z * Work.Construction.FK g z) ^ 2
        ≤ Work.FTS.GalBasis.cc.BK ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
      have hstep : (Work.FTS.GalBasis.cc.BK
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) ^ 2
          = Work.FTS.GalBasis.cc.BK ^ 2
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
        rw [mul_pow, Real.sq_sqrt hI0]
      calc (Work.Spaces.w z * Work.Construction.FK g z) ^ 2
          ≤ (Work.FTS.GalBasis.cc.BK
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) ^ 2 := hsq
        _ = Work.FTS.GalBasis.cc.BK ^ 2
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := hstep
    have hcomm : (Work.Spaces.w z * Work.Construction.FK g z) ^ 2
        = (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    rwa [hcomm] at hmain
  -- measurability of the integrand
  have hmeasw : Measurable (fun z : ℝ => Work.Spaces.w z) := by
    unfold Work.Spaces.w
    fun_prop
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hcont := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fk_cont_FK hg.reg hmem4
    have h1 : AEStronglyMeasurable (fun z => Work.Construction.FK g z)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      hcont.aestronglyMeasurable measurableSet_Ioi
    have hEq : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
    have h2 : AEStronglyMeasurable (fun z => Work.Construction.FK g z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set hEq]
      exact h1
    exact (h2.pow 2).mul ((hmeasw.pow_const 2).aestronglyMeasurable)
  have hbigInt : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.GalBasis.cc.BK ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) Work.Spaces.Iz :=
    hmem4.2.const_mul _
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hbigInt haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpt z hz
  · calc (∫ z in Work.Spaces.Iz,
          (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫ z in Work.Spaces.Iz, Work.FTS.GalBasis.cc.BK ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
            hbigInt
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
      _ = Work.FTS.GalBasis.cc.BK ^ 2
            * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 4 g z θ) :=
          MeasureTheory.integral_const_mul _ _
      _ = Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g := by
          rw [Work.Spaces.HkSq]

end Work.FTS_EllLimOK.PkgJets
