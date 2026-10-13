import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Sys.EPCDefs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FM.Core2
import Submission.Work.Construction.Basic
import Submission.Work.Coercivity.integral_Itheta_K
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_Prelim
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKjet.L12` — the `L₁₂`-side of the jet package

Second half of the jet package of `L12_FK_jets_of_datum`: `∂_z L₁₂(F) = -L12dens(F)`
(`FM.hasDerivAt_L12`, whose continuity hypothesis comes from the angular-moment derivative of
`Qang F 0`), the bound `|L₁₂(F)(z)| ≤ C` from the `L¹`-control of the density, and the level one
angular moment differentiated under the `θ`-integral,
`∂_z Qang F 1 (z) = Qang F 2 z / z`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- `Work.Construction.L12dens F` is `Qang F 0` divided by the radial variable. -/
theorem lfj_FM_L12dens_eq (F : ℝ → ℝ → ℝ) :
    Work.FM.L12dens Work.Spaces.K F = fun s => Work.Elliptic.Qang F 0 s / s := by
  funext s
  rw [← Work.Elliptic.L12dens_eq_Qang_div F s]
  rfl

/-- Continuity of the `L₁₂`-density at `z`, from continuity of the level zero angular moment. -/
theorem lfj_L12dens_continuousAt {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hQ0 : ContinuousAt (Work.Elliptic.Qang F 0) z) (hz : 0 < z) :
    ContinuousAt (Work.Construction.L12dens F) z := by
  have hfun : Work.Construction.L12dens F = fun s => Work.Elliptic.Qang F 0 s / s :=
    lfj_FM_L12dens_eq F
  rw [hfun]
  exact hQ0.div continuousAt_id (ne_of_gt hz)

/-- **`∂_z L₁₂(F)(z) = -L12dens(F)(z)`.** -/
theorem lfj_L12_hasDerivAt {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hint : IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0))
    (hcont : ContinuousAt (Work.Construction.L12dens F) z) (hz : 0 < z) :
    HasDerivAt (fun z' => Work.Construction.L12 F z')
      (-(Work.Construction.L12dens F z)) z := by
  have hin : IntegrableOn (Work.FM.L12dens Work.Spaces.K F) (Set.Ioi 0) := hint
  have hc : ContinuousAt (Work.FM.L12dens Work.Spaces.K F) z := hcont
  simpa only [Work.Construction.L12, Work.Construction.L12dens] using
    Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := F) (a := 0) (ρ := z) hin hc (by linarith)

/-- **`|L₁₂(F)(z)| ≤ C`** from the `L¹`-control of the density. -/
theorem lfj_L12_abs_le {F : ℝ → ℝ → ℝ} {C z : ℝ}
    (hint : IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0))
    (hmass : (∫ s in Set.Ioi 0, |Work.Construction.L12dens F s|) ≤ C) (hz : 0 < z) :
    |Work.Construction.L12 F z| ≤ C := by
  have h1 : |∫ s in Set.Ioi z, Work.Construction.L12dens F s| ≤
      ∫ s in Set.Ioi z, |Work.Construction.L12dens F s| := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Set.Ioi z)) (f := fun s => Work.Construction.L12dens F s)
    simpa only [Real.norm_eq_abs] using h
  have h2 : (∫ s in Set.Ioi z, |Work.Construction.L12dens F s|) ≤
      ∫ s in Set.Ioi 0, |Work.Construction.L12dens F s| :=
    MeasureTheory.setIntegral_mono_set hint.abs
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Set.Ioi_subset_Ioi hz.le).eventuallySubset
  have h3 : Work.Construction.L12 F z
      = ∫ s in Set.Ioi z, Work.Construction.L12dens F s := rfl
  rw [h3]
  linarith [h1, h2, hmass]

/-- **`∂_z Qang F 1 (z) = Qang F 2 z / z`** (the level one angular moment, differentiated). -/
theorem lfj_Qang_one_hasDerivAt {F : ℝ → ℝ → ℝ} {C z : ℝ}
    (h2 : ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k F z θ| ≤ C)
    (hC : 0 ≤ C) (hz : 0 < z) :
    HasDerivAt (Work.Elliptic.Qang F 1) (Work.Elliptic.Qang F 2 z / z) z := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS_RegExport.RXT.Slots.isFiniteMeasure_restrict_Iθ
  have hz2 : 0 < z / 2 := by linarith
  have hVmem : z ∈ Set.Ioi (z / 2) := Set.mem_Ioi.mpr (by linarith)
  have hVpos : ∀ x ∈ Set.Ioi (z / 2), 0 < x := fun x hx => lt_trans hz2 (Set.mem_Ioi.mp hx)
  have hcd1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter 1 F))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin Work.FTS.EllipticEst.isOpen_Q0
      (n := 2) h2 1 (by norm_num)
  have hpz1 : ContDiffOn ℝ 0
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter 1 F))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin Work.FTS.EllipticEst.isOpen_Q0 (n := 0) hcd1
  have hKbd : ∀ θ : ℝ, |Work.Elliptic.Ktheta θ| ≤ 3 :=
    Work.FTS_RegExport.RXT.Slots.abs_Ktheta_le
  have hcg : ContinuousOn
      (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 F x θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter 1 F p.1 p.2)
      Work.FTS.EllipticEst.Q0 from lfj_continuousOn_Ktheta_jet.mul hcd1.continuousOn
  have hcg' : ContinuousOn
      (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ
        * Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ)) Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.pz (Work.Spaces.DzIter 1 F) p.1 p.2) Work.FTS.EllipticEst.Q0 from
      lfj_continuousOn_Ktheta_jet.mul hpz1.continuousOn
  have hint : Integrable (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 F z θ)
      (volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (3 * C))
      (Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 hcg hz) ?_
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hKbd θ) (hb 1 (by norm_num) z θ hz hθ.1 hθ.2) (abs_nonneg _) (by norm_num)
  have hpzbd : ∀ x ∈ Set.Ioi (z / 2), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ| ≤ 2 * C / z := by
    intro x hx θ hθ
    have hx0 : 0 < x := hVpos x hx
    have hxz : z / 2 < x := Set.mem_Ioi.mp hx
    have h := hb 2 (by norm_num) x θ hx0 hθ.1 hθ.2
    have heq : Work.Spaces.DzIter 2 F x θ
        = x * Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ := rfl
    rw [heq, abs_mul, abs_of_pos hx0] at h
    have hle : |Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ| ≤ C / x := by
      rw [le_div_iff₀ hx0]; rw [mul_comm]; exact h
    have h2' : C / x ≤ 2 * C / z := by
      have h3 : C / x ≤ C / (z / 2) := div_le_div_of_nonneg_left hC hz2 hxz.le
      have h4 : C / (z / 2) = 2 * C / z := by field_simp
      linarith [h3, le_of_eq h4]
    linarith
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ Set.Ioi (z / 2),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ‖
        ≤ 3 * (2 * C / z) := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h3 := hpzbd x hx θ hθ
    exact mul_le_mul (hKbd θ) h3 (abs_nonneg _) (by norm_num)
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioi (z / 2),
      HasDerivAt (fun y => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 F y θ)
        (Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ) x :=
    fun θ hθ x hx =>
      (lfj_slice_hasDerivAt hcd1 (hVpos x hx) hθ.1 hθ.2).const_mul _
  have key := Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0 (V := Set.Ioi (z / 2))
    isOpen_Ioi hVmem hVpos hcg hcg' hint hbound hdiff
  have hval : (∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 F) z θ)
      = Work.Elliptic.Qang F 2 z / z := by
    rw [lfj_Qang_succ_eq F 1 z, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  rw [hval] at key
  have hfun : Work.Elliptic.Qang F 1 = fun x => ∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 F x θ := rfl
  rw [hfun]
  exact key

end Work.FTS_RegExport.RXT.Sys
