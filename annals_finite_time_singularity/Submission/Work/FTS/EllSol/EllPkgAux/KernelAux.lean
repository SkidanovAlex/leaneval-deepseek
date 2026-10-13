/-
# `Work.FTS.EllSol.EllPkgAux.KernelAux` — the analytic auxiliary lemmas for `kernelJensen`

On top of `KernelDefs` (the kernel `KJ` and its elementary bounds) this module proves:

* `restrict_Iθ_eq_restrict_Ioo`, `thEta_pos_of_mem_Ioo`, `one_le_thEta_of_mem_Ioo` : the angular
  weight `σθ = thEta` is positive and at least `1` on the open interval;
* `integrable_of_le` : domination criterion for integrability via the Lebesgue integral;
* `aesm_sq_of_integrableOn`, `integrableOn_sq_of_integrableOn` : the single hypothesis
  `IntegrableOn (g² σθ) Iθ` of the target controls `g²` itself;
* `KJ_pointwise` : the pointwise Cauchy–Schwarz/Jensen bound
  `(∫_{Iθ} KJ ε θ s · g s)² ≤ 3 ∫_{Iθ} KJ ε θ s · (g s)²`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs

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
set_option maxHeartbeats 1000000

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

theorem restrict_Iθ_eq_restrict_Ioo :
    volume.restrict Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  refine MeasureTheory.Measure.restrict_congr_set ?_
  show Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2)
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

theorem thEta_pos_of_mem_Ioo {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < σθ s := by
  have h : 0 < Real.sin (2 * s) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2, Real.pi_pos])
  simpa only [Work.FTS.EllipticEst.thEta] using
    Real.rpow_pos_of_pos h (-(Work.Spaces.eta))

theorem one_le_thEta_of_mem_Ioo {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ σθ s := by
  have hpos : 0 < Real.sin (2 * s) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2, Real.pi_pos])
  have hle : Real.sin (2 * s) ≤ 1 := Real.sin_le_one _
  have hne : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  simpa only [Work.FTS.EllipticEst.thEta] using
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle hne

/-- **Domination criterion.**  A nonnegative a.e.-strongly-measurable function dominated a.e. by an
integrable nonnegative function is integrable.  (This is `Integrable.mono'` routed through the
Lebesgue integral, which avoids the expensive second-order unification of `mono'`.) -/
theorem integrable_of_le {f h : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict Iθ))
    (hfnn : 0 ≤ᵐ[volume.restrict Iθ] f) (hh : Integrable h (volume.restrict Iθ))
    (hh0 : 0 ≤ᵐ[volume.restrict Iθ] h) (hle : f ≤ᵐ[volume.restrict Iθ] h) :
    Integrable f (volume.restrict Iθ) := by
  refine ⟨hf, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hfnn]
  calc ∫⁻ s in Iθ, ENNReal.ofReal (f s)
      ≤ ∫⁻ s in Iθ, ENNReal.ofReal (h s) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [hle] with s hs
        exact ENNReal.ofReal_le_ofReal hs
    _ = ENNReal.ofReal (∫ s in Iθ, h s) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hh hh0).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem ae_le_of_forall_mem_Ioo {f h' : ℝ → ℝ}
    (hh : ∀ s ∈ Set.Ioo 0 (Real.pi / 2), f s ≤ h' s) : f ≤ᵐ[volume.restrict Iθ] h' := by
  have hμ : volume.restrict Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    restrict_Iθ_eq_restrict_Ioo
  rw [hμ]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hh

theorem aesm_sq_of_integrableOn {g : ℝ → ℝ}
    (hg : IntegrableOn (fun s : ℝ => g s ^ 2 * σθ s) Iθ) :
    AEStronglyMeasurable (fun s : ℝ => g s ^ 2) (volume.restrict Iθ) := by
  have haeth : AEMeasurable σθ (volume.restrict Iθ) :=
    (Work.FTS.EllipticEst.integrableOn_thEta.1).aemeasurable
  have hinv : AEMeasurable (fun s : ℝ => (σθ s)⁻¹) (volume.restrict Iθ) := haeth.inv
  have hne : ∀ᵐ s ∂(volume.restrict Iθ), σθ s ≠ 0 := by
    have h1 : ∀ᵐ s ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))), σθ s ≠ 0 :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun s hs => ne_of_gt (thEta_pos_of_mem_Ioo hs))
    have hμ : volume.restrict Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
      restrict_Iθ_eq_restrict_Ioo
    rw [hμ]
    exact h1
  have hcongr : (fun s : ℝ => g s ^ 2)
      =ᵐ[volume.restrict Iθ] (fun s : ℝ => (g s ^ 2 * σθ s) * (σθ s)⁻¹) := by
    filter_upwards [hne] with s hs
    rw [mul_assoc, mul_inv_cancel₀ hs, mul_one]
  exact ((hg.1.aemeasurable.mul hinv).congr hcongr.symm).aestronglyMeasurable

theorem integrableOn_sq_of_integrableOn {g : ℝ → ℝ}
    (hg : IntegrableOn (fun s : ℝ => g s ^ 2 * σθ s) Iθ) :
    IntegrableOn (fun s : ℝ => g s ^ 2) Iθ := by
  refine integrable_of_le (aesm_sq_of_integrableOn hg)
    (Filter.Eventually.of_forall (fun s => sq_nonneg (g s))) hg ?_ ?_
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun s hs => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs))
  · refine ae_le_of_forall_mem_Ioo (fun s hs => ?_)
    exact le_mul_of_one_le_right (sq_nonneg (g s)) (one_le_thEta_of_mem_Ioo hs)

theorem KJ_pointwise {g : ℝ → ℝ} {ε θ : ℝ} (hε : 0 < ε)
    (hg : IntegrableOn (fun s : ℝ => g s ^ 2 * σθ s) Iθ) (hθ : θ ∈ Iθ) :
    (∫ s in Iθ, KJ ε θ s * g s) ^ 2 ≤ 3 * ∫ s in Iθ, KJ ε θ s * g s ^ 2 := by
  have hg2aesm := aesm_sq_of_integrableOn hg
  have hGsm : AEStronglyMeasurable (fun s : ℝ => Real.sqrt (g s ^ 2)) (volume.restrict Iθ) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg2aesm
  have hG2 : ∀ s : ℝ, Real.sqrt (g s ^ 2) ^ 2 = g s ^ 2 := fun s =>
    Real.sq_sqrt (sq_nonneg (g s))
  have hGabs : ∀ s : ℝ, Real.sqrt (g s ^ 2) = |g s| := fun s => Real.sqrt_sq_eq_abs (g s)
  have hKJint : IntegrableOn (fun s : ℝ => KJ ε θ s) Iθ := by
    have hc : Continuous (fun t : ℝ => sKer ε t) := Work.FTS.EllSol.K5cAux.continuous_sKer ε
    have h1 : Continuous (fun s : ℝ => sKer ε (θ - s)) :=
      hc.comp (continuous_const.sub continuous_id)
    have h2 : Continuous (fun s : ℝ => sKer ε (θ + s)) :=
      hc.comp (continuous_const.add continuous_id)
    have h3 : Continuous (fun s : ℝ => sKer ε (θ + s - Real.pi)) :=
      hc.comp ((continuous_const.add continuous_id).sub continuous_const)
    have hcont : Continuous (fun s : ℝ => KJ ε θ s) := by
      simp only [KJ]
      exact (h1.add h2).add h3
    have h := hcont.integrableOn_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)
    simpa only [Work.Spaces.Iθ] using h
  have hKJsm : AEStronglyMeasurable (fun s : ℝ => KJ ε θ s) (volume.restrict Iθ) := hKJint.1
  have hKg2 : IntegrableOn (fun s : ℝ => KJ ε θ s * g s ^ 2) Iθ := by
    have hc : (0:ℝ) ≤ 3 * (ε * sMass)⁻¹ :=
      mul_nonneg (by norm_num) (inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le))
    refine integrable_of_le (hKJsm.mul hg2aesm)
      (Filter.Eventually.of_forall (fun s => mul_nonneg (KJ_nonneg hε θ s) (sq_nonneg (g s))))
      ((hg.const_mul (3 * (ε * sMass)⁻¹))) ?_ ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s hs =>
        mul_nonneg hc (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs)))
    · refine ae_le_of_forall_mem_Ioo (fun s hs => ?_)
      have h1 : KJ ε θ s ≤ 3 * (ε * sMass)⁻¹ := KJ_le hε θ s
      have h2 : 1 ≤ σθ s := one_le_thEta_of_mem_Ioo hs
      have h3 : 0 ≤ g s ^ 2 := sq_nonneg _
      calc KJ ε θ s * g s ^ 2 ≤ (3 * (ε * sMass)⁻¹) * g s ^ 2 :=
            mul_le_mul_of_nonneg_right h1 h3
        _ ≤ (3 * (ε * sMass)⁻¹) * (g s ^ 2 * σθ s) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_right h3 h2) hc
  have hKJGs : IntegrableOn (fun s : ℝ => KJ ε θ s * Real.sqrt (g s ^ 2) ^ 2) Iθ :=
    MeasureTheory.Integrable.congr hKg2
      (Filter.Eventually.of_forall (fun s => by
        show KJ ε θ s * g s ^ 2 = KJ ε θ s * Real.sqrt (g s ^ 2) ^ 2
        rw [hG2 s]))
  have hstep1 : |∫ s in Iθ, KJ ε θ s * g s|
      ≤ ∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2) := by
    have h1 := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict Iθ) (fun s : ℝ => KJ ε θ s * g s)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans (le_of_eq ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    show ‖KJ ε θ s * g s‖ = KJ ε θ s * Real.sqrt (g s ^ 2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (KJ_nonneg hε θ s), hGabs]
  have hu_mem : MemLp (fun s : ℝ => Real.sqrt (KJ ε θ s)) 2 (volume.restrict Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (f := fun s : ℝ => Real.sqrt (KJ ε θ s))
      (Real.continuous_sqrt.comp_aestronglyMeasurable hKJsm)).mpr
      (MeasureTheory.Integrable.congr hKJint (Filter.Eventually.of_forall (fun s => by
        show KJ ε θ s = Real.sqrt (KJ ε θ s) ^ 2
        rw [Real.sq_sqrt (KJ_nonneg hε θ s)])))
  have hG_mem : MemLp (fun s : ℝ => Real.sqrt (g s ^ 2)) 2 (volume.restrict Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (f := fun s : ℝ => Real.sqrt (g s ^ 2))
      hGsm).mpr
      (MeasureTheory.Integrable.congr (integrableOn_sq_of_integrableOn hg)
        (Filter.Eventually.of_forall (fun s => by
          show g s ^ 2 = Real.sqrt (g s ^ 2) ^ 2
          rw [Real.sq_sqrt (sq_nonneg (g s))])))
  have hv_mem : MemLp (fun s : ℝ => Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)) 2
      (volume.restrict Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      (f := fun s : ℝ => Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2))
      ((Real.continuous_sqrt.comp_aestronglyMeasurable hKJsm).mul hGsm)).mpr
      (MeasureTheory.Integrable.congr hKg2 (Filter.Eventually.of_forall (fun s => by
        show KJ ε θ s * g s ^ 2 = (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)) ^ 2
        rw [mul_pow, Real.sq_sqrt (KJ_nonneg hε θ s), Real.sq_sqrt (sq_nonneg (g s))])))
  have hcs : (∫ s in Iθ, Real.sqrt (KJ ε θ s) * (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2))) ^ 2
      ≤ (∫ s in Iθ, Real.sqrt (KJ ε θ s) ^ 2)
        * (∫ s in Iθ, (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)) ^ 2) :=
    Work.Spaces.cs_integral (s := Iθ) hu_mem hv_mem
  have e1 : (∫ s in Iθ, Real.sqrt (KJ ε θ s) * (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)))
      = ∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => by
      show Real.sqrt (KJ ε θ s) * (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2))
        = KJ ε θ s * Real.sqrt (g s ^ 2)
      rw [← mul_assoc, ← sq, Real.sq_sqrt (KJ_nonneg hε θ s)]))
  have e2 : (∫ s in Iθ, Real.sqrt (KJ ε θ s) ^ 2) = ∫ s in Iθ, KJ ε θ s :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => by
      show Real.sqrt (KJ ε θ s) ^ 2 = KJ ε θ s
      rw [Real.sq_sqrt (KJ_nonneg hε θ s)]))
  have e3 : (∫ s in Iθ, (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)) ^ 2)
      = ∫ s in Iθ, KJ ε θ s * g s ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => by
      show (Real.sqrt (KJ ε θ s) * Real.sqrt (g s ^ 2)) ^ 2 = KJ ε θ s * g s ^ 2
      rw [mul_pow, Real.sq_sqrt (KJ_nonneg hε θ s), Real.sq_sqrt (sq_nonneg (g s))]))
  rw [e1, e2, e3] at hcs
  have hQnn : 0 ≤ ∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2) :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun s =>
        mul_nonneg (KJ_nonneg hε θ s) (Real.sqrt_nonneg _)))
  have hPnn : 0 ≤ (∫ s in Iθ, KJ ε θ s * g s ^ 2) :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun s =>
        mul_nonneg (KJ_nonneg hε θ s) (sq_nonneg _)))
  have hmass : (∫ s in Iθ, KJ ε θ s) ≤ 3 := KJ_mass hε hθ
  have hArith : (∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2)) ^ 2
      ≤ 3 * (∫ s in Iθ, KJ ε θ s * g s ^ 2) := by
    have h3 : (∫ s in Iθ, KJ ε θ s) * (∫ s in Iθ, KJ ε θ s * g s ^ 2)
        ≤ 3 * (∫ s in Iθ, KJ ε θ s * g s ^ 2) := by
      have h4 := mul_le_mul_of_nonneg_right hmass hPnn
      linarith
    linarith [hcs, h3]
  have hstep2 : (∫ s in Iθ, KJ ε θ s * g s) ^ 2
      ≤ (∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2)) ^ 2 := by
    have h := abs_le.mp hstep1
    have h1 : 0 ≤ (∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
        + (∫ s in Iθ, KJ ε θ s * g s) := by linarith [h.1]
    have h2 : 0 ≤ (∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
        - (∫ s in Iθ, KJ ε θ s * g s) := by linarith [h.2]
    have h3 : 0 ≤ ((∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
          - (∫ s in Iθ, KJ ε θ s * g s))
        * ((∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
          + (∫ s in Iθ, KJ ε θ s * g s)) :=
      mul_nonneg h2 h1
    have h4 : ((∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
          - (∫ s in Iθ, KJ ε θ s * g s))
        * ((∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2))
          + (∫ s in Iθ, KJ ε θ s * g s))
        = (∫ s in Iθ, KJ ε θ s * Real.sqrt (g s ^ 2)) ^ 2
          - (∫ s in Iθ, KJ ε θ s * g s) ^ 2 := by ring_nf
    linarith [h3, h4]
  linarith [hstep2, hArith]

end Work.FTS.EllSol.EllPkgAux
