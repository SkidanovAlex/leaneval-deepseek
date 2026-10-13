import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTraceO
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTracePth
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceThetaStep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg_Iθ_w {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Work.FTS.StrongEps.EpsSqTools.sin_two_nonneg_Iθ_eps hθ

/-- Pointwise identity: on `Iθ` the weighted `(0,0)`-slot is `w²` times the `η`-weighted square. -/
private lemma epsW_slot_eq {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h : ℝ) :
    (h * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
      = (Work.Spaces.w z)^2 * (h^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) := by
  have hs := sin_two_nonneg_Iθ_w hθ
  have hpow : ((Real.sin (2*θ))^(Work.Spaces.eta/2))^2 = (Real.sin (2*θ))^(Work.Spaces.eta) := by
    rw [Work.FTS.StrongEps.EpsSqTools.sin_rpow_sq hs]; congr 1; ring
  rw [mul_pow, div_pow, hpow, Real.rpow_neg hs]
  ring

theorem TraceWeightedL2 :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      ∃ lam : ℝ → ℝ,
        (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
            Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (lam z))) ∧
        (∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal ((lam z) ^ 2 * (Work.Spaces.w z) ^ 2))
          ≤ ENNReal.ofReal
              (C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 f) := by
  classical
  refine ⟨300, by norm_num, fun α hα f hso hm => ?_⟩
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα0
  have hγm : 0 < Work.Spaces.gam α - 1 := by linarith
  have hγle : Work.Spaces.gam α - 1 ≤ 1 := by rw [Work.Spaces.gam]; linarith
  -- the two slot functions and the `∂_θ`-energy
  let S : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2
  let T : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    (f z θ * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
  let A : ℝ → ℝ := fun z => ∫ σ in Work.Spaces.Iθ,
    (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2
  -- integrability of `S`, `T` and their bounds by `HkSq`
  have hprod01 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed hso hm 0 1
      (by norm_num) (by norm_num)
  have hSint : MeasureTheory.Integrable S (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hprod01.integral_prod_left
  have hSle : (∫ z in Work.Spaces.Iz, S z) ≤ Work.Spaces.HkSq α 6 f := by
    have h := Work.Spaces.L2Sq_mixed_le_HkSq α 6 f hm 1 0 (by norm_num) (by norm_num)
    rw [Work.Spaces.L2Sq] at h
    exact h
  have hprod0 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter 0 f z θ
        * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_z hso hm 0 (by norm_num)
  have hTint : MeasureTheory.Integrable T (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h : MeasureTheory.Integrable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 f z θ
          * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hprod0.integral_prod_left
    simpa only [Work.Spaces.DzIter_zero] using h
  have hTle : (∫ z in Work.Spaces.Iz, T z) ≤ Work.Spaces.HkSq α 6 f := by
    have h := Work.Spaces.L2Sq_DzIter_le_HkSq α 6 f hm 0 (by norm_num)
    rw [Work.Spaces.L2Sq] at h
    simpa only [Work.Spaces.DzIter_zero] using h
  have hHknn : 0 ≤ Work.Spaces.HkSq α 6 f := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z _ => ?_)
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
  have hSnn : ∀ z : ℝ, 0 ≤ S z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hTnn : ∀ z : ℝ, 0 ≤ T z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hAnn : ∀ z : ℝ, 0 ≤ A z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun σ hσ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ_w hσ) _) (sq_nonneg _))
  -- the choice predicate and the trace
  let Q : ℝ → Prop := fun z => ∃ mu : ℝ,
    Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds mu) ∧
      ∀ θ ∈ Set.Ioo 0 (π/4),
        (f z θ - mu)^2 ≤ 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
          * A z
  let lam : ℝ → ℝ := fun z => if h : Q z then Classical.choose h else 0
  -- the `(0,1)`-slot is `θ`-integrable for almost every `z`
  have hslot01ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable
        (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hprod01.prod_right_ae
  -- the trace exists for almost every `z`
  have hQae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), Q z := by
    filter_upwards [hslot01ae, Work.FTS.StrongEps.EpsSqTools.ae_pos_Iz] with z hslot hz
    exact SliceTracePth hα hz hso hslot
  -- the `θ`-integrability of the unweighted `(0,0)`-slot integrand, for every `z ∈ Iz`
  have hzint0 : ∀ z : ℝ, 0 < z → MeasureTheory.Integrable
      (fun θ => (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have hsum := Work.FTS.EllipticEst.integrableOn_zSummand α 6 hso hm 0 (by norm_num)
      (z := z) (le_of_lt hz)
    have hw : ((Work.Spaces.w z)^2) ≠ 0 := by
      have h1 : (0:ℝ) < (1+z)^2 := by positivity
      have h2 : (0:ℝ) < z^2 := by positivity
      rw [Work.Spaces.w]; exact pow_ne_zero 2 (div_ne_zero (ne_of_gt h1) (ne_of_gt h2))
    refine (hsum.const_mul (((Work.Spaces.w z)^2)⁻¹)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ hθ => ?_)
    show ((Work.Spaces.w z)^2)⁻¹
        * (f z θ * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
      = (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
    have h1 : (f z θ * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
        = (Work.Spaces.w z)^2 * ((f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) :=
      epsW_slot_eq hθ (f z θ)
    rw [h1, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]
  -- the pointwise bound on `lam`
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (lam z)^2 * (Work.Spaces.w z)^2
        ≤ (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z := by
    filter_upwards [hQae, Work.FTS.StrongEps.EpsSqTools.ae_pos_Iz] with z hQ hz
    have hlam : lam z = Classical.choose hQ := dif_pos hQ
    have hspec := Classical.choose_spec hQ
    -- the trace step, with the energy `A z`
    have hstep : (lam z)^2 ≤ 200/(Work.Spaces.gam α - 1) * A z
        + 8/Real.pi * (∫ θ in Work.Spaces.Iθ,
            (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) := by
      refine TraceThetaStep (γ := Work.Spaces.gam α) (m := lam z) (A := A z) hγ1 (hAnn z)
        (hzint0 z hz) (fun θ hθ => ?_)
      rw [hlam]
      exact hspec.2 θ hθ
    -- multiply by `w²`
    have hmul := mul_le_mul_of_nonneg_right hstep (sq_nonneg (Work.Spaces.w z))
    -- the two identities converting `A z · w²` and `w² · ∫ f²` into the slots
    have hAeq : A z * (Work.Spaces.w z)^2 = S z := by
      rw [mul_comm]
      exact (Work.FTS.StrongEps.EpsSqTools.slot_slice_eq hα0 hα1 f).symm
    have hYeq : (Work.Spaces.w z)^2 * (∫ θ in Work.Spaces.Iθ,
          (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) = T z := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ hθ => ?_)
      exact (epsW_slot_eq hθ (f z θ)).symm
    calc (lam z)^2 * (Work.Spaces.w z)^2
        ≤ (200/(Work.Spaces.gam α - 1) * A z
            + 8/Real.pi * (∫ θ in Work.Spaces.Iθ,
                (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)))
          * (Work.Spaces.w z)^2 := hmul
      _ = (200/(Work.Spaces.gam α - 1)) * (A z * (Work.Spaces.w z)^2)
            + (8/Real.pi) * ((Work.Spaces.w z)^2 * (∫ θ in Work.Spaces.Iθ,
                (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta))) := by ring
      _ = (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z := by
          rw [hAeq, hYeq]
  -- the majorant is integrable and its integral is bounded by `HkSq`
  have hmaj : MeasureTheory.Integrable
      (fun z : ℝ => (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hSint.const_mul _).add (hTint.const_mul _)
  have hmajnn : (0 : ℝ → ℝ) ≤ fun z : ℝ =>
      (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z := fun z =>
    add_nonneg (mul_nonneg (by positivity) (hSnn z)) (mul_nonneg (by positivity) (hTnn z))
  have hcoef : 8/Real.pi ≤ 100/(Work.Spaces.gam α - 1) := by
    rw [div_le_div_iff₀ (by positivity) hγm]
    nlinarith [Real.pi_gt_three, hγle]
  have hcomb : (∫ z in Work.Spaces.Iz,
        ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z))
      ≤ 300/(Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 f := by
    have h1 := mul_le_mul_of_nonneg_left hSle (by positivity : (0:ℝ) ≤ 200/(Work.Spaces.gam α - 1))
    have h2 := mul_le_mul_of_nonneg_left hTle (by positivity : (0:ℝ) ≤ 8/Real.pi)
    rw [MeasureTheory.integral_add (hSint.const_mul _) (hTint.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    calc (200/(Work.Spaces.gam α - 1)) * (∫ z in Work.Spaces.Iz, S z)
          + 8/Real.pi * (∫ z in Work.Spaces.Iz, T z)
        ≤ (200/(Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 6 f
          + 8/Real.pi * Work.Spaces.HkSq α 6 f := by linarith
      _ = (200/(Work.Spaces.gam α - 1) + 8/Real.pi) * Work.Spaces.HkSq α 6 f := by ring
      _ ≤ (300/(Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 6 f := by
          refine mul_le_mul_of_nonneg_right ?_ hHknn
          have hsum : (200:ℝ)/(Work.Spaces.gam α - 1)
              + 100/(Work.Spaces.gam α - 1) = 300/(Work.Spaces.gam α - 1) := by ring
          linarith [hcoef]
  -- the `z`-integral
  have hlinz : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((lam z)^2 * (Work.Spaces.w z)^2))
      ≤ ENNReal.ofReal (300/(Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 f) := by
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal hcomb)
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((lam z)^2 * (Work.Spaces.w z)^2))
        ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
            ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z) :=
          MeasureTheory.lintegral_mono_ae
            (hpoint.mono (fun z hz => ENNReal.ofReal_le_ofReal hz))
      _ = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
            ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmaj
            (Filter.Eventually.of_forall hmajnn)).symm
  -- the measure `volume` restricted to `(0,∞)` and to `Iz = [0,∞)` agree
  have hIz : (MeasureTheory.volume : Measure (ℝ)).restrict (Set.Ioi (0:ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.restrict_Ioi_eq_restrict_Ici
  refine ⟨lam, ?_, ?_⟩
  · rw [hIz]
    filter_upwards [hQae] with z hQ
    rw [show lam z = Classical.choose hQ from dif_pos hQ]
    exact (Classical.choose_spec hQ).1
  · rw [hIz]
    exact hlinz

end Work.FTS.StrongEps.EpsLocalPStar
