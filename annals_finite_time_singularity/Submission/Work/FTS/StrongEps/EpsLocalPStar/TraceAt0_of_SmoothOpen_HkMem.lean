import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTracePth
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceThetaStep
import Submission.Work.FTS.StrongEps.EpsLocalPStar.aemeasurable_traceSeq
import Submission.Work.FTS.StrongEps.EpsLocalPStar.inv_zw_sq_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary helpers -/

private lemma sin_two_nonneg_Iθ_s {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Work.FTS.StrongEps.EpsSqTools.sin_two_nonneg_Iθ_eps hθ

/-- Pointwise identity: on `Iθ` the weighted `(0,0)`-slot is `w²` times the `η`-weighted square. -/
private lemma zSlot_sq_eq {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h : ℝ) :
    (h * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
      = (Work.Spaces.w z)^2 * (h^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) := by
  have hs := sin_two_nonneg_Iθ_s hθ
  have hpow : ((Real.sin (2*θ))^(Work.Spaces.eta/2))^2 = (Real.sin (2*θ))^(Work.Spaces.eta) := by
    rw [Work.FTS.StrongEps.EpsSqTools.sin_rpow_sq hs]; congr 1; ring
  rw [mul_pow, div_pow, hpow, Real.rpow_neg hs]
  ring

/-- The angular sampling sequence `θ_n = 1/(n+2)`, converging to `0⁺`. -/
private noncomputable def trs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)

private lemma trs_pos (n : ℕ) : 0 < trs n := by
  change 0 < (1:ℝ) / ((n : ℝ) + 2)
  positivity

private lemma tendsto_trs : Tendsto trs atTop (𝓝[>] (0:ℝ)) := by
  have h0 : Tendsto trs atTop (𝓝 (0:ℝ)) := by
    have htop : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    change Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 2)) atTop (𝓝 (0:ℝ))
    simpa [one_div] using htop.const_div_atTop (1:ℝ)
  rw [tendsto_nhdsWithin_iff]
  exact ⟨h0, Filter.Eventually.of_forall trs_pos⟩

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
private lemma sqrt_add_le_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h2 : 0 ≤ Real.sqrt a + Real.sqrt b := add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b)^2 := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  rw [← Real.sqrt_sq h2]
  exact Real.sqrt_le_sqrt h

/-- The AM–GM inequality `x·√s ≤ (x²+s)/2` for `x, s ≥ 0`. -/
private lemma mul_sqrt_le {x s : ℝ} (_hx : 0 ≤ x) (hs : 0 ≤ s) :
    x * Real.sqrt s ≤ (x^2 + s)/2 := by
  nlinarith [sq_nonneg (x - Real.sqrt s), Real.sq_sqrt hs, Real.sqrt_nonneg s]

/-- If the slice has a trace `mu` at `0⁺`, the sampled sequence converges to `mu`. -/
private lemma limUnder_trs_eq {f : ℝ → ℝ → ℝ} {z mu : ℝ}
    (h : Tendsto (fun θ => f z θ) (𝓝[>] (0:ℝ)) (𝓝 mu)) :
    limUnder atTop (fun n : ℕ => f z (trs n)) = mu :=
  (h.comp tendsto_trs).limUnder_eq

set_option maxHeartbeats 1600000 in
theorem TraceAt0_of_SmoothOpen_HkMem {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f) :
    ∃ lam : ℝ → ℝ, Measurable lam ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (lam z))) ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), ∀ θ ∈ Set.Ioo 0 (Real.pi/4),
        (f z θ - lam z)^2
          ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
            * (∫ σ in Work.Spaces.Iθ,
                (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2)) ∧
      MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)) := by
  classical
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα0
  have hγm : 0 < Work.Spaces.gam α - 1 := by linarith
  -- the three slot functions
  let S : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2
  let T : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    (f z θ * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
  let A : ℝ → ℝ := fun z => ∫ σ in Work.Spaces.Iθ,
    (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2
  have hAnn : ∀ z : ℝ, 0 ≤ A z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun σ hσ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ_s hσ) _) (sq_nonneg _))
  have hSnn : ∀ z : ℝ, 0 ≤ S z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hTnn : ∀ z : ℝ, 0 ≤ T z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  -- product integrability of the two slots
  have hprod01 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ =>
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed hso hm 0 1
      (by norm_num) (by norm_num)
  have hprod0 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter 0 f z θ
        * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_z hso hm 0 (by norm_num)
  have hSintIz : MeasureTheory.Integrable S (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hprod01.integral_prod_left
  have hTintIz : MeasureTheory.Integrable T (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h : MeasureTheory.Integrable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 f z θ
          * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hprod0.integral_prod_left
    simpa only [Work.Spaces.DzIter_zero] using h
  -- a.e. slot integrability in `θ`
  have hslot01ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable
        (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hprod01.prod_right_ae
  -- the trace exists for almost every `z`
  have hQaeIz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∃ mu : ℝ, Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds mu) ∧
        ∀ θ ∈ Set.Ioo 0 (π/4),
          (f z θ - mu)^2 ≤ 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
            * A z := by
    filter_upwards [hslot01ae, Work.FTS.StrongEps.EpsSqTools.ae_pos_Iz] with z hslot hz
    exact SliceTracePth hα hz hso hslot
  -- the two measures agree
  have hIz : (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.restrict_Ioi_eq_restrict_Ici
  have hQae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ∃ mu : ℝ, Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds mu) ∧
        ∀ θ ∈ Set.Ioo 0 (π/4),
          (f z θ - mu)^2 ≤ 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
            * A z := by
    rw [hIz]; exact hQaeIz
  -- the measurable trace
  have hAe : AEMeasurable
      (fun z : ℝ => limUnder atTop (fun n : ℕ => f z (trs n)))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := aemeasurable_traceSeq hso
  set lam : ℝ → ℝ := hAe.mk (fun z : ℝ => limUnder atTop (fun n : ℕ => f z (trs n))) with hlamdef
  have hlammeas : Measurable lam := hAe.measurable_mk
  have hlamae : (fun z : ℝ => limUnder atTop (fun n : ℕ => f z (trs n)))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))] lam := hAe.ae_eq_mk
  -- the a.e. trace and the a.e. rate
  have htr : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (lam z)) := by
    filter_upwards [hQae, hlamae] with z hQ hzeq
    obtain ⟨mu, hmu, -⟩ := hQ
    rw [← hzeq, limUnder_trs_eq hmu]
    exact hmu
  have hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), ∀ θ ∈ Set.Ioo 0 (π/4),
      (f z θ - lam z)^2
        ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
          * (∫ σ in Work.Spaces.Iθ,
              (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2) := by
    filter_upwards [hQae, hlamae] with z hQ hzeq
    obtain ⟨mu, hmu, hb⟩ := hQ
    have heq : lam z = mu := by rw [← hzeq, limUnder_trs_eq hmu]
    rw [heq]
    exact hb
  -- the pointwise `L²` bound on the trace
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      (lam z)^2 * (Work.Spaces.w z)^2
        ≤ (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z := by
    filter_upwards [hQae, hlamae, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with z hQ hzeq hzmem
    have hz : 0 < z := hzmem
    obtain ⟨mu, hmu, hb⟩ := hQ
    have heq : lam z = mu := by rw [← hzeq, limUnder_trs_eq hmu]
    -- integrability of `θ ↦ f² sin^{-η}`
    have hzint0 : MeasureTheory.Integrable
        (fun θ => (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hsum := Work.FTS.EllipticEst.integrableOn_zSummand α 1 hso hm 0 (by norm_num)
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
        zSlot_sq_eq hθ (f z θ)
      rw [h1, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]
    have hstep := TraceThetaStep (γ := Work.Spaces.gam α) (m := lam z) (A := A z) (u := fun θ => f z θ)
      hγ1 (hAnn z) hzint0 (fun θ hθ => by rw [heq]; exact hb θ hθ)
    have hmul := mul_le_mul_of_nonneg_right hstep (sq_nonneg (Work.Spaces.w z))
    have hAeq : A z * (Work.Spaces.w z)^2 = S z := by
      rw [mul_comm]
      exact (Work.FTS.StrongEps.EpsSqTools.slot_slice_eq hα0 hα1 f).symm
    have hYeq : (Work.Spaces.w z)^2 * (∫ θ in Work.Spaces.Iθ,
          (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) = T z := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ hθ => ?_)
      exact (zSlot_sq_eq hθ (f z θ)).symm
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
  -- the pointwise bound on `|λ z|/z`
  set Cst : ℝ := max (Real.sqrt (200/(Work.Spaces.gam α - 1))) (Real.sqrt (8/Real.pi)) with hCstdef
  have hCstnn : 0 ≤ Cst := le_max_of_le_left (Real.sqrt_nonneg _)
  have hmain : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ‖lam z / z‖ ≤ (Cst/2) * (S z + T z + 2 * (1/(z * Work.Spaces.w z))^2) := by
    filter_upwards [hpoint, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hp hzmem
    have hz : 0 < z := hzmem
    have hw : 0 < Work.Spaces.w z := by
      rw [Work.Spaces.w]; positivity
    have hS0 : 0 ≤ S z := hSnn z
    have hT0 : 0 ≤ T z := hTnn z
    have hcoef1 : 0 ≤ 200/(Work.Spaces.gam α - 1) := by positivity
    have hcoef2 : 0 ≤ 8/Real.pi := by positivity
    have hPnn : 0 ≤ (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z :=
      add_nonneg (mul_nonneg hcoef1 hS0) (mul_nonneg hcoef2 hT0)
    -- `|λ z| ≤ √P / w`
    have hsq : (lam z)^2 ≤ ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
        / (Work.Spaces.w z)^2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hp]
    have habs : |lam z| ≤ Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
        / Work.Spaces.w z := by
      rw [le_div_iff₀ hw]
      have h1 : |lam z| * Work.Spaces.w z
          = Real.sqrt ((lam z)^2 * (Work.Spaces.w z)^2) := by
        rw [Real.sqrt_mul (sq_nonneg (lam z)), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
          abs_of_pos hw]
      rw [h1]
      exact Real.sqrt_le_sqrt hp
    -- `√P ≤ Cst (√S + √T)`
    have hsqrtP : Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
        ≤ Cst * (Real.sqrt (S z) + Real.sqrt (T z)) := by
      have h1 : Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
          ≤ Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z)
            + Real.sqrt ((8/Real.pi) * T z) :=
        sqrt_add_le_sqrt (mul_nonneg hcoef1 hS0) (mul_nonneg hcoef2 hT0)
      have h2 : Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z)
          = Real.sqrt (200/(Work.Spaces.gam α - 1)) * Real.sqrt (S z) :=
        Real.sqrt_mul hcoef1 _
      have h3 : Real.sqrt ((8/Real.pi) * T z)
          = Real.sqrt (8/Real.pi) * Real.sqrt (T z) := Real.sqrt_mul hcoef2 _
      have h4 : Real.sqrt (200/(Work.Spaces.gam α - 1)) * Real.sqrt (S z)
          ≤ Cst * Real.sqrt (S z) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      have h5 : Real.sqrt (8/Real.pi) * Real.sqrt (T z) ≤ Cst * Real.sqrt (T z) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
      calc Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
          ≤ Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z)
            + Real.sqrt ((8/Real.pi) * T z) := h1
        _ = Real.sqrt (200/(Work.Spaces.gam α - 1)) * Real.sqrt (S z)
            + Real.sqrt (8/Real.pi) * Real.sqrt (T z) := by rw [h2, h3]
        _ ≤ Cst * Real.sqrt (S z) + Cst * Real.sqrt (T z) := add_le_add h4 h5
        _ = Cst * (Real.sqrt (S z) + Real.sqrt (T z)) := by ring
    -- assemble
    have hx : 0 ≤ 1/(z * Work.Spaces.w z) := by positivity
    have hstep1 : |lam z| / z ≤ Cst * ((1/(z * Work.Spaces.w z))
        * (Real.sqrt (S z) + Real.sqrt (T z))) := by
      have hz1 : (0:ℝ) < z := hz
      have h0 : |lam z| / z ≤ (Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z
          + (8/Real.pi) * T z) / Work.Spaces.w z) / z := by
        exact div_le_div_of_nonneg_right habs (le_of_lt hz1)
      have h1 : (Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
            / Work.Spaces.w z) / z
          = (1/(z * Work.Spaces.w z))
            * Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z) := by
        field_simp
      rw [h1] at h0
      calc |lam z| / z
          ≤ (1/(z * Work.Spaces.w z))
            * Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z) := h0
        _ ≤ (1/(z * Work.Spaces.w z)) * (Cst * (Real.sqrt (S z) + Real.sqrt (T z))) :=
            mul_le_mul_of_nonneg_left hsqrtP hx
        _ = Cst * ((1/(z * Work.Spaces.w z)) * (Real.sqrt (S z) + Real.sqrt (T z))) := by ring
    have hstep2 : Cst * ((1/(z * Work.Spaces.w z)) * (Real.sqrt (S z) + Real.sqrt (T z)))
        ≤ (Cst/2) * (S z + T z + 2 * (1/(z * Work.Spaces.w z))^2) := by
      have h1 : (1/(z * Work.Spaces.w z)) * Real.sqrt (S z)
          ≤ ((1/(z * Work.Spaces.w z))^2 + S z)/2 := mul_sqrt_le hx hS0
      have h2 : (1/(z * Work.Spaces.w z)) * Real.sqrt (T z)
          ≤ ((1/(z * Work.Spaces.w z))^2 + T z)/2 := mul_sqrt_le hx hT0
      have h3 : (1/(z * Work.Spaces.w z)) * (Real.sqrt (S z) + Real.sqrt (T z))
          ≤ ((1/(z * Work.Spaces.w z))^2 + S z)/2 + ((1/(z * Work.Spaces.w z))^2 + T z)/2 := by
        rw [mul_add]; linarith
      calc Cst * ((1/(z * Work.Spaces.w z)) * (Real.sqrt (S z) + Real.sqrt (T z)))
          ≤ Cst * (((1/(z * Work.Spaces.w z))^2 + S z)/2
              + ((1/(z * Work.Spaces.w z))^2 + T z)/2) :=
            mul_le_mul_of_nonneg_left h3 hCstnn
        _ = (Cst/2) * (S z + T z + 2 * (1/(z * Work.Spaces.w z))^2) := by ring
    have hnorm : ‖lam z / z‖ = |lam z| / z := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hz]
    rw [hnorm]
    exact hstep1.trans hstep2
  -- integrability of the majorant
  have hIoiIz : Set.Ioi (0:ℝ) ⊆ Work.Spaces.Iz := by
    intro z hz
    simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hz ⊢
    exact le_of_lt hz
  have hSint : MeasureTheory.Integrable S (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    hSintIz.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hIoiIz)
  have hTint : MeasureTheory.Integrable T (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    hTintIz.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hIoiIz)
  have hxint : MeasureTheory.Integrable
      (fun z : ℝ => (1 / (z * Work.Spaces.w z))^2)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := inv_zw_sq_integrableOn.1
  have hGint : MeasureTheory.Integrable
      (fun z : ℝ => (Cst/2) * (S z + T z + 2 * (1/(z * Work.Spaces.w z))^2))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    ((hSint.add hTint).add (hxint.const_mul 2)).const_mul (Cst/2)
  have hmeasdiv : AEStronglyMeasurable (fun z : ℝ => lam z / z)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    (hlammeas.div measurable_id).aestronglyMeasurable
  have hIntOn : MeasureTheory.IntegrableOn (fun z : ℝ => lam z / z) (Set.Ioi (0:ℝ)) :=
    MeasureTheory.Integrable.mono' hGint hmeasdiv hmain
  have hcomp := (integrable_comp_exp (fun z : ℝ => lam z / z)).mpr hIntOn
  have hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)) :=
    hcomp.congr (Filter.Eventually.of_forall fun u => by
      show Real.exp u • (lam (Real.exp u) / Real.exp u) = lam (Real.exp u)
      rw [smul_eq_mul, mul_comm, div_mul_cancel₀ _ (Real.exp_ne_zero u)])
  exact ⟨lam, hlammeas, htr, hbd, hint⟩

end Work.FTS.StrongEps.EpsLocalPStar
