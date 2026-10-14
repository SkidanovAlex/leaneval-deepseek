import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.cmode_variation_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-! ## Helpers -/

private def phiW (m : ℕ) (θ : ℝ) : ℝ := Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ

private def numW (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, F z θ * phiW m θ

private def hkSlice (α : ℝ) (F : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ

private theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

private theorem continuous_phiW (m : ℕ) : Continuous (phiW m) := by
  have h : Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
    rw [show Work.FTS.PhiStar.Gegenbauer.eFam m = fun θ : ℝ =>
      Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) from rfl]
    exact Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
        Real.continuous_sin)
  rw [show phiW m = fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ from rfl]
  exact h.mul Real.continuous_cos

private theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ,
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2)).symm]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

private theorem cmode_eq_num_div (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.cmode m F z
      = numW m F z / (((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5)) := by
  have hden : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
      = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) :=
    Work.FTS.PhiStar.Gegenbauer.FamNormValue m
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, F z θ * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Real.cos θ) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2),
      Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun θ _ => by ring)
  rw [Work.FTS.PhiStar.Series.cmode, hnum, hden]
  simp only [numW, phiW]

/-! ## The main theorem -/

theorem cmode_variation_le (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α 1 F →
      ∀ {x y : ℝ}, 0 < y → y ≤ x →
        |Work.FTS.PhiStar.Series.cmode m F x - Work.FTS.PhiStar.Series.cmode m F y|
          ≤ K * x ^ ((3 : ℝ) / 2)
            * Real.sqrt (∫ t in y..x, ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 1 F t θ) := by
  obtain ⟨Cφ, hCφnn, hCφ⟩ := Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos m
  set D : ℝ := ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hphibd : ∀ θ ∈ Work.Spaces.Iθ, |phiW m θ| ≤ Cφ := fun θ hθ => by
    rw [show phiW m θ = Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ from rfl]
    exact hCφ θ hθ
  refine ⟨(Cφ * Real.sqrt (Real.pi / 2) + 1) / D + 1, ?_, ?_⟩
  · have h1 : 0 ≤ (Cφ * Real.sqrt (Real.pi / 2) + 1) / D :=
      div_nonneg (by have h := mul_nonneg hCφnn (Real.sqrt_nonneg (Real.pi / 2)); linarith)
        hDpos.le
    linarith
  intro α F hsm hF x y hy hyx
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  have huIoc : Set.uIoc y x = Set.Ioc y x := Set.uIoc_of_le hyx
  have hmem : ∀ t ∈ Set.uIoc y x, 0 < t := by
    intro t ht
    rw [huIoc] at ht
    exact lt_trans hy (Set.mem_Ioc.mp ht).1
  have hmem_le : ∀ t ∈ Set.uIoc y x, t ≤ x := by
    intro t ht
    rw [huIoc] at ht
    exact (Set.mem_Ioc.mp ht).2
  have hAnn : ∀ t, 0 ≤ hkSlice α F t := fun t =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 1 F t θ
  -- integrability of the numerator integrands
  have hprodint : ∀ z : ℝ, 0 < z → MeasureTheory.Integrable (fun θ : ℝ => F z θ * phiW m θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have hbase : MeasureTheory.Integrable (fun θ : ℝ => |F z θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (Work.FTS.PhiStar.Honesty.slice_abs_integrable hsm hF hz).1
    refine MeasureTheory.Integrable.mono' (hbase.const_mul Cφ) ?_ ?_
    · exact ((hsm.aesm_slice_pzIter 0 hz).mul (continuous_phiW m).aestronglyMeasurable)
    · filter_upwards [MeasureTheory.ae_restrict_mem (by
          rw [Work.Spaces.Iθ]; exact measurableSet_Icc)] with θ hθ
      rw [Real.norm_eq_abs, abs_mul]
      calc |F z θ| * |phiW m θ| ≤ |F z θ| * Cφ :=
            mul_le_mul_of_nonneg_left (hphibd θ hθ) (abs_nonneg _)
        _ = Cφ * |F z θ| := by ring
  have hFx : MeasureTheory.Integrable (fun θ : ℝ => F x θ * phiW m θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hprodint x hx
  have hFy : MeasureTheory.Integrable (fun θ : ℝ => F y θ * phiW m θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hprodint y hy
  have hdiff : numW m F x - numW m F y
      = ∫ θ in Work.Spaces.Iθ, (F x θ - F y θ) * phiW m θ := by
    simp only [numW]
    rw [← MeasureTheory.integral_sub hFx hFy]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ _ => by ring)
  have habs : |numW m F x - numW m F y|
      ≤ ∫ θ in Work.Spaces.Iθ, |F x θ - F y θ| * |phiW m θ| := by
    have h1 : |numW m F x - numW m F y|
        ≤ ∫ θ in Work.Spaces.Iθ, |(F x θ - F y θ) * phiW m θ| := by
      rw [hdiff]
      exact MeasureTheory.abs_integral_le_integral_abs
    have h2 : (∫ θ in Work.Spaces.Iθ, |(F x θ - F y θ) * phiW m θ|)
        = ∫ θ in Work.Spaces.Iθ, |F x θ - F y θ| * |phiW m θ| :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ _ => by rw [abs_mul])
    rwa [h2] at h1
  -- the Tonelli input
  obtain ⟨hIint, hIswap⟩ := integral_swap_pz_abs hsm hF hy hyx
  have h2b : (∫ θ in Work.Spaces.Iθ, |F x θ - F y θ| * |phiW m θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, Cφ * (∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ|) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) ?_ ?_
    · exact hIint.const_mul Cφ
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      have hdθ : |F x θ - F y θ| ≤ ∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ| :=
        Work.FTS.PhiStar.Honesty.slice_abs_diff_le_uIoc hsm hθ hx hy
      have hph : |phiW m θ| ≤ Cφ := hphibd θ ⟨hθ.1.le, hθ.2.le⟩
      have hnn : 0 ≤ ∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ| :=
        integral_nonneg fun t => abs_nonneg _
      calc |F x θ - F y θ| * |phiW m θ|
          ≤ (∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ|) * Cφ :=
            mul_le_mul hdθ hph (abs_nonneg _) hnn
        _ = Cφ * (∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ|) := by ring
  have h3b : (∫ θ in Work.Spaces.Iθ, Cφ * (∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ|))
      = Cφ * ∫ θ in Work.Spaces.Iθ, (∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ|) :=
    MeasureTheory.integral_const_mul Cφ _
  -- the interval machinery
  have hAint : MeasureTheory.IntegrableOn (hkSlice α F) (Set.uIoc y x) :=
    hF.2.mono_set (fun t ht => le_of_lt (hmem t ht))
  have hconst1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.uIoc y x) :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ)) (s := Set.uIoc y x)
      (by rw [huIoc, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hplus1 : MeasureTheory.IntegrableOn (fun t : ℝ => hkSlice α F t + 1) (Set.uIoc y x) :=
    hAint.add hconst1
  have hsqrt_int : MeasureTheory.IntegrableOn (fun t : ℝ => Real.sqrt (hkSlice α F t))
      (Set.uIoc y x) := by
    refine MeasureTheory.Integrable.mono' hplus1 ?_ ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable hAint.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hs : (Real.sqrt (hkSlice α F t)) ^ 2 = hkSlice α F t := Real.sq_sqrt (hAnn t)
      nlinarith [sq_nonneg (Real.sqrt (hkSlice α F t) - 1), Real.sqrt_nonneg (hkSlice α F t)]
  have hAintI : IntervalIntegrable (hkSlice α F) MeasureTheory.volume y x :=
    intervalIntegrable_iff.mpr hAint
  have hsqrtI : IntervalIntegrable (fun t : ℝ => Real.sqrt (hkSlice α F t))
      MeasureTheory.volume y x := intervalIntegrable_iff.mpr hsqrt_int
  -- the per-slice bound
  have hpt : ∀ t ∈ Set.uIoc y x, (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|)
      ≤ Real.sqrt (Real.pi / 2) * (t / (1 + t) ^ 2) * Real.sqrt (hkSlice α F t) :=
    fun t ht => pz_abs_slice_le_sqrt_Hk hsm hF (hmem t ht)
  have hdom_int : MeasureTheory.Integrable
      (fun t : ℝ => Real.sqrt (Real.pi / 2) * (t / (1 + t) ^ 2) * Real.sqrt (hkSlice α F t))
      (MeasureTheory.volume.restrict (Set.uIoc y x)) := by
    have hbdd : MeasureTheory.Integrable
        (fun t : ℝ => Real.sqrt (Real.pi / 2) * x * (hkSlice α F t + 1))
        (MeasureTheory.volume.restrict (Set.uIoc y x)) :=
      (hplus1.const_mul (Real.sqrt (Real.pi / 2) * x) : _)
    refine MeasureTheory.Integrable.mono' hbdd ?_ ?_
    · exact ((measurable_const.mul (by fun_prop : Measurable fun t : ℝ => t / (1 + t) ^ 2)
        ).aestronglyMeasurable.mul
          (Real.continuous_sqrt.comp_aestronglyMeasurable hAint.aestronglyMeasurable))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
      have ht0 : 0 ≤ t := le_of_lt (hmem t ht)
      have htx : t ≤ x := hmem_le t ht
      have hc_nn : 0 ≤ t / (1 + t) ^ 2 := div_nonneg ht0 (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        hc_nn) (Real.sqrt_nonneg _))]
      have hc_le : t / (1 + t) ^ 2 ≤ x := by
        have h1 : t / (1 + t) ^ 2 ≤ t := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + t) ^ 2)]
          nlinarith [sq_nonneg t, ht0]
        linarith
      have hs_le : Real.sqrt (hkSlice α F t) ≤ hkSlice α F t + 1 := by
        have hs : (Real.sqrt (hkSlice α F t)) ^ 2 = hkSlice α F t := Real.sq_sqrt (hAnn t)
        nlinarith [sq_nonneg (Real.sqrt (hkSlice α F t) - 1),
          Real.sqrt_nonneg (hkSlice α F t)]
      have h1 : Real.sqrt (Real.pi / 2) * (t / (1 + t) ^ 2) ≤ Real.sqrt (Real.pi / 2) * x :=
        mul_le_mul_of_nonneg_left hc_le (Real.sqrt_nonneg _)
      have h3 : 0 ≤ Real.sqrt (Real.pi / 2) * x :=
        mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hx)
      exact mul_le_mul h1 hs_le (Real.sqrt_nonneg _) h3
  have hstep1 : (∫ t in Set.uIoc y x, (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|))
      ≤ ∫ t in Set.uIoc y x,
          Real.sqrt (Real.pi / 2) * (t / (1 + t) ^ 2) * Real.sqrt (hkSlice α F t) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => integral_nonneg fun θ => abs_nonneg _)
      hdom_int
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc hpt)
  have hstep2 : (∫ t in Set.uIoc y x,
        Real.sqrt (Real.pi / 2) * (t / (1 + t) ^ 2) * Real.sqrt (hkSlice α F t))
      = Real.sqrt (Real.pi / 2)
        * ∫ t in Set.uIoc y x, (t / (1 + t) ^ 2) * Real.sqrt (hkSlice α F t) := by
    rw [show (fun t : ℝ => Real.sqrt (Real.pi / 2) * (t / (1 + t) ^ 2)
          * Real.sqrt (hkSlice α F t))
        = (fun t : ℝ => Real.sqrt (Real.pi / 2)
            * ((t / (1 + t) ^ 2) * Real.sqrt (hkSlice α F t))) from
      funext fun t => by ring]
    rw [MeasureTheory.integral_const_mul]
  have hstep3 : (∫ t in Set.uIoc y x, (t / (1 + t) ^ 2) * Real.sqrt (hkSlice α F t))
      = ∫ t in y..x, (t / (1 + t) ^ 2) * Real.sqrt (hkSlice α F t) := by
    rw [huIoc, ← intervalIntegral.integral_of_le hyx]
  have h5 : (∫ t in Set.uIoc y x, (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|))
      ≤ Real.sqrt (Real.pi / 2) * x ^ ((3 : ℝ) / 2)
        * Real.sqrt (∫ t in y..x, hkSlice α F t) := by
    calc (∫ t in Set.uIoc y x, (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|))
        ≤ ∫ t in Set.uIoc y x,
            Real.sqrt (Real.pi / 2) * (t / (1 + t) ^ 2) * Real.sqrt (hkSlice α F t) := hstep1
      _ = Real.sqrt (Real.pi / 2)
            * ∫ t in Set.uIoc y x, (t / (1 + t) ^ 2) * Real.sqrt (hkSlice α F t) := hstep2
      _ = Real.sqrt (Real.pi / 2)
            * ∫ t in y..x, (t / (1 + t) ^ 2) * Real.sqrt (hkSlice α F t) := by rw [hstep3]
      _ ≤ Real.sqrt (Real.pi / 2)
            * (x ^ ((3 : ℝ) / 2) * Real.sqrt (∫ t in y..x, hkSlice α F t)) :=
          mul_le_mul_of_nonneg_left (intervalIntegral_weight_mul_sqrt_le hy hyx hAnn hAintI hsqrtI) (Real.sqrt_nonneg _)
      _ = Real.sqrt (Real.pi / 2) * x ^ ((3 : ℝ) / 2)
            * Real.sqrt (∫ t in y..x, hkSlice α F t) := by ring
  have hmain : |numW m F x - numW m F y|
      ≤ Cφ * (Real.sqrt (Real.pi / 2) * x ^ ((3 : ℝ) / 2)
          * Real.sqrt (∫ t in y..x, hkSlice α F t)) :=
    calc |numW m F x - numW m F y|
        ≤ ∫ θ in Work.Spaces.Iθ, |F x θ - F y θ| * |phiW m θ| := habs
      _ ≤ ∫ θ in Work.Spaces.Iθ, Cφ * (∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ|) := h2b
      _ = Cφ * ∫ θ in Work.Spaces.Iθ,
            (∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ|) := h3b
      _ = Cφ * ∫ t in Set.uIoc y x,
            (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|) := by rw [hIswap]
      _ ≤ Cφ * (Real.sqrt (Real.pi / 2) * x ^ ((3 : ℝ) / 2)
            * Real.sqrt (∫ t in y..x, hkSlice α F t)) :=
          mul_le_mul_of_nonneg_left h5 hCφnn
  have hcm : |Work.FTS.PhiStar.Series.cmode m F x - Work.FTS.PhiStar.Series.cmode m F y|
      = |numW m F x - numW m F y| / D := by
    have hDE : ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) = D := hDdef.symm
    rw [cmode_eq_num_div m F x, cmode_eq_num_div m F y, ← sub_div, abs_div, hDE,
      abs_of_pos hDpos]
  have hle_div : |Work.FTS.PhiStar.Series.cmode m F x - Work.FTS.PhiStar.Series.cmode m F y|
      ≤ (Cφ * Real.sqrt (Real.pi / 2) * x ^ ((3 : ℝ) / 2)
          * Real.sqrt (∫ t in y..x, hkSlice α F t)) / D := by
    rw [hcm]
    refine div_le_div_of_nonneg_right ?_ hDpos.le
    calc |numW m F x - numW m F y|
        ≤ Cφ * (Real.sqrt (Real.pi / 2) * x ^ ((3 : ℝ) / 2)
            * Real.sqrt (∫ t in y..x, hkSlice α F t)) := hmain
      _ = Cφ * Real.sqrt (Real.pi / 2) * x ^ ((3 : ℝ) / 2)
            * Real.sqrt (∫ t in y..x, hkSlice α F t) := by ring
  have hfinal : |Work.FTS.PhiStar.Series.cmode m F x - Work.FTS.PhiStar.Series.cmode m F y|
      ≤ ((Cφ * Real.sqrt (Real.pi / 2) + 1) / D + 1) * x ^ ((3 : ℝ) / 2)
          * Real.sqrt (∫ t in y..x, hkSlice α F t) := by
    refine le_trans hle_div ?_
    have hSnn : 0 ≤ Real.sqrt (∫ t in y..x, hkSlice α F t) := Real.sqrt_nonneg _
    have hxnn : 0 ≤ x ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hx.le _
    have hKD : Cφ * Real.sqrt (Real.pi / 2) / D ≤ (Cφ * Real.sqrt (Real.pi / 2) + 1) / D + 1 := by
      have h3 : Cφ * Real.sqrt (Real.pi / 2) ≤ Cφ * Real.sqrt (Real.pi / 2) + 1 := by linarith
      have h4 := div_le_div_of_nonneg_right h3 hDpos.le
      linarith
    calc (Cφ * Real.sqrt (Real.pi / 2) * x ^ ((3 : ℝ) / 2)
            * Real.sqrt (∫ t in y..x, hkSlice α F t)) / D
        = (Cφ * Real.sqrt (Real.pi / 2) / D)
            * (x ^ ((3 : ℝ) / 2) * Real.sqrt (∫ t in y..x, hkSlice α F t)) := by ring
      _ ≤ ((Cφ * Real.sqrt (Real.pi / 2) + 1) / D + 1)
            * (x ^ ((3 : ℝ) / 2) * Real.sqrt (∫ t in y..x, hkSlice α F t)) :=
          mul_le_mul_of_nonneg_right hKD (mul_nonneg hxnn hSnn)
      _ = ((Cφ * Real.sqrt (Real.pi / 2) + 1) / D + 1) * x ^ ((3 : ℝ) / 2)
            * Real.sqrt (∫ t in y..x, hkSlice α F t) := by ring
  simpa only [hkSlice] using hfinal

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ip4UnfoldSix =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## `ip4_unfold_bound` at level five with finite-order smoothness

`Work.FTS.TransportS.ip4_unfold_bound` proves, for every level `n`,
`|IPn α n u v| ≤ 3^n · 10^22 · SlotSum α (n+1) u v` under `SmoothOpen u`, `SmoothOpen v`
(`C^∞` on the *open* quadrant).  The bare-`f` `N₀`-row needs the level-five case for a datum
that is only `C⁷` on the open quadrant (its coefficient `L₁₂(f)` is merely
`ContDiffOn ℝ 7`), so this file re-runs the very same induction with the *level-dependent*
finite-order hypothesis `ContDiffOn ℝ (n + 2) (uncurry u) Q0`.

The only analytic input of the unfolding is the shift of a slot along `D_z`, i.e. the
finite-order Clairaut identity
`D_z^bD_θ^a(D_z u) = D_z^{b+1}D_θ^a u` on `Q0` (`SixAux.mixed_dz_eqOn_fin`, obtained from
the `SmoothOpen` version `Work.FTS.TransportS.mixed_dz_eqOn` by tracking the derivative
order), together with the one-order closure of `ContDiffOn` under `D_z`/`D_θ`
(`SixAux.contDiffOn_Dz_le`, `SixAux.contDiffOn_Dth_le`).  The `D_θ`-shift of the slot sum is
hypothesis-free; the `D_z`-shift with the pointwise identity as a hypothesis is
`SlotSum_dz_le_of` (sibling module).  Everything else is the verbatim bookkeeping of
`ip4_unfold_bound`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace SixAux

/-! ## Order bookkeeping for `ContDiffOn` -/

/-- Weakening the order of a `ContDiffOn`-statement. -/
theorem cd_of_le_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} {m n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry G) V) (hmn : m ≤ n) :
    ContDiffOn ℝ m (Function.uncurry G) V :=
  h.of_le (by exact_mod_cast hmn)

/-- `∂_z` costs one order of smoothness on an open set. -/
theorem contDiffOn_pz_le {V : Set (ℝ × ℝ)} (hV : IsOpen V) {G : ℝ → ℝ → ℝ} {m : ℕ}
    (h : ContDiffOn ℝ (m + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ m (Function.uncurry (Work.Spaces.pz G)) V := by
  have hfd : ContDiffOn ℝ m (fderiv ℝ (Function.uncurry G)) V :=
    h.fderiv_of_isOpen hV (by norm_num)
  have hcomp : ContDiffOn ℝ m
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) ((1 : ℝ), (0 : ℝ))) V :=
    (ContinuousLinearMap.contDiff
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ)))).comp_contDiffOn hfd
  refine hcomp.congr ?_
  intro p hp
  exact Work.Spaces.pz_eq_fderiv
    ((h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp))

/-- `∂_θ` costs one order of smoothness on an open set. -/
theorem contDiffOn_pth_le {V : Set (ℝ × ℝ)} (hV : IsOpen V) {G : ℝ → ℝ → ℝ} {m : ℕ}
    (h : ContDiffOn ℝ (m + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ m (Function.uncurry (Work.Spaces.pth G)) V := by
  have hfd : ContDiffOn ℝ m (fderiv ℝ (Function.uncurry G)) V :=
    h.fderiv_of_isOpen hV (by norm_num)
  have hcomp : ContDiffOn ℝ m
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) ((0 : ℝ), (1 : ℝ))) V :=
    (ContinuousLinearMap.contDiff
      (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ)))).comp_contDiffOn hfd
  refine hcomp.congr ?_
  intro p hp
  exact Work.Spaces.pth_eq_fderiv
    ((h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp))

/-- `D_z = z∂_z` costs one order of smoothness on an open set. -/
theorem contDiffOn_Dz_le {V : Set (ℝ × ℝ)} (hV : IsOpen V) {G : ℝ → ℝ → ℝ} {m : ℕ}
    (h : ContDiffOn ℝ (m + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ m (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact contDiffOn_fst.mul (contDiffOn_pz_le hV h)

/-- `D_θ = sin(2θ)∂_θ` costs one order of smoothness on an open set. -/
theorem contDiffOn_Dth_le {V : Set (ℝ × ℝ)} (hV : IsOpen V) {G : ℝ → ℝ → ℝ} {m : ℕ}
    (h : ContDiffOn ℝ (m + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ m (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dth G)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  have hsin : ContDiffOn ℝ m (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    ((Real.contDiff_sin.comp
      ((contDiff_const (c := (2 : ℝ))).mul contDiff_snd))).contDiffOn
  exact hsin.mul (contDiffOn_pth_le hV h)


/-- The iterated `D_θ^i` costs `i` orders of smoothness on an open set. -/
theorem contDiffOn_DthIter_le {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (i : ℕ) {G : ℝ → ℝ → ℝ} {m : ℕ},
      ContDiffOn ℝ (i + m) (Function.uncurry G) V →
      ContDiffOn ℝ m (Function.uncurry (Work.Spaces.DthIter i G)) V := by
  intro i
  induction i with
  | zero => intro G m h; exact cd_of_le_nat (m := m) (n := 0 + m) h (by omega)
  | succ i ih =>
      intro G m h
      have h1 : ContDiffOn ℝ (i + m + 1 : ℕ) (Function.uncurry G) V :=
        cd_of_le_nat (m := i + m + 1) (n := Nat.succ i + m) h (by omega)
      have h2 : ContDiffOn ℝ (i + m : ℕ) (Function.uncurry (Work.Spaces.Dth G)) V :=
        contDiffOn_Dth_le hV h1
      have h3 : ContDiffOn ℝ m
          (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dth G))) V := ih h2
      rwa [Work.FTS.TransportS.DthIter_comp] at h3

/-! ## The finite-order Clairaut chain -/

/-- `D_θ` and `D_z` commute at any point where the datum is `C²`. -/
theorem Dth_Dz_apply_fin {X : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ 2 (Function.uncurry X) (z, θ)) :
    Work.Spaces.Dth (Work.Spaces.Dz X) z θ = Work.Spaces.Dz (Work.Spaces.Dth X) z θ :=
  (Work.Spaces.Dz_Dth_comm hX).symm

/-- `D_θ^i(D_z X) = D_z(D_θ^i X)` on the open quadrant, for `X` of class `C^{i+1}`. -/
theorem Dth_Dz_iter_eqOn_fin (i : ℕ) {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ (i + 1) (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz X)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i X)))
      Work.FTS.EllipticEst.Q0 := by
  induction i with
  | zero => intro p hp; rfl
  | succ i ih =>
      have h1 : ContDiffOn ℝ (i + 1) (Function.uncurry X) Work.FTS.EllipticEst.Q0 :=
        cd_of_le_nat (m := i + 1) (n := Nat.succ i + 1) hX (by omega)
      have h2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DthIter i X))
          Work.FTS.EllipticEst.Q0 :=
        contDiffOn_DthIter_le Work.FTS.EllipticEst.isOpen_Q0 i (m := 2)
          (cd_of_le_nat (m := i + 2) (n := Nat.succ i + 1) hX (by omega))
      have hA : Set.EqOn
          (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz X))))
          (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i X))))
          Work.FTS.EllipticEst.Q0 :=
        Work.FTS.TransportS.Dth_congrOn Work.FTS.EllipticEst.isOpen_Q0 (ih h1)
      have hB : Set.EqOn
          (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i X))))
          (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i X))))
          Work.FTS.EllipticEst.Q0 := fun p hp =>
        Dth_Dz_apply_fin (h2.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))
      exact hA.trans hB

/-- **The finite-order slot identity**: on the open quadrant the `z`-derivative slides through
the iterated curvilinear derivatives, needing only `C^{a+b+1}` of `u`. -/
theorem mixed_dz_eqOn_fin {u : ℝ → ℝ → ℝ} (b a : ℕ)
    (hu : ContDiffOn ℝ (a + b + 1) (Function.uncurry u) Work.FTS.EllipticEst.Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz u)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a u)) Work.FTS.EllipticEst.Q0 := by
  have h1 : Set.EqOn (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.Dz u)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter a u))) Work.FTS.EllipticEst.Q0 :=
    Dth_Dz_iter_eqOn_fin a (cd_of_le_nat (m := a + 1) (n := a + b + 1) hu (by omega))
  have h2 := Work.FTS.TransportS.DzIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 h1 b
  intro p hp
  have h4 : Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.Dz u)) p.1 p.2
      = Work.Spaces.DzIter b (Work.Spaces.Dz (Work.Spaces.DthIter a u)) p.1 p.2 := h2 hp
  show Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.Dz u)) p.1 p.2
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a u) p.1 p.2
  rw [h4, Work.FTS.TransportS.DzIter_comp]

end SixAux

/-! ## The shifts of the slot sum -/

/-- The `D_θ`-shift of the slot sum needs no smoothness at all (the underlying shift of the
slot pairing is definitional). -/
theorem SlotTerm_dth_le_fin (α : ℝ) (a b : ℕ) (u v : ℝ → ℝ → ℝ) :
    Work.FTS.TransportS.SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v)
      ≤ Work.FTS.TransportS.SlotTerm α (a + 1) b u v := by
  have heta := Work.FTS.TransportS.slotPairing_dth Work.FTS.TransportS.leafEta a b u v
  have hone := Work.FTS.TransportS.slotPairing_dth Work.FTS.TransportS.leafOne a b u v
  have hgam := Work.FTS.TransportS.slotPairing_dth (Work.FTS.TransportS.leafGam α) a b u v
  have hthird : (if 1 ≤ a then
        |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) (a + 1) b u v|
      else 0)
      ≤ (if 1 ≤ a + 1 then
        |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) (a + 1) b u v|
      else 0) := by
    rw [if_pos (by omega : 1 ≤ a + 1)]
    by_cases ha : 1 ≤ a
    · rw [if_pos ha]
    · rw [if_neg ha]
      exact abs_nonneg _
  unfold Work.FTS.TransportS.SlotTerm
  rw [heta, hone, hgam]
  linarith [hthird]

/-- The `D_θ`-shift of the slot sum at finite order. -/
theorem SlotSum_dth_le_fin (α : ℝ) (n : ℕ) (u v : ℝ → ℝ → ℝ) :
    Work.FTS.TransportS.SlotSum α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)
      ≤ Work.FTS.TransportS.SlotSum α (n + 1) u v := by
  rw [Work.FTS.TransportS.SlotSum_eq_sum_SlotTerm,
    Work.FTS.TransportS.SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          Work.FTS.TransportS.SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          Work.FTS.TransportS.SlotTerm α (a + 1) b u v :=
        Finset.sum_le_sum (fun a _ =>
          Finset.sum_le_sum (fun b _ => SlotTerm_dth_le_fin α a b u v))
    _ = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2 - (a + 1)),
          Work.FTS.TransportS.SlotTerm α (a + 1) b u v := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [show n + 2 - (a + 1) = n + 1 - a from Nat.succ_sub_succ (n := n + 1) (m := a)]
    _ ≤ ∑ a' ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2 - a'),
          Work.FTS.TransportS.SlotTerm α a' b u v := by
        conv_rhs => rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right
          (show (0 : ℝ) ≤ ∑ b ∈ Finset.range (n + 2 - 0),
            Work.FTS.TransportS.SlotTerm α 0 b u v from
            Finset.sum_nonneg (fun b _ => Work.FTS.TransportS.SlotTerm_nonneg α 0 b u v))

/-! ## The unfolding at finite order -/

/-- **The induction of the unfolding at finite order.**  For every `n`, the `n`-fold iterate
of the coercive recursion is dominated by `3^n · 10^22` times the slot sum of level `n + 1`,
under the level-dependent hypothesis that the datum is `C^{n+2}` on the open quadrant. -/
theorem ip4_unfold_bound_fin : ∀ (n : ℕ) (α : ℝ) (u v : ℝ → ℝ → ℝ),
    ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry u) Work.FTS.EllipticEst.Q0 →
    ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry v) Work.FTS.EllipticEst.Q0 →
    |Work.FTS.TransportS.IPn α n u v|
      ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * Work.FTS.TransportS.SlotSum α (n + 1) u v := by
  intro n
  induction n with
  | zero =>
      intro α u v hu hv
      rw [show Work.FTS.TransportS.IPn α 0 = Work.Coercivity.H1IP α from rfl]
      simpa using Work.FTS.TransportS.H1IP_le_SlotSum_one α u v
  | succ n ih =>
      intro α u v hu hv
      have hu' : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry u) Work.FTS.EllipticEst.Q0 :=
        SixAux.cd_of_le_nat (m := n + 2) (n := n + 3) hu (by omega)
      have hv' : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry v) Work.FTS.EllipticEst.Q0 :=
        SixAux.cd_of_le_nat (m := n + 2) (n := n + 3) hv (by omega)
      have hdt : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry (Work.Spaces.Dth u))
          Work.FTS.EllipticEst.Q0 :=
        SixAux.contDiffOn_Dth_le (m := n + 2) Work.FTS.EllipticEst.isOpen_Q0
          (show ContDiffOn ℝ (n + 2 + 1 : ℕ) (Function.uncurry u)
            Work.FTS.EllipticEst.Q0 from hu)
      have hdv : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry (Work.Spaces.Dth v))
          Work.FTS.EllipticEst.Q0 :=
        SixAux.contDiffOn_Dth_le (m := n + 2) Work.FTS.EllipticEst.isOpen_Q0
          (show ContDiffOn ℝ (n + 2 + 1 : ℕ) (Function.uncurry v)
            Work.FTS.EllipticEst.Q0 from hv)
      have hdz : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry (Work.Spaces.Dz u))
          Work.FTS.EllipticEst.Q0 :=
        SixAux.contDiffOn_Dz_le (m := n + 2) Work.FTS.EllipticEst.isOpen_Q0
          (show ContDiffOn ℝ (n + 2 + 1 : ℕ) (Function.uncurry u)
            Work.FTS.EllipticEst.Q0 from hu)
      have hdzu : ContDiffOn ℝ (n + 2 : ℕ) (Function.uncurry (Work.Spaces.Dz v))
          Work.FTS.EllipticEst.Q0 :=
        SixAux.contDiffOn_Dz_le (m := n + 2) Work.FTS.EllipticEst.isOpen_Q0
          (show ContDiffOn ℝ (n + 2 + 1 : ℕ) (Function.uncurry v)
            Work.FTS.EllipticEst.Q0 from hv)
      have hIHu := ih α u v hu' hv'
      have hIHd := ih α (Work.Spaces.Dth u) (Work.Spaces.Dth v) hdt hdv
      have hIHz := ih α (Work.Spaces.Dz u) (Work.Spaces.Dz v) hdz hdzu
      have hd := SlotSum_dth_le_fin α (n + 1) u v
      have hz : Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
            (Work.Spaces.Dz v)
          ≤ Work.FTS.TransportS.SlotSum α (n + 1 + 1) u v :=
        SlotSum_dz_le_of (n := n + 1)
          (fun a b _ => SixAux.mixed_dz_eqOn_fin b a
            (SixAux.cd_of_le_nat (m := a + b + 1) (n := n + 3) hu (by omega)))
          (fun a b _ => SixAux.mixed_dz_eqOn_fin b a
            (SixAux.cd_of_le_nat (m := a + b + 1) (n := n + 3) hv (by omega)))
      have hmono := Work.FTS.TransportS.SlotSum_mono (α := α) (u := u) (v := v)
        (n := n + 1) (m := n + 1 + 1) (by omega)
      have hsum : Work.FTS.TransportS.SlotSum α (n + 1) u v
            + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dth u)
              (Work.Spaces.Dth v)
            + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
              (Work.Spaces.Dz v)
          ≤ 3 * Work.FTS.TransportS.SlotSum α (n + 1 + 1) u v := by
        linarith
      have hstep : Work.FTS.TransportS.IPn α (n + 1) u v
          = Work.FTS.TransportS.IPn α n u v
            + Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v) := by
        rw [show Work.FTS.TransportS.IPn α (n + 1)
              = Work.Coercivity.HkIPStep 1 1 (Work.FTS.TransportS.IPn α n) from rfl]
        simp only [Work.Coercivity.HkIPStep, one_mul]
      rw [hstep]
      have htri : |Work.FTS.TransportS.IPn α n u v
            + Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ |Work.FTS.TransportS.IPn α n u v|
            + |Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)| := by
        have h1 := abs_add_le
          (Work.FTS.TransportS.IPn α n u v
            + Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v))
          (Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v))
        have h2 := abs_add_le (Work.FTS.TransportS.IPn α n u v)
          (Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v))
        linarith
      have hscale : |Work.FTS.TransportS.IPn α n u v|
            + |Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * Work.FTS.TransportS.SlotSum α (n + 1) u v
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22
              * Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dth u)
                (Work.Spaces.Dth v)
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22
              * Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
                (Work.Spaces.Dz v) := by
        linarith
      have hfac : (3 : ℝ) ^ n * (10 : ℝ) ^ 22 * Work.FTS.TransportS.SlotSum α (n + 1) u v
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22
              * Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dth u)
                (Work.Spaces.Dth v)
            + (3 : ℝ) ^ n * (10 : ℝ) ^ 22
              * Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
                (Work.Spaces.Dz v)
          = (3 : ℝ) ^ n * (10 : ℝ) ^ 22
            * (Work.FTS.TransportS.SlotSum α (n + 1) u v
              + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dth u)
                (Work.Spaces.Dth v)
              + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
                (Work.Spaces.Dz v)) := by
        ring
      have hnonneg : (0 : ℝ) ≤ (3 : ℝ) ^ n * (10 : ℝ) ^ 22 := by positivity
      have hfinal : (3 : ℝ) ^ n * (10 : ℝ) ^ 22
            * (Work.FTS.TransportS.SlotSum α (n + 1) u v
              + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dth u)
                (Work.Spaces.Dth v)
              + Work.FTS.TransportS.SlotSum α (n + 1) (Work.Spaces.Dz u)
                (Work.Spaces.Dz v))
          ≤ (3 : ℝ) ^ (n + 1) * (10 : ℝ) ^ 22
            * Work.FTS.TransportS.SlotSum α (n + 1 + 1) u v := by
        have h3 : (3 : ℝ) ^ n * (10 : ℝ) ^ 22
              * (3 * Work.FTS.TransportS.SlotSum α (n + 1 + 1) u v)
            = (3 : ℝ) ^ (n + 1) * (10 : ℝ) ^ 22
              * Work.FTS.TransportS.SlotSum α (n + 1 + 1) u v := by
          rw [pow_succ]; ring
        rw [← h3]
        exact mul_le_mul_of_nonneg_left hsum hnonneg
      linarith [htri, hscale, hfac, hfinal]

/-- `ip4_unfold_bound` at level five with FINITE-ORDER smoothness (`C⁷`) instead of
`SmoothOpen`.  This is what the bare-`f` `N₀`-row needs: there `u = N₀ α (F_* + f) f` has
the coefficient `L₁₂(f)`, which is only `ContDiffOn ℝ 7 (·) (Ioi 0)` (`UopHk.contDiffOn_L12_k`
with `HkMem α 7 f`), and `SmoothOpen (fun z _ => L₁₂ f z)` is NOT available.

ROUTE.  Copy the proof of `TransportS.ip4_unfold_bound`
(`Submission/Work/FTS/TransportS/ip4SlotDomFixed.lean`, line 520), running the induction with
the level-dependent hypothesis `ContDiffOn ℝ (n + 2) (uncurry u) Q0`: the inductive calls at
`(Dth u, Dth v)` and `(Dz u, Dz v)` need `C^{n+2}` of `Dth u` resp. `Dz u`, i.e. `C^{n+3}`
of `u`, and the shift `SlotSum α (n+1) (Dz u) ≤ SlotSum α (n+2) u` is the only place needing
Clairaut (`D_θ D_z = D_z D_θ`: `SixAux.mixed_dz_eqOn_fin`), at derivative order
`a + b + 1 ≤ n + 3`; the `Dth`-shift `mixed b a (Dth u) = mixed b (a+1) u` is definitional.
The base case `H1IP_le_SlotSum_one` has no smoothness hypotheses. -/
theorem ip4UnfoldSix (α : ℝ) (u v : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 7 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ 7 (Function.uncurry v) Work.FTS.EllipticEst.Q0) :
    |Work.FTS.TransportS.IPn α 5 u v|
      ≤ (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * Work.FTS.TransportS.SlotSum α 6 u v := by
  exact ip4_unfold_bound_fin 5 α u v hu hv

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
end
