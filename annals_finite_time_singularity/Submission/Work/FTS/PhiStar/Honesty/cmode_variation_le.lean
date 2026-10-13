/-
# `cmode_variation_le` — the `z`-variation of the mode coefficients is controlled by `ℋ¹`

For a source `F` which is `C^∞` on the open quadrant and honest in the weighted space
`Work.Spaces.HkMem α 1 F`, the `m`-th mode coefficient `cmode m F z` of the angular slice
`F z ·` (in the self-adjoint weight `cos θ dθ`) satisfies, for all `0 < y ≤ x`,

  `|cmode m F x - cmode m F y| ≤ K_m · x^{3/2} · √(∫_{y}^{x} ∫_θ HkIntegrand α 1 F t θ)`,

with a constant `K_m > 0` depending only on the mode number `m`.

**Route.**  `cmode m F z = numW m F z / eNorm m`, where `numW m F z = ∫_θ F z θ · e_m θ cos θ`.
The difference is rewritten with the `θ`-Fubini theorem for the nonnegative function
`|∂_z F|` on `(y,x] × Iθ`, and the `θ`-integral of `|∂_zF|` is dominated by the square root of
the slice of `HkIntegrand α 1 F` with the sharp weight `1/(t·w t) = t/(1+t)²`
(the `i = 1` summand of the integrand is `(t ∂_zF · w t / sin(2θ)^{η/2})²`).  A final
Cauchy–Schwarz in `t`, together with `t/(1+t)² ≤ t` and `∫_{uIoc y x} t² ≤ x³`
(which uses only `y ≥ 0`), produces the factor `x^{3/2}`.

The three analytic inputs are the sibling lemmas `pz_abs_slice_le_sqrt_Hk`,
`integral_swap_pz_abs` and `intervalIntegral_weight_mul_sqrt_le`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos
import Submission.Work.FTS.PhiStar.Honesty.slice_abs_diff_le_uIoc
import Submission.Work.FTS.PhiStar.Honesty.slice_abs_integrable
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.PhiStar.Honesty.pz_abs_slice_le_sqrt_Hk
import Submission.Work.FTS.PhiStar.Honesty.integral_swap_pz_abs
import Submission.Work.FTS.PhiStar.Honesty.intervalIntegral_weight_mul_sqrt_le

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
