import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.Elliptic.DivSinWPDefs
import Submission.Work.Elliptic.DivSinIdentDefs
import Submission.Work.Elliptic.DivSinIdentitySetup
import Submission.Work.Elliptic.DivSinIntegrable_u1
import Submission.Work.Elliptic.SliceBddBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-! ## The pointwise derivative of the primitive `DivSinWP`

`DivSinWP γ h θ = -(1/2) sin(2θ)^{3-γ} cos(2θ) (u'(θ))²` with `u = SinQ h`, so that

`d/dθ DivSinWP γ h θ = WDfun γ h θ = W2 θ - (3-γ) W1 θ - W3 θ`

on `(0, π/2)`.  This is the pointwise identity underlying the weighted integration by parts. -/

private theorem WPHasDeriv (γ : ℝ) (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (DivSinWP γ h) (WDfun γ h θ) θ := by
  have hsmU : ContDiffOn ℝ ⊤ h (Set.Ioo 0 (Real.pi / 2)) :=
    hh.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)
  have hsinU : ContDiffOn ℝ ⊤ (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hgU : ContDiffOn ℝ ⊤ (SinQ h) (Set.Ioo 0 (Real.pi / 2)) := by
    show ContDiffOn ℝ ⊤ (fun x => h x / Real.sin (2 * x)) _
    exact hsmU.div hsinU (fun x hx => ne_of_gt (sin_two_pos hx))
  have hderU : ContDiffOn ℝ ⊤ (deriv (SinQ h)) (Set.Ioo 0 (Real.pi / 2)) :=
    hgU.deriv_of_isOpen isOpen_Ioo le_top
  have huD : HasDerivAt (deriv (SinQ h)) (deriv (deriv (SinQ h)) θ) θ :=
    ((hderU.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)).hasDerivAt
  have hspos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hs := Work.Elliptic.hasDerivAt_sin_two θ
  have hc := Work.Elliptic.hasDerivAt_cos_two θ
  have h3 := hs.rpow_const (p := 3 - γ) (Or.inl (ne_of_gt hspos))
  have h1 : HasDerivAt (fun x : ℝ => -(1/2) * (Real.sin (2 * x)) ^ (3 - γ))
      (-(1/2) * ((2 * Real.cos (2 * θ)) * (3 - γ) * (Real.sin (2 * θ)) ^ (3 - γ - 1))) θ :=
    h3.const_mul (-(1/2))
  have h2 : HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-2 * Real.sin (2 * θ)) θ := hc
  have h4 : HasDerivAt (fun x : ℝ => (deriv (SinQ h) x) ^ 2)
      ((2 : ℝ) * (deriv (SinQ h) θ) ^ (2 - 1) * deriv (deriv (SinQ h)) θ) θ := huD.pow 2
  have hmain := (h1.mul h2).mul h4
  have hfun : DivSinWP γ h = fun x : ℝ => -(1/2) * (Real.sin (2 * x)) ^ (3 - γ)
      * Real.cos (2 * x) * (deriv (SinQ h) x) ^ 2 := rfl
  have hval : (-(1/2) * ((2 * Real.cos (2 * θ)) * (3 - γ) * (Real.sin (2 * θ)) ^ (3 - γ - 1))
          * Real.cos (2 * θ) + (-(1/2) * (Real.sin (2 * θ)) ^ (3 - γ)) * (-2 * Real.sin (2 * θ)))
          * (deriv (SinQ h) θ) ^ 2
        + ((-(1/2) * (Real.sin (2 * θ)) ^ (3 - γ)) * Real.cos (2 * θ))
          * ((2 : ℝ) * (deriv (SinQ h) θ) ^ (2 - 1) * deriv (deriv (SinQ h)) θ)
        = WDfun γ h θ := by
    have hexp : (3 : ℝ) - γ - 1 = 2 - γ := by ring
    have hs4 : (Real.sin (2 * θ)) ^ (4 - γ)
        = (Real.sin (2 * θ)) ^ (3 - γ) * Real.sin (2 * θ) := by
      rw [← Real.rpow_add_one (ne_of_gt hspos) (3 - γ)]
      congr 1
      ring
    rw [hexp, WDfun, W1, W2, W3, hs4]
    ring
  rw [hfun, ← hval]
  exact hmain

/-! ## The primitive vanishes at both endpoints -/

private theorem WPTendsto (γ : ℝ) (h : ℝ → ℝ) (hγ : γ < 3) (hh : Work.Elliptic.SmoothSlice h)
    (hb : Work.Elliptic.SliceBdd h) :
    Filter.Tendsto (DivSinWP γ h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (DivSinWP γ h)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨C, hC0, -, -, -, -, hE, -, -, -, -, hJ⟩ := hb
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4' : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hexp : 0 < 3 - γ := by linarith
  have hrpow : Filter.Tendsto (fun x : ℝ => x ^ (3 - γ)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hc := Real.continuousAt_rpow_const (0 : ℝ) (3 - γ) (Or.inr (le_of_lt hexp))
    have hval : (0 : ℝ) ^ (3 - γ) = 0 := Real.zero_rpow (ne_of_gt hexp)
    simpa [hval] using hc.tendsto
  have hC2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
  have hboundL : ∀ θ ∈ Set.Ioo 0 (Real.pi / 4),
      ‖DivSinWP γ h θ‖ ≤ (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * C ^ 2 := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hspos : 0 < Real.sin (2 * θ) := sin_two_pos hθ'
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (3 - γ) := Real.rpow_nonneg (le_of_lt hspos) _
    have hu : |deriv (SinQ h) θ| ≤ C := hE θ hθ
    have hu2 : (deriv (SinQ h) θ) ^ 2 ≤ C ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) hu 2
      rwa [sq_abs] at h
    show ‖DivSinWP γ h θ‖ ≤ (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * C ^ 2
    have heq : ‖DivSinWP γ h θ‖
        = (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * |Real.cos (2 * θ)|
          * (deriv (SinQ h) θ) ^ 2 := by
      rw [show DivSinWP γ h θ = -(1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * Real.cos (2 * θ)
        * (deriv (SinQ h) θ) ^ 2 from rfl]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg,
        abs_of_pos (by norm_num : (0 : ℝ) < 1/2), abs_of_nonneg hsnn, abs_pow, sq_abs]
    rw [heq]
    calc (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * |Real.cos (2 * θ)| * (deriv (SinQ h) θ) ^ 2
        ≤ (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * 1 * C ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)) hu2
            (sq_nonneg _) (by positivity)
      _ = (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * C ^ 2 := by ring
  have hboundR : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      ‖DivSinWP γ h θ‖ ≤ (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * C ^ 2 := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hspos : 0 < Real.sin (2 * θ) := sin_two_pos hθ'
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (3 - γ) := Real.rpow_nonneg (le_of_lt hspos) _
    have hu : |deriv (SinQ h) θ| ≤ C := hJ θ hθ
    have hu2 : (deriv (SinQ h) θ) ^ 2 ≤ C ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) hu 2
      rwa [sq_abs] at h
    show ‖DivSinWP γ h θ‖ ≤ (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * C ^ 2
    have heq : ‖DivSinWP γ h θ‖
        = (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * |Real.cos (2 * θ)|
          * (deriv (SinQ h) θ) ^ 2 := by
      rw [show DivSinWP γ h θ = -(1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * Real.cos (2 * θ)
        * (deriv (SinQ h) θ) ^ 2 from rfl]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg,
        abs_of_pos (by norm_num : (0 : ℝ) < 1/2), abs_of_nonneg hsnn, abs_pow, sq_abs]
    rw [heq]
    calc (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * |Real.cos (2 * θ)| * (deriv (SinQ h) θ) ^ 2
        ≤ (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * 1 * C ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)) hu2
            (sq_nonneg _) (by positivity)
      _ = (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * C ^ 2 := by ring
  constructor
  · have hlim : Filter.Tendsto
        (fun θ : ℝ => (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * C ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hbase : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
        simpa using (hcont.tendsto 0).mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      have hspow : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - γ))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa only [Function.comp_def] using hrpow.comp hbase
      have h := hspow.const_mul (C ^ 2 * (1/2))
      rw [mul_zero] at h
      refine h.congr' (Filter.Eventually.of_forall (fun θ => ?_))
      ring
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT hpi4] with θ hθ
    exact hboundL θ hθ
  · have hlim : Filter.Tendsto
        (fun θ : ℝ => (1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * C ^ 2)
        (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
      have hbase : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
          (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
        have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
        have h1 := (hcont.tendsto (Real.pi / 2)).mono_left
          (nhdsWithin_le_nhds : 𝓝[<] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
        have h2 : Real.sin (2 * (Real.pi / 2)) = 0 := by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        simpa [h2] using h1
      have hspow : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - γ))
          (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
        simpa only [Function.comp_def] using hrpow.comp hbase
      have h := hspow.const_mul (C ^ 2 * (1/2))
      rw [mul_zero] at h
      refine h.congr' (Filter.Eventually.of_forall (fun θ => ?_))
      ring
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsLT hpi4'] with θ hθ
    exact hboundR θ hθ


/-! ## Integrability of the integrands

Every integrand is bounded on `Iθ = [0, π/2]` by a constant multiple of `C²`, where `C` is
the constant of `SliceBdd_ae_bounds`.  On `Iθ` the powers `sin(2θ)^p` with `p ≥ 0` are at
most `1`, `cos(2θ)² ≤ 1`, `|u'| ≤ C` and — crucially, so that the `u''` factor causes no
trouble — `|sin(2θ) u''| ≤ C`. -/

private lemma W1mul_abs_le (γ : ℝ) (h : ℝ → ℝ) (hγ1 : 1 < γ) (hγ2 : γ ≤ 11/10)
    {C θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu1 : |deriv (SinQ h) θ| ≤ C) :
    ‖(3 - γ) * W1 γ h θ‖ ≤ 2 * C ^ 2 := by
  have hsnn : 0 ≤ Real.sin (2 * θ) := le_of_lt (sin_two_pos hθ)
  have hsp : (Real.sin (2 * θ)) ^ (2 - γ) ≤ 1 :=
    Real.rpow_le_one hsnn (Real.sin_le_one _) (by linarith)
  have h3 : (3 - γ) ≤ 2 := by linarith
  have h3nn : 0 ≤ 3 - γ := by linarith
  have hc2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_cos_le_one (2 * θ)) 2
    rwa [sq_abs, one_pow] at h
  have hu2 : (deriv (SinQ h) θ) ^ 2 ≤ C ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hu1 2
    rwa [sq_abs] at h
  rw [show (3 - γ) * W1 γ h θ = (3 - γ) * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - γ) * (deriv (SinQ h) θ) ^ 2 from by
    rw [W1]; ring]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg h3nn, abs_pow, sq_abs,
    abs_of_nonneg (Real.rpow_nonneg hsnn _), abs_pow, sq_abs]
  calc (3 - γ) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
        * (deriv (SinQ h) θ) ^ 2
      ≤ 2 * 1 * 1 * C ^ 2 :=
        mul_le_mul (mul_le_mul (mul_le_mul h3 hc2 (sq_nonneg _) (by norm_num)) hsp
          (Real.rpow_nonneg hsnn _) (by norm_num)) hu2 (sq_nonneg _) (by positivity)
    _ = 2 * C ^ 2 := by ring

private lemma W2_abs_le (γ : ℝ) (h : ℝ → ℝ) (hγ2 : γ ≤ 11/10)
    {C θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu1 : |deriv (SinQ h) θ| ≤ C) :
    ‖W2 γ h θ‖ ≤ C ^ 2 := by
  have hsnn : 0 ≤ Real.sin (2 * θ) := le_of_lt (sin_two_pos hθ)
  have hsp : (Real.sin (2 * θ)) ^ (4 - γ) ≤ 1 :=
    Real.rpow_le_one hsnn (Real.sin_le_one _) (by linarith)
  have hu2 : (deriv (SinQ h) θ) ^ 2 ≤ C ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hu1 2
    rwa [sq_abs] at h
  rw [show W2 γ h θ = (Real.sin (2 * θ)) ^ (4 - γ) * (deriv (SinQ h) θ) ^ 2 from rfl]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hsnn _), abs_pow, sq_abs]
  calc (Real.sin (2 * θ)) ^ (4 - γ) * (deriv (SinQ h) θ) ^ 2 ≤ 1 * C ^ 2 :=
        mul_le_mul hsp hu2 (sq_nonneg _) (by norm_num)
    _ = C ^ 2 := by ring

private lemma W3_abs_le (γ : ℝ) (h : ℝ → ℝ) (hγ1 : 1 < γ) (hγ2 : γ ≤ 11/10)
    {C θ : ℝ} (hC0 : 0 ≤ C) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu1 : |deriv (SinQ h) θ| ≤ C)
    (hsu2 : |Real.sin (2 * θ) * deriv (deriv (SinQ h)) θ| ≤ C) :
    ‖W3 γ h θ‖ ≤ C ^ 2 := by
  have hspos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hsnn : 0 ≤ Real.sin (2 * θ) := le_of_lt hspos
  have hs3 : (Real.sin (2 * θ)) ^ (3 - γ)
      = (Real.sin (2 * θ)) ^ (2 - γ) * Real.sin (2 * θ) := by
    rw [show (3 : ℝ) - γ = (2 - γ) + 1 by ring, Real.rpow_add hspos, Real.rpow_one]
  have hsp : (Real.sin (2 * θ)) ^ (2 - γ) ≤ 1 :=
    Real.rpow_le_one hsnn (Real.sin_le_one _) (by linarith)
  rw [show W3 γ h θ = (Real.sin (2 * θ)) ^ (2 - γ) * Real.cos (2 * θ)
      * deriv (SinQ h) θ * (Real.sin (2 * θ) * deriv (deriv (SinQ h)) θ) from by
    rw [W3, hs3]; ring]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hsnn _)]
  calc (Real.sin (2 * θ)) ^ (2 - γ) * |Real.cos (2 * θ)| * |deriv (SinQ h) θ|
        * |Real.sin (2 * θ) * deriv (deriv (SinQ h)) θ|
      ≤ 1 * 1 * C * C :=
        mul_le_mul (mul_le_mul (mul_le_mul hsp (Real.abs_cos_le_one _) (abs_nonneg _)
          zero_le_one) hu1 (abs_nonneg _) (by positivity)) hsu2 (abs_nonneg _) (by positivity)
    _ = C ^ 2 := by ring

/-- Integrability of the first two integrands of `DivSinIBPWeight`, which is exactly
`DivSinIntegrable_u1` with `α = 10(γ-1)`. -/
private theorem W12Integrable (γ : ℝ) (h : ℝ → ℝ) (hγ1 : 1 < γ) (hγ2 : γ ≤ 11/10)
    (hh : Work.Elliptic.SmoothSlice h) (hb : Work.Elliptic.SliceBdd h) :
    MeasureTheory.IntegrableOn (W1 γ h) Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (W2 γ h) Work.Spaces.Iθ MeasureTheory.volume := by
  have hα0 : 0 < 10 * (γ - 1) := by linarith
  have hα1 : 10 * (γ - 1) ≤ 1 := by linarith
  obtain ⟨-, h2, h3⟩ := Work.Elliptic.DivSinIntegrable_u1 (10 * (γ - 1)) hα0 hα1 h hh hb
  have hgam : Work.Spaces.gam (10 * (γ - 1)) = γ := by
    simp only [Work.Spaces.gam]; ring
  rw [hgam] at h2 h3
  exact ⟨h2, h3⟩

/-- Integrability of the difference integrand `WDfun` and of the third integrand `W3`. -/
private theorem WIntegrable (γ : ℝ) (h : ℝ → ℝ) (hγ1 : 1 < γ) (hγ2 : γ ≤ 11/10)
    (hh : Work.Elliptic.SmoothSlice h) (hb : Work.Elliptic.SliceBdd h) :
    MeasureTheory.IntegrableOn (WDfun γ h) Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (W3 γ h) Work.Spaces.Iθ MeasureTheory.volume := by
  obtain ⟨C, hC0, hae⟩ := Work.Elliptic.SliceBdd_ae_bounds h hh hb
  have hfin : volume Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ]; exact isCompact_Icc.measure_lt_top
  have hms2 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - γ)) :=
    (Real.measurable_sin.comp (measurable_id.const_mul 2)).pow_const _
  have hms3 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - γ)) :=
    (Real.measurable_sin.comp (measurable_id.const_mul 2)).pow_const _
  have hms4 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (4 - γ)) :=
    (Real.measurable_sin.comp (measurable_id.const_mul 2)).pow_const _
  have hmc : Measurable (fun θ : ℝ => Real.cos (2 * θ)) :=
    Real.measurable_cos.comp (measurable_id.const_mul 2)
  have hmc2 : Measurable (fun θ : ℝ => (Real.cos (2 * θ)) ^ 2) := hmc.pow_const 2
  have hmd : Measurable (fun θ : ℝ => deriv (SinQ h) θ) := measurable_deriv _
  have hmdd : Measurable (fun θ : ℝ => deriv (deriv (SinQ h)) θ) := measurable_deriv _
  have hmW1 : Measurable (W1 γ h) := by
    rw [show W1 γ h = fun θ : ℝ => (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
      * (deriv (SinQ h) θ) ^ 2 from rfl]
    exact (hmc2.mul hms2).mul (hmd.pow_const 2)
  have hmW2 : Measurable (W2 γ h) := by
    rw [show W2 γ h = fun θ : ℝ => (Real.sin (2 * θ)) ^ (4 - γ)
      * (deriv (SinQ h) θ) ^ 2 from rfl]
    exact hms4.mul (hmd.pow_const 2)
  have hmW3 : Measurable (W3 γ h) := by
    rw [show W3 γ h = fun θ : ℝ => (Real.sin (2 * θ)) ^ (3 - γ) * Real.cos (2 * θ)
      * deriv (SinQ h) θ * deriv (deriv (SinQ h)) θ from rfl]
    exact ((hms3.mul hmc).mul hmd).mul hmdd
  have hmWD : Measurable (WDfun γ h) := by
    rw [show WDfun γ h = fun θ : ℝ => W2 γ h θ - (3 - γ) * W1 γ h θ - W3 γ h θ from rfl]
    exact (hmW2.sub (measurable_const.mul hmW1)).sub hmW3
  have hbdW3 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ‖W3 γ h θ‖ ≤ C ^ 2 :=
    (hae.and Work.Elliptic.ae_mem_Ioo_Iθ).mono fun θ hθ =>
      W3_abs_le γ h hγ1 hγ2 hC0 hθ.2 hθ.1.2.2.2.1 hθ.1.2.2.2.2
  have hbdWD : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ‖WDfun γ h θ‖ ≤ 4 * C ^ 2 := by
    filter_upwards [hae, Work.Elliptic.ae_mem_Ioo_Iθ] with θ hbnd hθ
    have hu1 := hbnd.2.2.2.1
    have hsu2 := hbnd.2.2.2.2
    have h1 := W1mul_abs_le γ h hγ1 hγ2 hθ hu1
    have h2 := W2_abs_le γ h hγ2 hθ hu1
    have h3 := W3_abs_le γ h hγ1 hγ2 hC0 hθ hu1 hsu2
    calc ‖WDfun γ h θ‖ = ‖W2 γ h θ - (3 - γ) * W1 γ h θ - W3 γ h θ‖ := rfl
      _ ≤ ‖W2 γ h θ - (3 - γ) * W1 γ h θ‖ + ‖W3 γ h θ‖ := norm_sub_le _ _
      _ ≤ (‖W2 γ h θ‖ + ‖(3 - γ) * W1 γ h θ‖) + ‖W3 γ h θ‖ := by
            linarith [norm_sub_le (W2 γ h θ) ((3 - γ) * W1 γ h θ)]
      _ ≤ (C ^ 2 + 2 * C ^ 2) + C ^ 2 := by linarith
      _ = 4 * C ^ 2 := by ring
  exact ⟨IntegrableOn.of_bound hfin hmWD.aestronglyMeasurable (4 * C ^ 2) hbdWD,
    IntegrableOn.of_bound hfin hmW3.aestronglyMeasurable (C ^ 2) hbdW3⟩

/-- **Weighted integration by parts.**  For `1 < γ ≤ 11/10` and a smooth angular slice `h`
vanishing at `θ = 0, π/2` with bounded endpoint behaviour (`SliceBdd`),

  `(3 - γ) ∫ cos²(2θ) sin(2θ)^{2-γ} (u')² = ∫ sin(2θ)^{4-γ} (u')²
                                            - ∫ sin(2θ)^{3-γ} cos(2θ) u' u''`,

where `u = SinQ h = h / sin(2θ)`.  Both sides are produced by integrating the derivative of
the primitive `DivSinWP γ h = -(1/2) sin(2θ)^{3-γ} cos(2θ) (u')²`, which vanishes at both
endpoints of `Iθ`. -/
theorem DivSinIBPWeight (γ : ℝ) (h : ℝ → ℝ) (hγ1 : 1 < γ) (hγ2 : γ ≤ 11/10)
    (hh : Work.Elliptic.SmoothSlice h)
    (h0 : h 0 = 0) (hπ : h (Real.pi / 2) = 0) (hb : Work.Elliptic.SliceBdd h) :
    (3 - γ) * (∫ θ in Work.Spaces.Iθ,
        (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
          * (deriv (Work.Elliptic.SinQ h) θ) ^ 2)
      = (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (4 - γ) * (deriv (Work.Elliptic.SinQ h) θ) ^ 2)
        - (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (3 - γ) * Real.cos (2 * θ)
              * deriv (Work.Elliptic.SinQ h) θ * deriv (deriv (Work.Elliptic.SinQ h)) θ) := by
  obtain ⟨hW1, hW2⟩ := W12Integrable γ h hγ1 hγ2 hh hb
  obtain ⟨hWD, hW3⟩ := WIntegrable γ h hγ1 hγ2 hh hb
  have hγlt : γ < 3 := by linarith
  obtain ⟨htL, htR⟩ := WPTendsto γ h hγlt hh hb
  have hder : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (DivSinWP γ h) (WDfun γ h θ) θ :=
    fun θ hθ => WPHasDeriv γ h hh θ hθ
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hIntOn : MeasureTheory.IntegrableOn (WDfun γ h) (Set.uIcc 0 (Real.pi / 2)) volume := by
    rw [Set.uIcc_of_le hpi2.le]
    simpa [Work.Spaces.Iθ] using hWD
  have hIntI : IntervalIntegrable (WDfun γ h) volume 0 (Real.pi / 2) := hIntOn.intervalIntegrable
  have hFTC : ∫ θ in (0 : ℝ)..(Real.pi / 2), WDfun γ h θ = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi2 hder hIntI htL htR
    simpa using h
  have hZero : ∫ θ in Work.Spaces.Iθ, WDfun γ h θ = 0 := by
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl]
    rw [← Measure.restrict_congr_set
        (Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)),
      ← intervalIntegral.integral_of_le hpi2.le]
    exact hFTC
  have hsplit : ∫ θ in Work.Spaces.Iθ, WDfun γ h θ
      = (∫ θ in Work.Spaces.Iθ, W2 γ h θ) - (3 - γ) * (∫ θ in Work.Spaces.Iθ, W1 γ h θ)
        - (∫ θ in Work.Spaces.Iθ, W3 γ h θ) := by
    have h2 : MeasureTheory.IntegrableOn (fun θ => (3 - γ) * W1 γ h θ)
        Work.Spaces.Iθ volume := hW1.const_mul (3 - γ)
    have h1 : MeasureTheory.IntegrableOn (fun θ => W2 γ h θ - (3 - γ) * W1 γ h θ)
        Work.Spaces.Iθ volume := hW2.sub h2
    simp only [WDfun]
    rw [integral_sub h1 hW3, integral_sub hW2 h2, integral_const_mul]
  have key : (3 - γ) * (∫ θ in Work.Spaces.Iθ, W1 γ h θ)
      = (∫ θ in Work.Spaces.Iθ, W2 γ h θ) - (∫ θ in Work.Spaces.Iθ, W3 γ h θ) := by
    have hz : (∫ θ in Work.Spaces.Iθ, W2 γ h θ) - (3 - γ) * (∫ θ in Work.Spaces.Iθ, W1 γ h θ)
        - (∫ θ in Work.Spaces.Iθ, W3 γ h θ) = 0 := by
      rw [← hsplit]; exact hZero
    linarith
  simpa only [W1, W2, W3] using key

end Work.Elliptic
