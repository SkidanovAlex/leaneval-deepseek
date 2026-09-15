import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_residue
import Submission.Commons.Analysis.Complex.contour_shift_double_pole
import Submission.Commons.Analysis.Complex.curve_inv_sq_integrable
import Submission.Commons.Analysis.Complex.norm_cpow_gam_eq
import Submission.Commons.Analysis.Integral.integrable_of_log_le_lorentz
import Submission.Commons.Analysis.Integral.integrable_log_lorentz
import Submission.Commons.NumberTheory.Zeta.norm_riemannZeta_le_const_of_one_lt_re

open Complex MeasureTheory intervalIntegral Filter Set
open scoped Topology Interval

namespace Commons.NumberTheory.Zeta

noncomputable section

private def W (t₀ : ℝ) : ℂ := (1 : ℂ) + (t₀ : ℂ) * Complex.I
private lemma W_re (t₀ : ℝ) : (W t₀).re = 1 := by simp [W]
private lemma W_im (t₀ : ℝ) : (W t₀).im = t₀ := by simp [W]
private lemma W_ne_zero (t₀ : ℝ) : W t₀ ≠ 0 := by
  intro h; have := W_re t₀; rw [h] at this; norm_num at this
private lemma one_add_W_re (t₀ : ℝ) : 1 < (1 + W t₀).re := by
  rw [Complex.add_re, Complex.one_re, W_re]; norm_num
private lemma one_add_W_ne_one (t₀ : ℝ) : (1 + W t₀) ≠ 1 := by
  intro h; have := congrArg Complex.re h; simp [W] at this
private lemma W_continuous (t₀ : ℝ) : Continuous fun _ : ℝ => W t₀ := continuous_const

private def Zt (R : ℝ) (t : ℝ) : ℂ := ((1/Real.log R : ℝ):ℂ) + (t:ℂ)*Complex.I
private lemma Zt_re (R t : ℝ) : (Zt R t).re = 1/Real.log R := by simp [Zt]
private lemma Zt_im (R t : ℝ) : (Zt R t).im = t := by simp [Zt]
private lemma sq_norm_Zt (R t : ℝ) : ‖Zt R t‖^2 = (1/Real.log R)^2 + t^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [Zt]; ring
private lemma Zt_continuous (R : ℝ) : Continuous (Zt R) := by unfold Zt; fun_prop
private lemma Zt_ne {R : ℝ} (hR : 1 < R) (t : ℝ) : Zt R t ≠ 0 := by
  intro h
  have hre := Zt_re R t
  rw [h] at hre
  simp only [Complex.zero_re] at hre
  have hpos : 0 < (1/Real.log R : ℝ) := by have := Real.log_pos hR; positivity
  linarith

private def Gfun (f : ℂ → ℂ → ℂ) (R : ℝ) (t₀ : ℝ) (u : ℂ) : ℂ :=
  f u (W t₀)
    * (riemannZeta (1 + u + W t₀) * (riemannZeta (1 + u))⁻¹ * (riemannZeta (1 + W t₀))⁻¹)
    * (R : ℂ) ^ (u + W t₀) * (u ^ 2 * (W t₀) ^ 2)⁻¹

private def Hfun (f : ℂ → ℂ → ℂ) (R : ℝ) (t₀ : ℝ) (z : ℂ) : ℂ :=
  f z (W t₀) * riemannZeta (1 + z + W t₀) * (riemannZeta₁ (1 + z))⁻¹
    * (riemannZeta (1 + W t₀))⁻¹ * (R : ℂ) ^ (z + W t₀) * ((W t₀) ^ 2)⁻¹

private lemma Rpos_of_three_le {R : ℝ} (hR : 3 ≤ R) : 0 < R := by linarith
private lemma logRpos_of_three_le {R : ℝ} (hR : 3 ≤ R) : 0 < Real.log R :=
  Real.log_pos (by linarith)
private lemma cpos_of_three_le {R : ℝ} (hR : 3 ≤ R) : (0:ℝ) < 1/Real.log R := by
  have := logRpos_of_three_le hR; positivity
private lemma c_le_one_of_three_le {R : ℝ} (hR : 3 ≤ R) : (1/Real.log R : ℝ) ≤ 1 := by
  have hlogR : 0 < Real.log R := logRpos_of_three_le hR
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hle : Real.log 3 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hgt : 1 < Real.log 3 := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
  have h1 : (1:ℝ)/Real.log R ≤ 1/Real.log 3 := one_div_le_one_div_of_le hlog3 hle
  have h2 : (1:ℝ)/Real.log 3 ≤ 1 := by rw [div_le_one hlog3]; linarith
  linarith

private lemma betalog2_lt_one {β : ℝ} (hβ10 : β ≤ 1/10) : β / Real.log 2 < 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_one hlog2]; linarith [Real.log_two_gt_d9]

private lemma B_nonneg {β B : ℝ} (hβ : 0 < β) (f : ℂ → ℂ → ℂ) (t₀ : ℝ)
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B) : 0 ≤ B := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : -(β / Real.log (|(1:ℂ).im| + 2)) ≤ (1:ℂ).re := by
    simp only [Complex.one_re, Complex.one_im, abs_zero, zero_add]
    have : 0 ≤ β / Real.log 2 := div_nonneg hβ.le hlog2.le
    linarith
  have h2 : (1:ℂ).re ≤ 1 := by simp
  have h3 : -(β / Real.log (|(W t₀).im| + 2)) ≤ (W t₀).re := by
    rw [W_re, W_im]
    have hh : 0 ≤ β / Real.log (|t₀| + 2) := div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t₀]))
    linarith
  have h4 : (W t₀).re ≤ 1 := by rw [W_re]
  exact le_trans (norm_nonneg _) (hbound 1 (W t₀) h1 h2 h3 h4)

/-! ## Differentiability -/

private lemma differentiableAt_cpow_const'' {c w : ℂ} (hc : c ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => c ^ z) w :=
  (Complex.hasStrictDerivAt_const_cpow (Or.inl hc)).hasDerivAt.differentiableAt

private lemma differentiableAt_Gfun {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10)
    (f : ℂ → ℂ → ℂ) (t₀ : ℝ) (hR : (R : ℂ) ≠ 0)
    (hinv : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z)
    (hdiff1 : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => f u z') z) :
    ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 → z ≠ 0 →
      DifferentiableAt ℂ (Gfun f R t₀) z := by
  intro z hz1 hz2 hz0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpos : 0 < Real.log (|z.im| + 2) := Real.log_pos (by have := abs_nonneg z.im; linarith)
  have hlog2le : Real.log 2 ≤ Real.log (|z.im| + 2) :=
    Real.log_le_log (by norm_num) (by have := abs_nonneg z.im; linarith)
  have hratio : β / Real.log (|z.im| + 2) ≤ β / Real.log 2 :=
    div_le_div_of_nonneg_left hβ.le hlog2 hlog2le
  have hzre : -1 < z.re := by linarith [hz1, hratio, betalog2_lt_one hβ10]
  have hzW : 1 + z + W t₀ ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, W_re] at hre
    linarith
  have hWreg1z : -(β / Real.log (|(W t₀).im| + 2)) ≤ (W t₀).re := by
    rw [W_re, W_im]
    have h : 0 ≤ β / Real.log (|t₀| + 2) := div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t₀]))
    linarith
  have hWreg2z : (W t₀).re ≤ 1 := by rw [W_re]
  have hf1 : DifferentiableAt ℂ (fun u : ℂ => f u (W t₀)) z :=
    hdiff1 z (W t₀) hz1 hz2 hWreg1z hWreg2z
  have hζ : DifferentiableAt ℂ (fun u : ℂ => riemannZeta (1 + u + W t₀)) z :=
    (differentiableAt_riemannZeta hzW).comp z (by fun_prop)
  have hinvz : DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z := hinv z hz0 hz1 hz2
  have hconst : DifferentiableAt ℂ (fun _ : ℂ => (riemannZeta (1 + W t₀))⁻¹) z :=
    differentiableAt_const _
  have hcpow : DifferentiableAt ℂ (fun u : ℂ => (R : ℂ) ^ (u + W t₀)) z :=
    (differentiableAt_cpow_const'' hR).comp z (by fun_prop)
  have hinv2 : DifferentiableAt ℂ (fun u : ℂ => (u ^ 2 * (W t₀) ^ 2)⁻¹) z := by
    have hd : DifferentiableAt ℂ (fun u : ℂ => u ^ 2 * (W t₀) ^ 2) z := by fun_prop
    exact hd.inv (mul_ne_zero (pow_ne_zero 2 hz0) (pow_ne_zero 2 (W_ne_zero t₀)))
  show DifferentiableAt ℂ (fun u : ℂ => f u (W t₀)
      * (riemannZeta (1 + u + W t₀) * (riemannZeta (1 + u))⁻¹ * (riemannZeta (1 + W t₀))⁻¹)
      * (R : ℂ) ^ (u + W t₀) * (u ^ 2 * (W t₀) ^ 2)⁻¹) z
  exact ((hf1.mul ((hζ.mul hinvz).mul hconst)).mul hcpow).mul hinv2

/-! ## Residue -/

private lemma eventuallyEq_mul_Gfun (f : ℂ → ℂ → ℂ) (R : ℝ) (t₀ : ℝ) :
    (fun z : ℂ => z * Gfun f R t₀ z) =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℂ)] Hfun f R t₀ := by
  have hζinv : ∀ᶠ z : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ),
      (riemannZeta (1 + z))⁻¹ = z * (riemannZeta₁ (1 + z))⁻¹ := by
    have hcomp : Tendsto (fun z : ℂ => 1 + z) (nhdsWithin 0 ({0}ᶜ : Set ℂ))
        (nhdsWithin 1 ({1}ᶜ : Set ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun z : ℂ => (1:ℂ) + z) (nhds 0) (nhds 1) := by
          simpa using (tendsto_const_nhds.add tendsto_id :
            Tendsto (fun z : ℂ => (1:ℂ) + z) (nhds 0) (nhds ((1:ℂ) + 0)))
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
        intro h; exact hz (by linear_combination h)
    filter_upwards [hcomp.eventually inv_riemannZeta_eq_sub_mul] with z hz
    simpa only [add_sub_cancel_left] using hz
  filter_upwards [hζinv, self_mem_nhdsWithin] with z hz hz0
  have hz0' : z ≠ 0 := by simpa using hz0
  show z * Gfun f R t₀ z = Hfun f R t₀ z
  unfold Gfun Hfun
  rw [hz, mul_inv]
  field_simp [hz0', W_ne_zero t₀]

private lemma Hfun_zero (f : ℂ → ℂ → ℂ) (R : ℝ) (t₀ : ℝ) :
    Hfun f R t₀ 0 = f 0 (W t₀) * (R : ℂ) ^ (W t₀) * ((W t₀) ^ 2)⁻¹ := by
  have hne : riemannZeta (1 + W t₀) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (one_add_W_re t₀)
  unfold Hfun
  rw [show (1:ℂ) + 0 + W t₀ = 1 + W t₀ by ring, show (1:ℂ) + 0 = 1 by ring, zero_add,
      riemannZeta₁_one, inv_one, mul_one]
  field_simp [hne]

private lemma continuousAt_Hfun (f : ℂ → ℂ → ℂ) (R : ℝ) (t₀ : ℝ) (hR : (R:ℂ) ≠ 0)
    (hcont : Continuous (Function.uncurry f)) : ContinuousAt (Hfun f R t₀) 0 := by
  have h1 : Tendsto (fun z : ℂ => f z (W t₀)) (nhds 0) (nhds (f 0 (W t₀))) :=
    ((hcont.comp (continuous_id.prodMk continuous_const)).tendsto 0)
  have hlin : Tendsto (fun z : ℂ => (1:ℂ) + z + W t₀) (nhds 0) (nhds ((1:ℂ) + 0 + W t₀)) :=
    (((continuous_const : Continuous fun _ : ℂ => (1:ℂ)).add continuous_id).add continuous_const).tendsto 0
  have h2 : Tendsto (fun z : ℂ => riemannZeta (1 + z + W t₀)) (nhds 0)
      (nhds (riemannZeta (1 + 0 + W t₀))) :=
    ((differentiableAt_riemannZeta (by
        rw [show (1:ℂ) + 0 + W t₀ = 1 + W t₀ by ring]; exact one_add_W_ne_one t₀)).continuousAt).comp hlin
  have h3 : Tendsto (fun z : ℂ => (riemannZeta₁ (1 + z))⁻¹) (nhds 0)
      (nhds ((riemannZeta₁ (1 + 0))⁻¹)) := by
    have hζ1 : Tendsto (fun z : ℂ => riemannZeta₁ (1 + z)) (nhds 0) (nhds (riemannZeta₁ (1 + 0))) :=
      ((differentiable_riemannZeta₁.continuous.continuousAt).comp
        (((continuous_const : Continuous fun _ : ℂ => (1:ℂ)).add continuous_id).tendsto 0))
    refine hζ1.inv₀ ?_
    simp [riemannZeta₁_one]
  have h4 : Tendsto (fun z : ℂ => (R : ℂ) ^ (z + W t₀)) (nhds 0) (nhds ((R:ℂ) ^ (0 + W t₀))) := by
    have hcp : Tendsto (fun z : ℂ => (R:ℂ) ^ z) (nhds (0 + W t₀)) (nhds ((R:ℂ) ^ (0 + W t₀))) :=
      ((Complex.hasStrictDerivAt_const_cpow (Or.inl hR)).hasDerivAt.differentiableAt).continuousAt
    exact hcp.comp (((continuous_id.add continuous_const)).tendsto 0)
  have hconst : Tendsto (fun _ : ℂ => (riemannZeta (1 + W t₀))⁻¹) (nhds 0) (nhds ((riemannZeta (1 + W t₀))⁻¹)) :=
    tendsto_const_nhds
  have hconst2 : Tendsto (fun _ : ℂ => ((W t₀) ^ 2)⁻¹) (nhds 0) (nhds (((W t₀) ^ 2)⁻¹)) :=
    tendsto_const_nhds
  show Tendsto (Hfun f R t₀) (nhds 0) (nhds (Hfun f R t₀ 0))
  unfold Hfun
  exact ((((h1.mul h2).mul h3).mul hconst).mul h4).mul hconst2

private lemma tendsto_mul_Gfun (f : ℂ → ℂ → ℂ) (R : ℝ) (t₀ : ℝ) (hR : (R:ℂ) ≠ 0)
    (hcont : Continuous (Function.uncurry f)) :
    Tendsto (fun z : ℂ => z * Gfun f R t₀ z) (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (nhds (f 0 (W t₀) * (R : ℂ) ^ (W t₀) * ((W t₀) ^ 2)⁻¹)) := by
  have hcontH : Tendsto (Hfun f R t₀) (nhds 0) (nhds (Hfun f R t₀ 0)) :=
    continuousAt_Hfun f R t₀ hR hcont
  have h2 : Tendsto (Hfun f R t₀) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds (Hfun f R t₀ 0)) :=
    hcontH.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun z : ℂ => z * Gfun f R t₀ z) (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (nhds (Hfun f R t₀ 0)) := h2.congr' (eventuallyEq_mul_Gfun f R t₀).symm
  have hv : Hfun f R t₀ 0 = f 0 (W t₀) * (R : ℂ) ^ (W t₀) * ((W t₀) ^ 2)⁻¹ := Hfun_zero f R t₀
  rw [hv] at h3
  exact h3

/-! ## Pointwise bounds on the vertical line -/

private lemma norm_Zt_factors {β R B C₁ Cζ : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10)
    (hR : 3 ≤ R) (hC1 : 0 < C₁) (f : ℂ → ℂ → ℂ) (t₀ : ℝ)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hCζ : ∀ z : ℂ, 2 - β / Real.log 2 ≤ z.re → ‖riemannZeta z‖ ≤ Cζ) :
    ∀ t : ℝ,
      ‖f (Zt R t) (W t₀)‖ ≤ B ∧
      ‖riemannZeta (1 + Zt R t + W t₀)‖ ≤ Cζ ∧
      ‖(riemannZeta (1 + Zt R t))⁻¹‖ ≤ C₁ * (Real.log (2 + |t|) + 1) ∧
      ‖((R:ℂ) ^ (Zt R t + W t₀))‖ ≤ R ^ ((1/Real.log R : ℝ) + 1) ∧
      ‖((Zt R t)^2)⁻¹‖ ≤ ((1/Real.log R : ℝ)^2 + (t-0)^2)⁻¹ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcpos : (0:ℝ) < 1/Real.log R := cpos_of_three_le hR
  have hc1 : (1/Real.log R : ℝ) ≤ 1 := c_le_one_of_three_le hR
  have hRpos : (0:ℝ) < R := Rpos_of_three_le hR
  have hWreg1 : -(β / Real.log (|(W t₀).im| + 2)) ≤ (W t₀).re := by
    rw [W_re, W_im]
    have h : 0 ≤ β / Real.log (|t₀| + 2) := div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t₀]))
    linarith
  have hWreg2 : (W t₀).re ≤ 1 := by rw [W_re]
  intro t
  have hzt_re : (Zt R t).re = 1/Real.log R := Zt_re R t
  have hzt_im : (Zt R t).im = t := Zt_im R t
  have hzt_ne : Zt R t ≠ 0 := by
    intro h
    have hh := hzt_re
    rw [h] at hh
    simp only [Complex.zero_re] at hh
    linarith
  have hreg1 : -(β / Real.log (|(Zt R t).im| + 2)) ≤ (Zt R t).re := by
    rw [hzt_re]
    have h : 0 ≤ β / Real.log (|(Zt R t).im| + 2) :=
      div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg (Zt R t).im]))
    linarith
  have hreg2 : (Zt R t).re ≤ 1 := by rw [hzt_re]; exact hc1
  refine ⟨hbound (Zt R t) (W t₀) hreg1 hreg2 hWreg1 hWreg2, ?_, ?_, ?_, ?_⟩
  · apply hCζ
    simp only [Complex.add_re, Complex.one_re, hzt_re, W_re]
    have h : 0 < β / Real.log 2 := div_pos hβ hlog2
    linarith [hcpos]
  · have := hinvb (Zt R t) hzt_ne hreg1 hreg2
    rw [hzt_im] at this
    calc ‖(riemannZeta (1 + Zt R t))⁻¹‖ ≤ C₁ * (Real.log (|t| + 2) + 1) := this
      _ = C₁ * (Real.log (2 + |t|) + 1) := by rw [add_comm 2 |t|]
  · have hre : (Zt R t + W t₀).re = (1/Real.log R : ℝ) + 1 := by
      rw [Complex.add_re, hzt_re, W_re]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos, hre]
  · rw [norm_inv, norm_pow, sq_norm_Zt]
    simp

end
end Commons.NumberTheory.Zeta

namespace Commons.NumberTheory.Zeta
open Commons.Analysis.Complex

noncomputable section

private lemma continuous_riemannZeta_one_add_Zt {R : ℝ} (hR : 1 < R) :
    Continuous (fun t : ℝ => riemannZeta (1 + Zt R t)) := by
  rw [continuous_iff_continuousAt]; intro t
  have hne : (1 + Zt R t) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Zt_re] at hre
    have hpos : 0 < (1/Real.log R : ℝ) := by have := Real.log_pos hR; positivity
    linarith
  exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (1:ℂ) + Zt R t) (x := t)
    ((differentiableAt_riemannZeta hne).continuousAt)
    ((continuous_const.add (Zt_continuous R)).continuousAt)

private lemma continuous_riemannZeta_one_add_Zt_add_W {R : ℝ} (hR : 1 < R) (t₀ : ℝ) :
    Continuous (fun t : ℝ => riemannZeta (1 + Zt R t + W t₀)) := by
  rw [continuous_iff_continuousAt]; intro t
  have hne : (1 + Zt R t + W t₀) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Zt_re, W_re] at hre
    have hpos : 0 < (1/Real.log R : ℝ) := by have := Real.log_pos hR; positivity
    linarith
  exact ContinuousAt.comp (g := riemannZeta)
    (f := fun t : ℝ => (1:ℂ) + Zt R t + W t₀) (x := t)
    ((differentiableAt_riemannZeta hne).continuousAt)
    (((continuous_const.add (Zt_continuous R)).add continuous_const).continuousAt)

private lemma continuous_cpow_Zt {R : ℝ} (hR : 0 < R) (t₀ : ℝ) :
    Continuous (fun t : ℝ => (R:ℂ)^(Zt R t + W t₀)) := by
  rw [continuous_iff_continuousAt]; intro t
  have hRne : (R:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
  exact (((Complex.hasStrictDerivAt_const_cpow (Or.inl hRne)).hasDerivAt.differentiableAt).continuousAt).comp
    (((Zt_continuous R).add continuous_const).continuousAt)

private lemma continuous_inv_Zt_sq {R : ℝ} (hR : 1 < R) :
    Continuous (fun t : ℝ => ((Zt R t)^2)⁻¹) :=
  (((Zt_continuous R).pow 2).inv₀ (fun t => pow_ne_zero 2 (Zt_ne hR t)))

private lemma integrable_line {β R B C₁ Cζ : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10)
    (hR : 3 ≤ R) (hC1 : 0 < C₁) (hCζpos : 0 ≤ Cζ) (f : ℂ → ℂ → ℂ) (t₀ : ℝ)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hcont : Continuous (Function.uncurry f))
    (hCζ : ∀ z : ℂ, 2 - β / Real.log 2 ≤ z.re → ‖riemannZeta z‖ ≤ Cζ) :
    Integrable (fun t : ℝ => Gfun f R t₀ (Zt R t) * Complex.I) := by
  set Gg : ℝ → ℂ := fun t => (riemannZeta (1 + Zt R t))⁻¹ with hGg
  set Pr : ℝ → ℂ := fun t => f (Zt R t) (W t₀) * riemannZeta (1 + Zt R t + W t₀)
      * (riemannZeta (1 + W t₀))⁻¹ * (R:ℂ)^(Zt R t + W t₀) * ((W t₀)^2)⁻¹
      * ((Zt R t)^2)⁻¹ * Complex.I with hPr
  set K : ℝ := B * Cζ * ‖(riemannZeta (1 + W t₀))⁻¹‖ * R ^ ((1/Real.log R : ℝ) + 1)
      * ‖((W t₀)^2)⁻¹‖ with hKdef
  have hB : 0 ≤ B := B_nonneg hβ f t₀ hbound
  have hRpos : 0 < R := Rpos_of_three_le hR
  have hR1 : (1:ℝ) < R := by linarith
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB hCζpos) (norm_nonneg _))
      (le_of_lt (Real.rpow_pos_of_pos hRpos _))) (norm_nonneg _)
  have hprod : (fun t : ℝ => Gg t * Pr t) = (fun t : ℝ => Gfun f R t₀ (Zt R t) * Complex.I) := by
    funext t
    show Gg t * Pr t = Gfun f R t₀ (Zt R t) * Complex.I
    rw [hGg, hPr]
    simp only [Gfun]
    rw [mul_inv]
    ring
  have hGg_cont : Continuous Gg := by
    rw [hGg]
    refine (continuous_riemannZeta_one_add_Zt (by linarith : (1:ℝ) < R)).inv₀ (fun t => ?_)
    exact riemannZeta_ne_zero_of_one_lt_re (by
      simp only [Complex.add_re, Complex.one_re, Zt_re]
      linarith [cpos_of_three_le hR])
  have hPr_cont : Continuous Pr := by
    rw [hPr]
    have hf : Continuous (fun t : ℝ => f (Zt R t) (W t₀)) :=
      hcont.comp ((Zt_continuous R).prodMk continuous_const)
    have hζ1 := continuous_riemannZeta_one_add_Zt_add_W (by linarith : (1:ℝ) < R) t₀
    have hcp := continuous_cpow_Zt hRpos t₀
    have hz2 := continuous_inv_Zt_sq (by linarith : (1:ℝ) < R)
    exact (((((hf.mul hζ1).mul continuous_const).mul hcp).mul continuous_const).mul hz2).mul continuous_const
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Gg t * Pr t) volume :=
    (hGg_cont.mul hPr_cont).aestronglyMeasurable
  have hb : ∀ t : ℝ, ‖Gg t‖ ≤ C₁ * (Real.log (2 + |t|) + 1) := by
    intro t
    rw [hGg]
    exact (norm_Zt_factors hβ hβ10 hR hC1 f t₀ hinvb hbound hCζ t).2.2.1
  have hP : ∀ t : ℝ, ‖Pr t‖ ≤ K / ((1/Real.log R)^2 + (t-0)^2) := by
    intro t
    obtain ⟨h1, h2, _, h4, h5⟩ := norm_Zt_factors hβ hβ10 hR hC1 f t₀ hinvb hbound hCζ t
    rw [hPr, hKdef, div_eq_mul_inv]
    have hI : ‖Complex.I‖ = 1 := Complex.norm_I
    rw [show ‖f (Zt R t) (W t₀) * riemannZeta (1 + Zt R t + W t₀)
        * (riemannZeta (1 + W t₀))⁻¹ * (R:ℂ)^(Zt R t + W t₀) * ((W t₀)^2)⁻¹
        * ((Zt R t)^2)⁻¹ * Complex.I‖
      = ‖f (Zt R t) (W t₀)‖ * ‖riemannZeta (1 + Zt R t + W t₀)‖ * ‖(riemannZeta (1 + W t₀))⁻¹‖
        * ‖((R:ℂ)^(Zt R t + W t₀))‖ * ‖((W t₀)^2)⁻¹‖ * ‖((Zt R t)^2)⁻¹‖ * ‖Complex.I‖
      from by simp only [norm_mul], hI, mul_one]
    gcongr
  exact (Commons.Analysis.Integral.integrable_of_log_le_lorentz (g := Gg) (P := Pr)
    (a := 1/Real.log R) (b := 0) (C := C₁) (K := K) (cpos_of_three_le hR) hC1.le hK hmeas hb hP).congr
    (Filter.Eventually.of_forall (fun t => congrFun hprod t))

end
end Commons.NumberTheory.Zeta

namespace Commons.NumberTheory.Zeta
open Commons.Analysis.Complex

noncomputable section

private lemma norm_gam_factors {β R B C₁ Cζ : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10)
    (hR : 3 ≤ R) (hC1 : 0 < C₁) (f : ℂ → ℂ → ℂ) (t₀ : ℝ)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hCζ : ∀ z : ℂ, 2 - β / Real.log 2 ≤ z.re → ‖riemannZeta z‖ ≤ Cζ) :
    ∀ t : ℝ,
      ‖f (gam β t) (W t₀)‖ ≤ B ∧
      ‖riemannZeta (1 + gam β t + W t₀)‖ ≤ Cζ ∧
      ‖(riemannZeta (1 + gam β t))⁻¹‖ ≤ C₁ * (Real.log (2 + |t|) + 1) ∧
      ‖((R:ℂ) ^ (gam β t + W t₀))‖ ≤ R ∧
      ‖((gam β t)^2)⁻¹ * gamDot β t‖ ≤ curveConst β * (1 + t^2)⁻¹ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hRpos : 0 < R := Rpos_of_three_le hR
  have hWreg1 : -(β / Real.log (|(W t₀).im| + 2)) ≤ (W t₀).re := by
    rw [W_re, W_im]
    have h : 0 ≤ β / Real.log (|t₀| + 2) := div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t₀]))
    linarith
  have hWreg2 : (W t₀).re ≤ 1 := by rw [W_re]
  intro t
  have hgamre : (gam β t).re = -(β / Real.log (|t| + 2)) := gam_re β t
  have hgamim : (gam β t).im = t := gam_im β t
  have hreg1 : -(β / Real.log (|(gam β t).im| + 2)) ≤ (gam β t).re := by rw [hgamre, hgamim]
  have hreg2 : (gam β t).re ≤ 1 := by
    rw [hgamre]
    have h : 0 ≤ β / Real.log (|t| + 2) := div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t]))
    linarith
  have hgamne : gam β t ≠ 0 := gam_ne_zero hβ t
  refine ⟨hbound (gam β t) (W t₀) hreg1 hreg2 hWreg1 hWreg2, ?_, ?_, ?_, ?_⟩
  · apply hCζ
    simp only [Complex.add_re, Complex.one_re, hgamre, W_re]
    have h : β / Real.log (|t| + 2) ≤ β / Real.log 2 :=
      div_le_div_of_nonneg_left hβ.le hlog2 (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
    linarith
  · have := hinvb (gam β t) hgamne hreg1 hreg2
    rw [hgamim] at this
    calc ‖(riemannZeta (1 + gam β t))⁻¹‖ ≤ C₁ * (Real.log (|t| + 2) + 1) := this
      _ = C₁ * (Real.log (2 + |t|) + 1) := by rw [add_comm 2 |t|]
  · have hre : (gam β t + W t₀).re = -(β / Real.log (|t| + 2)) + 1 := by
      rw [Complex.add_re, hgamre, W_re]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos, hre]
    have hle1 : -(β / Real.log (|t| + 2)) ≤ 0 := by
      have h : 0 ≤ β / Real.log (|t| + 2) := div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t]))
      linarith
    calc R ^ (-(β / Real.log (|t| + 2)) + 1) ≤ R ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ R) (by linarith)
      _ = R := Real.rpow_one R
  · exact inv_sq_mul_gamDot_norm_le hβ t

private lemma integrable_gam {β R B C₁ Cζ : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10)
    (hR : 3 ≤ R) (hC1 : 0 < C₁) (hCζpos : 0 ≤ Cζ) (f : ℂ → ℂ → ℂ) (t₀ : ℝ)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hcont : Continuous (Function.uncurry f))
    (hCζ : ∀ z : ℂ, 2 - β / Real.log 2 ≤ z.re → ‖riemannZeta z‖ ≤ Cζ) :
    Integrable (fun t : ℝ => Gfun f R t₀ (gam β t) * gamDot β t) := by
  set Gg : ℝ → ℂ := fun t => (riemannZeta (1 + gam β t))⁻¹ with hGg
  set Q : ℝ → ℂ := fun t => ((gam β t)^2)⁻¹ * gamDot β t with hQ
  set Pr : ℝ → ℂ := fun t => f (gam β t) (W t₀) * riemannZeta (1 + gam β t + W t₀)
      * (riemannZeta (1 + W t₀))⁻¹ * (R:ℂ)^(gam β t + W t₀) * ((W t₀)^2)⁻¹ * Q t with hPr
  set K : ℝ := B * Cζ * ‖(riemannZeta (1 + W t₀))⁻¹‖ * R * ‖((W t₀)^2)⁻¹‖ * curveConst β with hKdef
  have hB : 0 ≤ B := B_nonneg hβ f t₀ hbound
  have hRpos : 0 < R := Rpos_of_three_le hR
  have hR1 : (1:ℝ) < R := by linarith
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB hCζpos) (norm_nonneg _))
      hRpos.le) (norm_nonneg _)) (curveConst_pos hβ).le
  have hprod : (fun t : ℝ => Gg t * Pr t) = (fun t : ℝ => Gfun f R t₀ (gam β t) * gamDot β t) := by
    funext t
    show Gg t * Pr t = Gfun f R t₀ (gam β t) * gamDot β t
    rw [hGg, hPr, hQ]
    simp only [Gfun]
    rw [mul_inv]
    ring
  have hζcont_gam : Continuous (fun t : ℝ => riemannZeta (1 + gam β t)) := by
    rw [continuous_iff_continuousAt]; intro t
    have hne : (1 + gam β t) ≠ 1 := by
      intro h; exact gam_ne_zero hβ t (by linear_combination h)
    exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => 1 + gam β t) (x := t)
      ((differentiableAt_riemannZeta hne).continuousAt)
      ((continuous_const.add (gam_continuous β)).continuousAt)
  have hGg_aesm : AEStronglyMeasurable Gg volume := by
    rw [hGg]
    exact (measurable_inv.comp hζcont_gam.measurable).aestronglyMeasurable
  have hPr_aesm : AEStronglyMeasurable Pr volume := by
    rw [hPr]
    have hf : Continuous (fun t : ℝ => f (gam β t) (W t₀)) :=
      hcont.comp ((gam_continuous β).prodMk continuous_const)
    have hζ1 : Continuous (fun t : ℝ => riemannZeta (1 + gam β t + W t₀)) := by
      rw [continuous_iff_continuousAt]; intro t
      have hne : (1 + gam β t + W t₀) ≠ 1 := by
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.add_re, Complex.one_re, gam_re, W_re] at hre
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hle : β / Real.log (|t| + 2) ≤ β / Real.log 2 :=
          div_le_div_of_nonneg_left hβ.le hlog2 (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
        linarith [betalog2_lt_one hβ10]
      exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => 1 + gam β t + W t₀) (x := t)
        ((differentiableAt_riemannZeta hne).continuousAt)
        (((continuous_const.add (gam_continuous β)).add continuous_const).continuousAt)
    have hcp : Continuous (fun t : ℝ => (R:ℂ)^(gam β t + W t₀)) := by
      rw [continuous_iff_continuousAt]; intro t
      have hRne : (R:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hRpos)
      exact ContinuousAt.comp (g := fun z : ℂ => (R:ℂ)^z) (f := fun t : ℝ => gam β t + W t₀) (x := t)
        (((Complex.hasStrictDerivAt_const_cpow (Or.inl hRne)).hasDerivAt.differentiableAt).continuousAt)
        (((gam_continuous β).add continuous_const).continuousAt)
    have hgam2 : Continuous (fun t : ℝ => ((gam β t)^2)⁻¹) :=
      ((gam_continuous β).pow 2).inv₀ (fun t => pow_ne_zero 2 (gam_ne_zero hβ t))
    have hgamDot_meas : AEStronglyMeasurable (fun t : ℝ => gamDot β t) volume :=
      (aestronglyMeasurable_deriv (gam β) volume).congr
        (by filter_upwards [ae_ne_zero] with t ht; rw [(hasDerivAt_gam ht).deriv])
    have hQ_aesm : AEStronglyMeasurable Q volume := by
      rw [hQ]
      exact hgam2.aestronglyMeasurable.mul hgamDot_meas
    exact (((((hf.aestronglyMeasurable.mul hζ1.aestronglyMeasurable).mul aestronglyMeasurable_const).mul
      hcp.aestronglyMeasurable).mul aestronglyMeasurable_const).mul hQ_aesm)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Gg t * Pr t) volume := hGg_aesm.mul hPr_aesm
  have hb : ∀ t : ℝ, ‖Gg t‖ ≤ C₁ * (Real.log (2 + |t|) + 1) := by
    intro t
    rw [hGg]
    exact (norm_gam_factors hβ hβ10 hR hC1 f t₀ hinvb hbound hCζ t).2.2.1
  have hP : ∀ t : ℝ, ‖Pr t‖ ≤ K / (1^2 + (t-0)^2) := by
    intro t
    obtain ⟨h1, h2, _, h4, h5⟩ := norm_gam_factors hβ hβ10 hR hC1 f t₀ hinvb hbound hCζ t
    have hnorm : ‖f (gam β t) (W t₀) * riemannZeta (1 + gam β t + W t₀)
        * (riemannZeta (1 + W t₀))⁻¹ * (R:ℂ)^(gam β t + W t₀) * ((W t₀)^2)⁻¹ * Q t‖
      = ‖f (gam β t) (W t₀)‖ * ‖riemannZeta (1 + gam β t + W t₀)‖ * ‖(riemannZeta (1 + W t₀))⁻¹‖
        * ‖((R:ℂ)^(gam β t + W t₀))‖ * ‖((W t₀)^2)⁻¹‖ * ‖Q t‖ := by simp only [norm_mul]
    have hq : ‖Q t‖ ≤ curveConst β * (1 + t^2)⁻¹ := by rw [hQ]; exact h5
    have hInn : (0:ℝ) ≤ ‖(riemannZeta (1 + W t₀))⁻¹‖ := norm_nonneg _
    have hWnn : (0:ℝ) ≤ ‖((W t₀)^2)⁻¹‖ := norm_nonneg _
    have hBC : (0:ℝ) ≤ B * Cζ := mul_nonneg hB hCζpos
    rw [hPr, hnorm, hQ, hKdef, div_eq_mul_inv]
    rw [show (1:ℝ)^2 + (t-0)^2 = 1 + t^2 by ring]
    calc ‖f (gam β t) (W t₀)‖ * ‖riemannZeta (1 + gam β t + W t₀)‖ * ‖(riemannZeta (1 + W t₀))⁻¹‖
          * ‖((R:ℂ)^(gam β t + W t₀))‖ * ‖((W t₀)^2)⁻¹‖ * ‖(gam β t ^ 2)⁻¹ * gamDot β t‖
        ≤ (B * Cζ) * ‖(riemannZeta (1 + W t₀))⁻¹‖ * R * ‖((W t₀)^2)⁻¹‖ * (curveConst β * (1 + t^2)⁻¹) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hB)
            (le_refl _) hInn hBC)
            h4 (norm_nonneg _) (mul_nonneg hBC hInn))
            (le_refl _) hWnn (mul_nonneg (mul_nonneg hBC hInn) (le_of_lt hRpos)))
            hq (norm_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg hBC hInn) (le_of_lt hRpos)) hWnn)
      _ = K * (1 + t^2)⁻¹ := by rw [hKdef]; ring
  exact (Commons.Analysis.Integral.integrable_of_log_le_lorentz (g := Gg) (P := Pr)
    (a := 1) (b := 0) (C := C₁) (K := K) one_pos hC1.le hK hmeas hb hP).congr
    (Filter.Eventually.of_forall (fun t => congrFun hprod t))

end
end Commons.NumberTheory.Zeta

namespace Commons.NumberTheory.Zeta
open Commons.Analysis.Complex

noncomputable section

private lemma integrable_deriv_form {β R B C₁ Cζ : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10)
    (hR : 3 ≤ R) (hC1 : 0 < C₁) (hCζpos : 0 ≤ Cζ) (f : ℂ → ℂ → ℂ) (t₀ : ℝ)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hcont : Continuous (Function.uncurry f))
    (hCζ : ∀ z : ℂ, 2 - β / Real.log 2 ≤ z.re → ‖riemannZeta z‖ ≤ Cζ) :
    Integrable (fun t : ℝ => Gfun f R t₀ (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t) := by
  refine (integrable_gam hβ hβ10 hR hC1 hCζpos f t₀ hinvb hbound hcont hCζ).congr ?_
  filter_upwards [ae_ne_zero] with t ht
  rw [deriv_phi_curve (β := β) ht]
  simp only [gam, phi]

private lemma tendsto_log_add_div_sq :
    Tendsto (fun T : ℝ => (Real.log (T + 2) + 1) * (T^2)⁻¹) atTop (nhds 0) := by
  have hshift : Tendsto (fun T : ℝ => T + 2) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_id
  have hlog : Tendsto (fun T : ℝ => Real.log (T + 2) / (T + 2)) atTop (nhds 0) := by
    have hbase : Tendsto (fun x : ℝ => Real.log x / (1 * x + 0)) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    refine (hbase.comp hshift).congr' ?_
    filter_upwards with T
    simp
  have hinv : Tendsto (fun T : ℝ => (1:ℝ) / (T + 2)) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hshift
  have hbase : Tendsto (fun T : ℝ => (Real.log (T + 2) + 1) / (T + 2)) atTop (nhds 0) := by
    have h := hlog.add hinv
    simp only [add_zero] at h
    refine h.congr' ?_
    filter_upwards with T
    exact (add_div (Real.log (T + 2)) 1 (T + 2)).symm
  refine squeeze_zero' ?_ ?_ hbase
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    have : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    positivity
  filter_upwards [eventually_ge_atTop (2:ℝ)] with T hT
  have hlog : 0 ≤ Real.log (T + 2) + 1 := by
    have : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith); linarith
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ hlog
  rw [inv_le_inv₀ (by positivity : (0:ℝ) < T^2) (by linarith : (0:ℝ) < T + 2)]
  nlinarith

private lemma norm_Gfun_horiz_le {β R B C₁ Cζ : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10)
    (hR : 3 ≤ R) (hC1 : 0 < C₁) (hCζpos : 0 ≤ Cζ) (f : ℂ → ℂ → ℂ) (t₀ : ℝ)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hCζ : ∀ z : ℂ, 2 - β / Real.log 2 ≤ z.re → ‖riemannZeta z‖ ≤ Cζ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 0 < T → ∀ s : ℝ, |s| = T → ∀ u : ℝ,
      -(β / Real.log (T + 2)) ≤ u → u ≤ 1/Real.log R →
      ‖Gfun f R t₀ ((u:ℂ) + (s:ℂ)*Complex.I)‖ ≤ M * (Real.log (T + 2) + 1) * (T^2)⁻¹ := by
  refine ⟨B * Cζ * C₁ * ‖(riemannZeta (1 + W t₀))⁻¹‖ * R ^ ((1/Real.log R : ℝ) + 1)
    * ‖((W t₀)^2)⁻¹‖, ?_, ?_⟩
  · have hB : 0 ≤ B := B_nonneg hβ f t₀ hbound
    have hRpos : 0 < R := Rpos_of_three_le hR
    have : (0:ℝ) ≤ R ^ ((1/Real.log R : ℝ) + 1) := le_of_lt (Real.rpow_pos_of_pos hRpos _)
    positivity
  · intro T hT s hs u hu1 hu2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hRpos : 0 < R := Rpos_of_three_le hR
    have hR1 : (1:ℝ) ≤ R := by linarith
    have hc1 : (1/Real.log R : ℝ) ≤ 1 := c_le_one_of_three_le hR
    have hTpos : 0 < T := hT
    have hsne : s ≠ 0 := by intro h; rw [h, abs_zero] at hs; linarith
    have hzre : (((u:ℂ) + (s:ℂ)*Complex.I)).re = u := by simp
    have hzim : (((u:ℂ) + (s:ℂ)*Complex.I)).im = s := by simp
    have hz1 : -(β / Real.log (|(((u:ℂ) + (s:ℂ)*Complex.I)).im| + 2)) ≤ (((u:ℂ) + (s:ℂ)*Complex.I)).re := by
      rw [hzre, hzim, hs]; exact hu1
    have hz2 : (((u:ℂ) + (s:ℂ)*Complex.I)).re ≤ 1 := by rw [hzre]; exact le_trans hu2 hc1
    have hzne : ((u:ℂ) + (s:ℂ)*Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.im h; rw [hzim] at this; simp at this; exact hsne this
    have hWreg1 : -(β / Real.log (|(W t₀).im| + 2)) ≤ (W t₀).re := by
      rw [W_re, W_im]
      have h : 0 ≤ β / Real.log (|t₀| + 2) := div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t₀]))
      linarith
    have hWreg2 : (W t₀).re ≤ 1 := by rw [W_re]
    have hf1 : ‖f ((u:ℂ) + (s:ℂ)*Complex.I) (W t₀)‖ ≤ B :=
      hbound _ _ hz1 hz2 hWreg1 hWreg2
    have hf2 : ‖riemannZeta (1 + ((u:ℂ) + (s:ℂ)*Complex.I) + W t₀)‖ ≤ Cζ := by
      apply hCζ
      simp only [Complex.add_re, Complex.one_re, hzre, W_re]
      have hle : β / Real.log (|s| + 2) ≤ β / Real.log 2 :=
        div_le_div_of_nonneg_left hβ.le hlog2 (Real.log_le_log (by norm_num) (by rw [hs]; linarith))
      have : β / Real.log (T + 2) ≤ β / Real.log 2 := by rw [hs] at hle; exact hle
      linarith
    have hf3 : ‖(riemannZeta (1 + ((u:ℂ) + (s:ℂ)*Complex.I)))⁻¹‖ ≤ C₁ * (Real.log (T + 2) + 1) := by
      have h := hinvb _ hzne hz1 hz2
      rw [hzim, hs] at h
      exact h
    have hf4 : ‖((R:ℂ)^(((u:ℂ) + (s:ℂ)*Complex.I) + W t₀))‖ ≤ R ^ ((1/Real.log R : ℝ) + 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos]
      have hre : (((u:ℂ) + (s:ℂ)*Complex.I) + W t₀).re = u + 1 := by simp [hzre, W_re]
      rw [hre]
      exact Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
    have hf5 : ‖((((u:ℂ) + (s:ℂ)*Complex.I))^2)⁻¹‖ ≤ (T^2)⁻¹ := by
      rw [norm_inv, norm_pow]
      rw [inv_le_inv₀ (by positivity : (0:ℝ) < ‖((u:ℂ)+(s:ℂ)*Complex.I)‖^2) (by positivity : (0:ℝ) < T^2)]
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [hzre, hzim]
      nlinarith [sq_nonneg u, sq_abs s, abs_nonneg s]
    have hInn : (0:ℝ) ≤ ‖(riemannZeta (1 + W t₀))⁻¹‖ := norm_nonneg _
    have hWnn : (0:ℝ) ≤ ‖((W t₀)^2)⁻¹‖ := norm_nonneg _
    have hBnn : (0:ℝ) ≤ B := B_nonneg hβ f t₀ hbound
    have hBC : (0:ℝ) ≤ B * Cζ := mul_nonneg hBnn hCζpos
    have hClog : (0:ℝ) ≤ C₁ * (Real.log (T + 2) + 1) := by
      have : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith); positivity
    have hRcnn : (0:ℝ) ≤ R ^ ((1/Real.log R : ℝ) + 1) := le_of_lt (Real.rpow_pos_of_pos hRpos _)
    have hTinv : (0:ℝ) ≤ (T^2)⁻¹ := by positivity
    have hnorm : ‖Gfun f R t₀ ((u:ℂ) + (s:ℂ)*Complex.I)‖
        = ‖f ((u:ℂ) + (s:ℂ)*Complex.I) (W t₀)‖ * ‖riemannZeta (1 + ((u:ℂ) + (s:ℂ)*Complex.I) + W t₀)‖
          * ‖(riemannZeta (1 + ((u:ℂ) + (s:ℂ)*Complex.I)))⁻¹‖ * ‖(riemannZeta (1 + W t₀))⁻¹‖
          * ‖((R:ℂ)^(((u:ℂ) + (s:ℂ)*Complex.I) + W t₀))‖ * ‖((((u:ℂ) + (s:ℂ)*Complex.I))^2)⁻¹‖
          * ‖((W t₀)^2)⁻¹‖ := by
      simp only [Gfun, mul_inv, norm_mul]; ring
    rw [hnorm]
    calc ‖f ((u:ℂ) + (s:ℂ)*Complex.I) (W t₀)‖ * ‖riemannZeta (1 + ((u:ℂ) + (s:ℂ)*Complex.I) + W t₀)‖
          * ‖(riemannZeta (1 + ((u:ℂ) + (s:ℂ)*Complex.I)))⁻¹‖ * ‖(riemannZeta (1 + W t₀))⁻¹‖
          * ‖((R:ℂ)^(((u:ℂ) + (s:ℂ)*Complex.I) + W t₀))‖ * ‖((((u:ℂ) + (s:ℂ)*Complex.I))^2)⁻¹‖
          * ‖((W t₀)^2)⁻¹‖
        = (‖f ((u:ℂ) + (s:ℂ)*Complex.I) (W t₀)‖ * ‖riemannZeta (1 + ((u:ℂ) + (s:ℂ)*Complex.I) + W t₀)‖)
          * ‖(riemannZeta (1 + ((u:ℂ) + (s:ℂ)*Complex.I)))⁻¹‖ * ‖(riemannZeta (1 + W t₀))⁻¹‖
          * ‖((R:ℂ)^(((u:ℂ) + (s:ℂ)*Complex.I) + W t₀))‖
          * (‖((((u:ℂ) + (s:ℂ)*Complex.I))^2)⁻¹‖ * ‖((W t₀)^2)⁻¹‖) := by ring
      _ ≤ (B * Cζ) * (C₁ * (Real.log (T + 2) + 1)) * ‖(riemannZeta (1 + W t₀))⁻¹‖
            * R ^ ((1/Real.log R : ℝ) + 1) * ((T^2)⁻¹ * ‖((W t₀)^2)⁻¹‖) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul
            (mul_le_mul hf1 hf2 (norm_nonneg _) hBnn) hf3 (norm_nonneg _) hBC)
            (le_refl _) hInn (mul_nonneg hBC hClog))
            hf4 (norm_nonneg _) (mul_nonneg (mul_nonneg hBC hClog) hInn))
            (mul_le_mul hf5 (le_refl _) hWnn hTinv) (mul_nonneg (norm_nonneg _) hWnn)
            (mul_nonneg (mul_nonneg (mul_nonneg hBC hClog) hInn) hRcnn)
      _ = (B * Cζ * C₁ * ‖(riemannZeta (1 + W t₀))⁻¹‖ * R ^ ((1/Real.log R : ℝ) + 1)
            * ‖((W t₀)^2)⁻¹‖) * (Real.log (T + 2) + 1) * (T^2)⁻¹ := by ring

private lemma horiz_tendsto {β R B C₁ Cζ : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1/10)
    (hR : 3 ≤ R) (hC1 : 0 < C₁) (hCζpos : 0 ≤ Cζ) (f : ℂ → ℂ → ℂ) (t₀ : ℝ)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hCζ : ∀ z : ℂ, 2 - β / Real.log 2 ≤ z.re → ‖riemannZeta z‖ ≤ Cζ) :
    Tendsto (fun T : ℝ =>
      (∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) + (T:ℂ)*Complex.I))
        - (∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) - (T:ℂ)*Complex.I)))
      atTop (nhds 0) := by
  obtain ⟨M, hM, hpt⟩ := norm_Gfun_horiz_le hβ hβ10 hR hC1 hCζpos f t₀ hinvb hbound hCζ
  have hβpos : 0 < β := hβ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLnn : 0 ≤ 2 * (M * (1/Real.log R + β / Real.log 2)) := by
    have h1 : 0 ≤ (1/Real.log R : ℝ) := le_of_lt (cpos_of_three_le hR)
    have h2 : 0 ≤ β / Real.log 2 := div_nonneg hβ.le hlog2.le
    positivity
  have hbd : ∀ᶠ T : ℝ in atTop,
      ‖(∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) + (T:ℂ)*Complex.I))
        - (∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) - (T:ℂ)*Complex.I))‖
      ≤ (2 * (M * (1/Real.log R + β / Real.log 2))) * ((Real.log (T + 2) + 1) * (T^2)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have hcpos : 0 < (1/Real.log R : ℝ) := cpos_of_three_le hR
    have hac : -(β / Real.log (T + 2)) ≤ (1/Real.log R : ℝ) := by
      have : 0 < β / Real.log (T + 2) := div_pos hβ (Real.log_pos (by linarith))
      linarith
    have hlen : |(1/Real.log R : ℝ) - (-(β / Real.log (T + 2)))| ≤ 1/Real.log R + β / Real.log 2 := by
      have h1 : Real.log 2 ≤ Real.log (T + 2) := Real.log_le_log (by norm_num) (by linarith)
      have h2 : β / Real.log (T + 2) ≤ β / Real.log 2 :=
        div_le_div_of_nonneg_left hβ.le hlog2 h1
      have h3 : 0 < β / Real.log (T + 2) := div_pos hβ (Real.log_pos (by linarith))
      have h4 : (1/Real.log R : ℝ) - (-(β / Real.log (T + 2))) = 1/Real.log R + β / Real.log (T+2) := by ring
      rw [h4, abs_of_pos (by linarith)]
      linarith
    have hptT : ∀ (s : ℝ), |s| = T → ∀ u ∈ Set.uIoc (-(β / Real.log (T + 2))) (1/Real.log R),
        ‖Gfun f R t₀ ((u:ℂ) + (s:ℂ)*Complex.I)‖ ≤ M * (Real.log (T + 2) + 1) * (T^2)⁻¹ := by
      intro s hs u hu
      have ha : -(β / Real.log (T+2)) < u := by
        have hh := hu.1; rwa [min_eq_left hac] at hh
      have huc : u ≤ 1/Real.log R := by
        have hh := hu.2; rwa [max_eq_right hac] at hh
      exact hpt T hT s hs u ha.le huc
    have hMnn : 0 ≤ M * (Real.log (T + 2) + 1) * (T^2)⁻¹ := by
      have h1 : 0 ≤ Real.log (T + 2) + 1 := by
        have := Real.log_nonneg (by linarith : (1:ℝ) ≤ T + 2); linarith
      exact mul_nonneg (mul_nonneg hM h1) (by positivity)
    have hb1 : ‖∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) + (T:ℂ)*Complex.I)‖
        ≤ M * (Real.log (T+2)+1) * (T^2)⁻¹ * (1/Real.log R + β / Real.log 2) := by
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun u hu => hptT T (abs_of_pos hT) u hu)) ?_
      exact mul_le_mul_of_nonneg_left hlen hMnn
    have hb2 : ‖∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) - (T:ℂ)*Complex.I)‖
        ≤ M * (Real.log (T+2)+1) * (T^2)⁻¹ * (1/Real.log R + β / Real.log 2) := by
      have hI : (∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) - (T:ℂ)*Complex.I))
          = ∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) + ((-T:ℝ):ℂ)*Complex.I) := by
        refine intervalIntegral.integral_congr (fun u _ => ?_)
        congr 1
        push_cast; ring
      rw [hI]
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun u hu => hptT (-T) (by rw [abs_neg, abs_of_pos hT]) u hu)) ?_
      exact mul_le_mul_of_nonneg_left hlen hMnn
    calc ‖(∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) + (T:ℂ)*Complex.I))
        - (∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) - (T:ℂ)*Complex.I))‖
        ≤ ‖(∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) + (T:ℂ)*Complex.I))‖
          + ‖(∫ u in (-(β / Real.log (T + 2)))..(1/Real.log R), Gfun f R t₀ ((u:ℂ) - (T:ℂ)*Complex.I))‖ :=
          norm_sub_le _ _
      _ ≤ M * (Real.log (T+2)+1) * (T^2)⁻¹ * (1/Real.log R + β / Real.log 2)
          + M * (Real.log (T+2)+1) * (T^2)⁻¹ * (1/Real.log R + β / Real.log 2) :=
          add_le_add hb1 hb2
      _ = (2 * (M * (1/Real.log R + β / Real.log 2))) * ((Real.log (T + 2) + 1) * (T^2)⁻¹) := by ring
  have hlim : Tendsto (fun T : ℝ => (2 * (M * (1/Real.log R + β / Real.log 2)))
      * ((Real.log (T + 2) + 1) * (T^2)⁻¹)) atTop (nhds 0) := by
    have := tendsto_log_add_div_sq.const_mul (2 * (M * (1/Real.log R + β / Real.log 2)))
    simpa using this
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _)) hbd hlim)

end
end Commons.NumberTheory.Zeta

namespace Commons.NumberTheory.Zeta
open Commons.Analysis.Complex

noncomputable section

set_option maxHeartbeats 1000000

theorem greenTao_single_pole_shift_Gamma2 {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B C₁ : ℝ) (hC1 : 0 < C₁)
    (hinv : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hdiff1 : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => f u z') z)
    (hcont : Continuous (Function.uncurry f))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (t₀ : ℝ) :
    (∫ t : ℝ, (fun u : ℂ => f u ((1 : ℂ) + (t₀ : ℂ) * Complex.I)
        * (riemannZeta (1 + u + ((1 : ℂ) + (t₀ : ℂ) * Complex.I))
            / (riemannZeta (1 + u) * riemannZeta (1 + ((1 : ℂ) + (t₀ : ℂ) * Complex.I))))
        * (R : ℂ) ^ (u + ((1 : ℂ) + (t₀ : ℂ) * Complex.I))
        / (u ^ 2 * (((1 : ℂ) + (t₀ : ℂ) * Complex.I)) ^ 2))
        (((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      = (∫ t : ℝ, (fun u : ℂ => f u ((1 : ℂ) + (t₀ : ℂ) * Complex.I)
        * (riemannZeta (1 + u + ((1 : ℂ) + (t₀ : ℂ) * Complex.I))
            / (riemannZeta (1 + u) * riemannZeta (1 + ((1 : ℂ) + (t₀ : ℂ) * Complex.I))))
        * (R : ℂ) ^ (u + ((1 : ℂ) + (t₀ : ℂ) * Complex.I))
        / (u ^ 2 * (((1 : ℂ) + (t₀ : ℂ) * Complex.I)) ^ 2))
        (Commons.Analysis.Complex.gam β t) * Commons.Analysis.Complex.gamDot β t)
        + 2 * (Real.pi : ℂ) * Complex.I *
          (f 0 ((1 : ℂ) + (t₀ : ℂ) * Complex.I) * (R : ℂ) ^ ((1 : ℂ) + (t₀ : ℂ) * Complex.I)
            / ((1 : ℂ) + (t₀ : ℂ) * Complex.I) ^ 2) := by
  have hRpos : 0 < R := by linarith
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hRpos)
  have hcpos : (0:ℝ) < 1/Real.log R := cpos_of_three_le hR
  have hc1 : (1/Real.log R : ℝ) ≤ 1 := c_le_one_of_three_le hR
  obtain ⟨Cζ, hCζpos, hCζ⟩ := norm_riemannZeta_le_const_of_one_lt_re
      (σ := 2 - β / Real.log 2) (by have := betalog2_lt_one hβ10; linarith)
  have hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1/Real.log R → z ≠ 0 →
      DifferentiableAt ℂ (Gfun f R t₀) z :=
    fun z h1 h2 h3 => differentiableAt_Gfun hβ hβ10 f t₀ hRne hinv hdiff1 z h1 (le_trans h2 hc1) h3
  have hres := tendsto_mul_Gfun f R t₀ hRne hcont
  have hCζnn : 0 ≤ Cζ := hCζpos.le
  have hint1 := integrable_line hβ hβ10 hR hC1 hCζnn f t₀ hinvb hbound hcont hCζ
  have hint0 := integrable_deriv_form hβ hβ10 hR hC1 hCζnn f t₀ hinvb hbound hcont hCζ
  have hhoriz := horiz_tendsto hβ hβ10 hR hC1 hCζnn f t₀ hinvb hbound hCζ
  have key := contour_shift_residue (β := β) (c := 1/Real.log R)
      hβ hcpos (Gfun f R t₀) (f 0 (W t₀) * (R : ℂ) ^ (W t₀) * ((W t₀) ^ 2)⁻¹)
      hdiff hres hint1 hint0 hhoriz
  have hconv1 : (∫ t : ℝ, Gfun f R t₀ (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
      = ∫ t : ℝ, Gfun f R t₀ (gam β t) * gamDot β t := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with t ht
    rw [deriv_phi_curve (β := β) ht]
    simp only [gam, phi]
  have hG : (fun u : ℂ => f u ((1 : ℂ) + (t₀ : ℂ) * Complex.I)
        * (riemannZeta (1 + u + ((1 : ℂ) + (t₀ : ℂ) * Complex.I))
            / (riemannZeta (1 + u) * riemannZeta (1 + ((1 : ℂ) + (t₀ : ℂ) * Complex.I))))
        * (R : ℂ) ^ (u + ((1 : ℂ) + (t₀ : ℂ) * Complex.I))
        / (u ^ 2 * (((1 : ℂ) + (t₀ : ℂ) * Complex.I)) ^ 2)) = Gfun f R t₀ := by
    funext u
    simp only [Gfun, W]
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [hG, key, hconv1]
  simp only [W]
  rw [div_eq_mul_inv]

end
end Commons.NumberTheory.Zeta
