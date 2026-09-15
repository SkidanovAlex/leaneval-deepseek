import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_residue_multi
import Submission.Commons.Analysis.Complex.curve_inv_sq_integrable
import Submission.Commons.Analysis.Complex.contour_shift_double_pole
import Submission.Commons.NumberTheory.Zeta.zeta_crude_strip_bound
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_log_one_le_re
import Submission.Commons.NumberTheory.Diophantine.three_mod_four_lseries_continuation
import Submission.Commons.Analysis.Integral.integrable_of_log_le_lorentz
import Submission.Commons.NumberTheory.Zeta.norm_riemannZeta_le_const_of_one_lt_re
import Submission.Commons.NumberTheory.Zeta.riemannZeta_inv_differentiableAt_imp_ne_zero
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Zeta

open Complex MeasureTheory Filter Topology Set
open scoped Topology Interval

noncomputable section

private lemma betalog_lt_one {β : ℝ} (hβ10 : β ≤ 1 / 10) (t : ℝ) : β / Real.log (|t| + 2) < 1 := by
  have hlog2 : (1:ℝ)/2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hpos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
  rw [div_lt_one hpos]
  linarith

private lemma mul_riemannZeta_one_add (w : ℂ) (hw : w ≠ 0) :
    w * riemannZeta (1 + w) = riemannZeta₁ (1 + w) := by
  have hs : (1 + w : ℂ) ≠ 1 := by intro h; exact hw (by linear_combination h)
  have hstep : ((1 + w : ℂ) - 1) = w := by ring
  rw [riemannZeta_eq_inv_sub_mul hs, hstep, ← mul_assoc, mul_inv_cancel₀ hw, one_mul]

private lemma tendsto_mul_riemannZeta_one_add :
    Tendsto (fun w : ℂ => w * riemannZeta (1 + w)) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 1) := by
  have heq : (fun w : ℂ => w * riemannZeta (1 + w)) =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℂ)]
      (fun w : ℂ => riemannZeta₁ (1 + w)) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact mul_riemannZeta_one_add w (by simpa using hw)
  have hcont : Tendsto (fun w : ℂ => riemannZeta₁ (1 + w)) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 1) := by
    have h : Tendsto (fun w : ℂ => riemannZeta₁ (1 + w)) (nhds (0:ℂ)) (nhds (riemannZeta₁ (1+0))) :=
      ((differentiable_riemannZeta₁.continuous.continuousAt).comp
        ((continuous_const.add continuous_id).continuousAt)).tendsto
    have h' : Tendsto (fun w : ℂ => riemannZeta₁ (1 + w)) (nhds (0:ℂ)) (nhds 1) := by
      simpa [riemannZeta₁_one] using h
    exact h'.mono_left nhdsWithin_le_nhds
  exact hcont.congr' heq.symm

private lemma norm_riemannZeta_abs_im (σ τ : ℝ) :
    ‖riemannZeta (((σ : ℝ) : ℂ) + Complex.I * ((|τ| : ℝ) : ℂ))‖
      = ‖riemannZeta (((σ : ℝ) : ℂ) + Complex.I * (τ : ℂ))‖ := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · have hτ' : |τ| = -τ := abs_of_neg hτ
    rw [hτ']
    have hconj : ((σ : ℂ) + Complex.I * ((-τ : ℝ) : ℂ))
        = starRingEnd ℂ ((σ : ℂ) + Complex.I * (τ : ℂ)) := by
      apply Complex.ext <;> simp
    rw [hconj, riemannZeta_conj]
    simp
  · rw [abs_of_nonneg hτ]

private lemma zeta_near_line_bound : ∃ C : ℝ, 0 < C ∧ ∀ δ τ : ℝ, 0 < δ → δ ≤ 1/2 → 3 ≤ |τ| →
    ‖riemannZeta (((1 - δ : ℝ) : ℂ) + Complex.I * (τ : ℂ))‖ ≤ C * (1 / δ) * (|τ| + 3) ^ δ := by
  obtain ⟨C, hCpos, hC⟩ := zeta_strip_conv_bound
  refine ⟨C, hCpos, ?_⟩
  intro δ τ hδ0 hδ1 hτ
  have hσlo : (1/2 : ℝ) ≤ 1 - δ := by linarith
  have hσlt : (1 - δ : ℝ) < 1 := by linarith
  have hb := hC (1 - δ) |τ| hσlo hσlt hτ
  rw [norm_riemannZeta_abs_im (1 - δ) τ] at hb
  simpa only [show (1:ℝ) - (1 - δ) = δ by ring] using hb

private lemma differentiableAt_cpow_const_v3 {c w : ℂ} (hc : c ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => c ^ z) w :=
  (Complex.hasStrictDerivAt_const_cpow (Or.inl hc)).hasDerivAt.differentiableAt

/-- **Green–Tao, two-pole shift from `Γ₂` to `Γ₀`** (step 4 of Green–Tao Lemma 10.4, `m = 1`).
Fix `z₀ = gam β t₀` on `Γ₀`.  Shifting the vertical line `Re w = 1` down to `Γ₀` crosses exactly
two simple poles, `w = 0` and `w = -z₀`, with residues `f z₀ 0 * R^z₀ / z₀^2` and
`f z₀ (-z₀) / (ζ(1+z₀) ζ(1-z₀) z₀^4)`.  Apply
`Commons.Analysis.Complex.contour_shift_residue_multi` with `c = 1` and `S = {0, -z₀}`
(and `i w = gam β t`, `i dw = gamDot β t dw` on the curve).
The hypotheses `hznumσ`, `hznumγ` are exactly what is needed for the two integrability
requirements (`hint1`, `hint0`) of the multi-pole shift: on the line `Re w = 1` the argument
`1+z₀+w` has real part `≥ 2 - β/log 2 > 1` so `ζ` is bounded there, while on the curve the sharp
bound of power `1/2` makes `(|t₀|+|t|+3)^{1/2}(log(|t|+2)+1)/(1+t^2)` integrable.
A previous version of this statement used the (too weak, hence useless) exponent `4`. -/
theorem greenTao_two_pole_shift_v4 {β R : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (hR : 3 ≤ R)
    (f : ℂ → ℂ → ℂ) (B C₁ C₂ C₃ : ℝ) (hC1 : 0 < C₁) (hC2 : 0 < C₂) (hC3 : 0 < C₃)
    (hinv : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hdiff2 : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => f z u) z')
    (hcont : Continuous (Function.uncurry f))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (t₀ : ℝ)
    (hznumσ : ∀ t : ℝ, ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t₀
        + ((1 : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C₂ * (|t₀| + |t| + 3) ^ ((1:ℝ)/2))
    (hznumγ : ∀ t : ℝ, ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t₀
        + Commons.Analysis.Complex.gam β t)‖ ≤ C₃ * (|t₀| + |t| + 3) ^ ((1:ℝ)/2)) :
    (∫ t : ℝ, (fun w : ℂ => f (Commons.Analysis.Complex.gam β t₀) w
        * (riemannZeta (1 + Commons.Analysis.Complex.gam β t₀ + w)
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β t₀) * riemannZeta (1 + w)))
        * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t₀ + w)
        / ((Commons.Analysis.Complex.gam β t₀) ^ 2 * w ^ 2))
        ((1 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      = (∫ t : ℝ, (fun w : ℂ => f (Commons.Analysis.Complex.gam β t₀) w
        * (riemannZeta (1 + Commons.Analysis.Complex.gam β t₀ + w)
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β t₀) * riemannZeta (1 + w)))
        * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t₀ + w)
        / ((Commons.Analysis.Complex.gam β t₀) ^ 2 * w ^ 2))
        (Commons.Analysis.Complex.gam β t) * Commons.Analysis.Complex.gamDot β t)
        + 2 * (Real.pi : ℂ) * Complex.I *
          (f (Commons.Analysis.Complex.gam β t₀) 0 * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t₀)
              / (Commons.Analysis.Complex.gam β t₀) ^ 2
            + f (Commons.Analysis.Complex.gam β t₀) (-(Commons.Analysis.Complex.gam β t₀))
              / (riemannZeta (1 + Commons.Analysis.Complex.gam β t₀)
                  * riemannZeta (1 - Commons.Analysis.Complex.gam β t₀)
                  * (Commons.Analysis.Complex.gam β t₀) ^ 4)) := by
  set z₀ : ℂ := Commons.Analysis.Complex.gam β t₀ with hz₀
  set g : ℂ → ℂ := fun w => f z₀ w * (riemannZeta (1 + z₀ + w) / (riemannZeta (1 + z₀) * riemannZeta (1 + w))) * (R : ℂ) ^ (z₀ + w) / (z₀ ^ 2 * w ^ 2) with hg
  set S : Finset ℂ := {0, -z₀} with hSfin
  set res : ℂ → ℂ := fun s => if s = 0 then f z₀ 0 * (R : ℂ) ^ z₀ / z₀ ^ 2 else if s = -z₀ then f z₀ (-z₀) / (riemannZeta (1 + z₀) * riemannZeta (1 - z₀) * z₀ ^ 4) else 0 with hresdef
  -- basic facts
  have hz₀ne : z₀ ≠ 0 := by rw [hz₀]; exact Commons.Analysis.Complex.gam_ne_zero hβ t₀
  have hz₀re : z₀.re = -(β / Real.log (|t₀| + 2)) := by
    rw [hz₀]; exact Commons.Analysis.Complex.gam_re β t₀
  have hz₀im : z₀.im = t₀ := by rw [hz₀]; exact Commons.Analysis.Complex.gam_im β t₀
  have hz₀reg1 : -(β / Real.log (|z₀.im| + 2)) ≤ z₀.re := by rw [hz₀re, hz₀im]
  have hz₀reg2 : z₀.re ≤ 1 := by
    rw [hz₀re]
    have hp : 0 < β / Real.log (|t₀| + 2) :=
      div_pos hβ (Real.log_pos (by linarith [abs_nonneg t₀]))
    linarith
  have hζz₀ : riemannZeta (1 + z₀) ≠ 0 :=
    riemannZeta_inv_differentiableAt_imp_ne_zero hz₀ne (hinv z₀ hz₀ne hz₀reg1 hz₀reg2)
  -- hS
  have hS : ∀ s ∈ S, -(β / Real.log (|s.im| + 2)) < s.re ∧ s.re < 1 := by
    intro s hs
    rw [hSfin] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · constructor
      · rw [Complex.zero_re, Complex.zero_im, abs_zero, zero_add]
        have : 0 < β / Real.log 2 := div_pos hβ (Real.log_pos (by norm_num))
        linarith
      · norm_num
    · have hre : (-z₀).re = β / Real.log (|t₀| + 2) := by
        rw [Complex.neg_re, hz₀re]; ring
      have him : (-z₀).im = -t₀ := by rw [Complex.neg_im, hz₀im]
      constructor
      · rw [hre, him, abs_neg]
        have hp : 0 < β / Real.log (|t₀| + 2) :=
          div_pos hβ (Real.log_pos (by linarith [abs_nonneg t₀]))
        linarith
      · rw [hre]; exact betalog_lt_one hβ10 t₀
  have hRne : (R : ℂ) ≠ 0 := by
    simp only [ne_eq, ofReal_eq_zero]; linarith
  -- hdiff
  have hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 → z ∉ S →
      DifferentiableAt ℂ g z := by
    intro z hz1 hz2 hzS
    rw [hSfin] at hzS
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzS
    obtain ⟨hz0, hzneg⟩ := hzS
    rw [hg]
    have hf : DifferentiableAt ℂ (fun u : ℂ => f z₀ u) z := hdiff2 z₀ z hz₀reg1 hz₀reg2 hz1 hz2
    have hne1 : (1 : ℂ) + z₀ + z ≠ 1 := by
      intro h
      apply hzneg
      linear_combination h
    have hζ1u : DifferentiableAt ℂ (fun u : ℂ => riemannZeta (1 + z₀ + u)) z :=
      (differentiableAt_riemannZeta hne1).comp z (by fun_prop)
    have hζu : DifferentiableAt ℂ (fun u : ℂ => riemannZeta (1 + u)) z :=
      (differentiableAt_riemannZeta (by intro h; exact hz0 (by linear_combination h))).comp z
        (by fun_prop)
    have hconst : DifferentiableAt ℂ (fun _ : ℂ => riemannZeta (1 + z₀)) z := differentiableAt_const _
    have hinvz : DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z := hinv z hz0 hz1 hz2
    have hζz : riemannZeta (1 + z) ≠ 0 :=
      riemannZeta_inv_differentiableAt_imp_ne_zero hz0 hinvz
    have hden : DifferentiableAt ℂ (fun u : ℂ => riemannZeta (1 + z₀) * riemannZeta (1 + u)) z :=
      hconst.mul hζu
    have hprod : DifferentiableAt ℂ
        (fun u : ℂ => riemannZeta (1 + z₀ + u) / (riemannZeta (1 + z₀) * riemannZeta (1 + u))) z :=
      hζ1u.div hden (mul_ne_zero hζz₀ hζz)
    have hcpow : DifferentiableAt ℂ (fun u : ℂ => (R : ℂ) ^ (z₀ + u)) z :=
      (differentiableAt_cpow_const_v3 hRne).comp z (by fun_prop)
    have hden2 : DifferentiableAt ℂ (fun u : ℂ => z₀ ^ 2 * u ^ 2) z := by fun_prop
    exact ((hf.mul hprod).mul hcpow).div hden2
      (mul_ne_zero (pow_ne_zero 2 hz₀ne) (pow_ne_zero 2 hz0))
  -- residue values / continuity helpers
  have hmS : -z₀ ∈ S := by rw [hSfin]; simp
  have hm0 : (0:ℂ) ∈ S := by rw [hSfin]; simp
  have hnegz₀reg1 : -(β / Real.log (|(-z₀).im| + 2)) ≤ (-z₀).re := (hS (-z₀) hmS).1.le
  have hnegz₀reg2 : (-z₀).re ≤ 1 := (hS (-z₀) hmS).2.le
  have hnegz₀ne : -z₀ ≠ 0 := neg_ne_zero.mpr hz₀ne
  have hζnegz₀ : riemannZeta (1 + (-z₀)) ≠ 0 :=
    riemannZeta_inv_differentiableAt_imp_ne_zero hnegz₀ne
      (hinv (-z₀) hnegz₀ne hnegz₀reg1 hnegz₀reg2)
  have hres : ∀ s ∈ S, Tendsto (fun z : ℂ => (z - s) * g z) (nhdsWithin s ({s}ᶜ : Set ℂ))
      (nhds (res s)) := by
    intro s hs
    rw [hSfin] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · -- s = 0
      simp only [sub_zero]
      set Hfun : ℂ → ℂ := fun z => f z₀ z * riemannZeta (1 + z₀ + z) * (riemannZeta₁ (1 + z))⁻¹
        * (riemannZeta (1 + z₀))⁻¹ * (R : ℂ) ^ (z₀ + z) * (z₀ ^ 2)⁻¹ with hHfun
      have hres0v : res 0 = f z₀ 0 * (R : ℂ) ^ z₀ / z₀ ^ 2 := by rw [hresdef]; simp
      have hHfun0 : Hfun 0 = f z₀ 0 * (R : ℂ) ^ z₀ / z₀ ^ 2 := by
        rw [hHfun]
        simp only [add_zero, Complex.ofReal_zero, mul_zero, zero_add, riemannZeta₁_one, inv_one,
          one_mul]
        rw [div_eq_mul_inv]
        field_simp [hζz₀, pow_ne_zero 2 hz₀ne]
      have hHtend : Tendsto Hfun (nhds (0:ℂ)) (nhds (Hfun 0)) := by
        rw [hHfun]
        have h1 : ContinuousAt (fun z : ℂ => f z₀ z) 0 :=
          (hcont.comp (continuous_const.prodMk continuous_id)).continuousAt
        have h2 : ContinuousAt (fun z : ℂ => riemannZeta (1 + z₀ + z)) 0 := by
          have hne : (1 : ℂ) + z₀ + 0 ≠ 1 := by
            rw [add_zero]; intro h; exact hz₀ne (by linear_combination h)
          exact (differentiableAt_riemannZeta hne).continuousAt.comp (by fun_prop)
        have h3 : ContinuousAt (fun z : ℂ => (riemannZeta₁ (1 + z))⁻¹) 0 := by
          refine ContinuousAt.inv₀ ?_ ?_
          · exact (differentiable_riemannZeta₁.continuous.continuousAt).comp (by fun_prop)
          · simpa [riemannZeta₁_one] using (one_ne_zero : (1:ℂ) ≠ 0)
        have h4 : ContinuousAt (fun _ : ℂ => (riemannZeta (1 + z₀))⁻¹) 0 := continuousAt_const
        have h5 : ContinuousAt (fun z : ℂ => (R : ℂ) ^ (z₀ + z)) 0 := by
          have hh : ContinuousAt (fun z : ℂ => (R : ℂ) ^ z) (z₀ + 0) :=
            (differentiableAt_cpow_const_v3 hRne).continuousAt
          exact hh.comp (by fun_prop : ContinuousAt (fun z : ℂ => z₀ + z) 0)
        have h6 : ContinuousAt (fun _ : ℂ => (z₀ ^ 2)⁻¹) 0 := continuousAt_const
        exact ((((h1.mul h2).mul h3).mul h4).mul h5).mul h6
      have heq : (fun z : ℂ => z * g z) =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℂ)] Hfun := by
        have hζ1ne : ∀ᶠ z : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ), riemannZeta₁ (1 + z) ≠ 0 := by
          have hcomp : Tendsto (fun z : ℂ => (1:ℂ) + z) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 1) := by
            have h : Tendsto (fun z : ℂ => (1:ℂ) + z) (nhds (0:ℂ)) (nhds (1 + 0)) :=
              ((continuous_const : Continuous fun _ : ℂ => (1:ℂ)).add continuous_id).tendsto 0
            rw [add_zero] at h
            exact h.mono_left nhdsWithin_le_nhds
          exact hcomp.eventually riemannZeta₁_ne_zero_of_near_one
        filter_upwards [self_mem_nhdsWithin, hζ1ne] with z hzmem hζ1z
        have hz0 : z ≠ 0 := by simpa using hzmem
        have hzz : z * riemannZeta (1 + z) = riemannZeta₁ (1 + z) := mul_riemannZeta_one_add z hz0
        have h1 : riemannZeta (1 + z) = z⁻¹ * riemannZeta₁ (1 + z) := by
          rw [← hzz, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
        simp only [hg, hHfun, h1, div_eq_mul_inv, mul_inv, inv_inv]
        field_simp [hz0, hz₀ne, hζz₀, hζ1z]
      have hlim : Tendsto (fun z : ℂ => z * g z) (nhdsWithin 0 ({0}ᶜ : Set ℂ))
          (nhds (res 0)) := by
        rw [hres0v, ← hHfun0]
        exact hHtend.mono_left nhdsWithin_le_nhds |>.congr' heq.symm
      exact hlim
    · -- s = -z₀
      set Hfun2 : ℂ → ℂ := fun z => f z₀ z * (riemannZeta (1 + z₀))⁻¹ * (riemannZeta (1 + z))⁻¹
        * (R : ℂ) ^ (z₀ + z) * (z₀ ^ 2 * z ^ 2)⁻¹ with hHfun2
      have hresnegv : res (-z₀) = f z₀ (-z₀)
          / (riemannZeta (1 + z₀) * riemannZeta (1 - z₀) * z₀ ^ 4) := by
        rw [hresdef]; simp [hz₀ne, sub_eq_add_neg]
      have hHfun2val : Hfun2 (-z₀) = f z₀ (-z₀)
          / (riemannZeta (1 + z₀) * riemannZeta (1 - z₀) * z₀ ^ 4) := by
        rw [hHfun2]
        simp only [add_neg_cancel, Complex.ofReal_zero, Complex.cpow_zero, mul_one, neg_sq,
          sub_eq_add_neg]
        rw [div_eq_mul_inv]
        field_simp [hζz₀, hζnegz₀, pow_ne_zero 2 hz₀ne]
      have hHcont2 : ContinuousAt Hfun2 (-z₀) := by
        rw [hHfun2]
        have h1 : ContinuousAt (fun z : ℂ => f z₀ z) (-z₀) :=
          (hcont.comp (continuous_const.prodMk continuous_id)).continuousAt
        have h2 : ContinuousAt (fun _ : ℂ => (riemannZeta (1 + z₀))⁻¹) (-z₀) := continuousAt_const
        have h3 : ContinuousAt (fun z : ℂ => (riemannZeta (1 + z))⁻¹) (-z₀) := by
          refine ContinuousAt.inv₀ ?_ ?_
          · refine (differentiableAt_riemannZeta ?_).continuousAt.comp (by fun_prop)
            intro h; apply hnegz₀ne; linear_combination h
          · simpa using hζnegz₀
        have h5 : ContinuousAt (fun z : ℂ => (R : ℂ) ^ (z₀ + z)) (-z₀) := by
          have hh : ContinuousAt (fun z : ℂ => (R : ℂ) ^ z) (z₀ + (-z₀)) :=
            (differentiableAt_cpow_const_v3 hRne).continuousAt
          exact hh.comp (by fun_prop : ContinuousAt (fun z : ℂ => z₀ + z) (-z₀))
        have h6 : ContinuousAt (fun z : ℂ => (z₀ ^ 2 * z ^ 2)⁻¹) (-z₀) := by
          refine ContinuousAt.inv₀ (by fun_prop) ?_
          have : z₀ ^ 2 * (-z₀) ^ 2 = z₀ ^ 4 := by ring
          rw [this]; exact pow_ne_zero 4 hz₀ne
        exact (((h1.mul h2).mul h3).mul h5).mul h6
      have hlim1 : Tendsto (fun z : ℂ => (z + z₀) * riemannZeta (1 + z₀ + z))
          (nhdsWithin (-z₀) ({-z₀}ᶜ : Set ℂ)) (nhds 1) := by
        have hφ : Tendsto (fun z : ℂ => z + z₀) (nhdsWithin (-z₀) ({-z₀}ᶜ : Set ℂ))
            (nhdsWithin 0 ({0}ᶜ : Set ℂ)) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · have h : Tendsto (fun z : ℂ => z + z₀) (nhds (-z₀)) (nhds ((-z₀) + z₀)) :=
              tendsto_id.add tendsto_const_nhds
            simpa using h.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with z hz
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
            intro h
            exact hz (by linear_combination h)
        have h := tendsto_mul_riemannZeta_one_add.comp hφ
        refine h.congr' ?_
        filter_upwards with z
        simp only [Function.comp_apply]
        rw [show (1:ℂ) + z₀ + z = 1 + (z + z₀) by ring]
      have heq2 : (fun z : ℂ => (z - (-z₀)) * g z) =ᶠ[nhdsWithin (-z₀) ({-z₀}ᶜ : Set ℂ)]
          (fun z : ℂ => Hfun2 z * ((z + z₀) * riemannZeta (1 + z₀ + z))) := by
        filter_upwards with z
        simp only [hg, hHfun2, sub_neg_eq_add, div_eq_mul_inv, mul_inv]
        ring
      have hlim2 : Tendsto (fun z : ℂ => (z - (-z₀)) * g z) (nhdsWithin (-z₀) ({-z₀}ᶜ : Set ℂ))
          (nhds (res (-z₀))) := by
        rw [hresnegv, ← hHfun2val]
        have h1 : Tendsto Hfun2 (nhdsWithin (-z₀) ({-z₀}ᶜ : Set ℂ)) (nhds (Hfun2 (-z₀))) :=
          hHcont2.tendsto.mono_left nhdsWithin_le_nhds
        have h2 := h1.mul hlim1
        rw [mul_one] at h2
        exact h2.congr' heq2.symm
      exact hlim2
  -- the three analytic hypotheses
  have hBnn : 0 ≤ B := by
    have h : -(β / Real.log (|(1:ℂ).im| + 2)) ≤ (1:ℂ).re := by
      simp only [Complex.one_im, abs_zero, zero_add, Complex.one_re]
      have : 0 ≤ β / Real.log 2 := div_nonneg hβ.le (Real.log_nonneg (by norm_num))
      linarith
    have h2 : (1:ℂ).re ≤ 1 := by simp
    exact le_trans (norm_nonneg _) (hbound 1 1 h h2 h h2)
  have hint1 : MeasureTheory.Integrable (fun t : ℝ => g ((1:ℂ) + (t:ℂ) * Complex.I) * Complex.I) := by
    obtain ⟨Cζ, hCζpos, hCζ⟩ :=
      norm_riemannZeta_le_const_of_one_lt_re (σ := 2 - β / Real.log (|t₀| + 2))
        (by linarith [betalog_lt_one hβ10 t₀])
    have hw_ne : ∀ t : ℝ, ((1:ℂ) + (t:ℂ) * Complex.I) ≠ 0 := by
      intro t h; have := congrArg Complex.re h; simp at this
    have hw_re : ∀ t : ℝ, ((1:ℂ) + (t:ℂ) * Complex.I).re = 1 := by intro t; simp
    have hw_im : ∀ t : ℝ, ((1:ℂ) + (t:ℂ) * Complex.I).im = t := by intro t; simp
    have hw_reg1 : ∀ t : ℝ, -(β / Real.log (|((1:ℂ) + (t:ℂ)*Complex.I).im| + 2))
        ≤ ((1:ℂ) + (t:ℂ)*Complex.I).re := by
      intro t; rw [hw_im, hw_re]
      have : 0 ≤ β / Real.log (|t| + 2) := div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t]))
      linarith
    have hw_reg2 : ∀ t : ℝ, ((1:ℂ) + (t:ℂ)*Complex.I).re ≤ 1 := by intro t; rw [hw_re]
    set Gg : ℝ → ℂ := fun t => (riemannZeta (1 + ((1:ℂ) + (t:ℂ)*Complex.I)))⁻¹ with hGg
    set Pr : ℝ → ℂ := fun t => f z₀ ((1:ℂ) + (t:ℂ)*Complex.I)
      * riemannZeta (1 + z₀ + ((1:ℂ) + (t:ℂ)*Complex.I)) * (riemannZeta (1 + z₀))⁻¹
      * (R:ℂ)^(z₀ + ((1:ℂ)+(t:ℂ)*Complex.I)) * (z₀^2)⁻¹
      * ((((1:ℂ)+(t:ℂ)*Complex.I))^2)⁻¹ * Complex.I with hPr
    set K : ℝ := B * Cζ * ‖(riemannZeta (1 + z₀))⁻¹‖ * R * ‖(z₀ ^ 2)⁻¹‖ with hKdef
    have hKnn : 0 ≤ K := by
      rw [hKdef]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hBnn hCζpos.le) (norm_nonneg _))
        (by linarith)) (norm_nonneg _)
    have hb : ∀ t : ℝ, ‖Gg t‖ ≤ C₁ * (Real.log (2 + |t|) + 1) := by
      intro t
      rw [hGg]
      have h := hinvb ((1:ℂ) + (t:ℂ)*Complex.I) (hw_ne t) (hw_reg1 t) (hw_reg2 t)
      simp only [hw_im] at h
      calc ‖(riemannZeta (1 + ((1:ℂ) + (t:ℂ) * Complex.I)))⁻¹‖
          ≤ C₁ * (Real.log (|t| + 2) + 1) := h
        _ = C₁ * (Real.log (2 + |t|) + 1) := by rw [add_comm 2 |t|]
    have hcpow_bound : ∀ t : ℝ, ‖(R:ℂ)^(z₀ + ((1:ℂ)+(t:ℂ)*Complex.I))‖ ≤ R := by
      intro t
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ) < R)]
      calc R ^ (z₀ + ((1:ℂ)+(t:ℂ)*Complex.I)).re ≤ R ^ (1:ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ R)
            rw [Complex.add_re, hz₀re, hw_re]
            have : 0 ≤ β / Real.log (|t₀| + 2) :=
              div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t₀]))
            linarith
        _ = R := Real.rpow_one R
    have hw2 : ∀ t : ℝ, ‖((((1:ℂ)+(t:ℂ)*Complex.I))^2)⁻¹‖ ≤ (1 + t^2)⁻¹ := by
      intro t
      rw [norm_inv, norm_pow]
      have h : ‖((1:ℂ) + (t:ℂ) * Complex.I)‖ ^ 2 = 1 + t ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      rw [h]
    have hP : ∀ t : ℝ, ‖Pr t‖ ≤ K / (1^2 + (t - 0)^2) := by
      intro t
      have h1 : ‖f z₀ ((1:ℂ) + (t:ℂ)*Complex.I)‖ ≤ B :=
        hbound z₀ _ hz₀reg1 hz₀reg2 (hw_reg1 t) (hw_reg2 t)
      have h2 : ‖riemannZeta (1 + z₀ + ((1:ℂ) + (t:ℂ)*Complex.I))‖ ≤ Cζ := by
        apply hCζ
        have he : (1 + z₀ + ((1:ℂ) + (t:ℂ)*Complex.I)).re = 2 - β / Real.log (|t₀| + 2) := by
          simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, hz₀re]
          ring
        rw [he]
      have h4 := hcpow_bound t
      have h6 := hw2 t
      have h3 : ‖(riemannZeta (1 + z₀))⁻¹‖ ≤ ‖(riemannZeta (1 + z₀))⁻¹‖ := le_rfl
      have h5 : ‖(z₀ ^ 2)⁻¹‖ ≤ ‖(z₀ ^ 2)⁻¹‖ := le_rfl
      have hBC : (0:ℝ) ≤ B * Cζ := mul_nonneg hBnn hCζpos.le
      have hBCP : (0:ℝ) ≤ B * Cζ * ‖(riemannZeta (1 + z₀))⁻¹‖ :=
        mul_nonneg hBC (norm_nonneg _)
      have hBCPR : (0:ℝ) ≤ B * Cζ * ‖(riemannZeta (1 + z₀))⁻¹‖ * R :=
        mul_nonneg hBCP (by linarith)
      have hBCPRQ : (0:ℝ) ≤ B * Cζ * ‖(riemannZeta (1 + z₀))⁻¹‖ * R * ‖(z₀ ^ 2)⁻¹‖ :=
        mul_nonneg hBCPR (norm_nonneg _)
      have e1 : ‖f z₀ ((1:ℂ) + (t:ℂ)*Complex.I)‖
          * ‖riemannZeta (1 + z₀ + ((1:ℂ) + (t:ℂ)*Complex.I))‖ ≤ B * Cζ :=
        mul_le_mul h1 h2 (norm_nonneg _) hBnn
      have e2 : ‖f z₀ ((1:ℂ) + (t:ℂ)*Complex.I)‖
          * ‖riemannZeta (1 + z₀ + ((1:ℂ) + (t:ℂ)*Complex.I))‖ * ‖(riemannZeta (1 + z₀))⁻¹‖
          ≤ B * Cζ * ‖(riemannZeta (1 + z₀))⁻¹‖ := mul_le_mul e1 h3 (norm_nonneg _) hBC
      have e3 : ‖f z₀ ((1:ℂ) + (t:ℂ)*Complex.I)‖
          * ‖riemannZeta (1 + z₀ + ((1:ℂ) + (t:ℂ)*Complex.I))‖ * ‖(riemannZeta (1 + z₀))⁻¹‖
          * ‖(R:ℂ)^(z₀ + ((1:ℂ)+(t:ℂ)*Complex.I))‖
          ≤ B * Cζ * ‖(riemannZeta (1 + z₀))⁻¹‖ * R := mul_le_mul e2 h4 (norm_nonneg _) hBCP
      have e4 : ‖f z₀ ((1:ℂ) + (t:ℂ)*Complex.I)‖
          * ‖riemannZeta (1 + z₀ + ((1:ℂ) + (t:ℂ)*Complex.I))‖ * ‖(riemannZeta (1 + z₀))⁻¹‖
          * ‖(R:ℂ)^(z₀ + ((1:ℂ)+(t:ℂ)*Complex.I))‖ * ‖(z₀ ^ 2)⁻¹‖
          ≤ B * Cζ * ‖(riemannZeta (1 + z₀))⁻¹‖ * R * ‖(z₀ ^ 2)⁻¹‖ :=
        mul_le_mul e3 h5 (norm_nonneg _) hBCPR
      have e5 : ‖f z₀ ((1:ℂ) + (t:ℂ)*Complex.I)‖
          * ‖riemannZeta (1 + z₀ + ((1:ℂ) + (t:ℂ)*Complex.I))‖ * ‖(riemannZeta (1 + z₀))⁻¹‖
          * ‖(R:ℂ)^(z₀ + ((1:ℂ)+(t:ℂ)*Complex.I))‖ * ‖(z₀ ^ 2)⁻¹‖
          * ‖(((1:ℂ)+(t:ℂ)*Complex.I)^2)⁻¹‖
          ≤ B * Cζ * ‖(riemannZeta (1 + z₀))⁻¹‖ * R * ‖(z₀ ^ 2)⁻¹‖ * (1 + t^2)⁻¹ :=
        mul_le_mul e4 h6 (norm_nonneg _) hBCPRQ
      rw [hPr]
      simp only [norm_mul, Complex.norm_I, mul_one]
      rw [div_eq_mul_inv, show (1:ℝ)^2 + (t - 0)^2 = 1 + t^2 by ring]
      rw [hKdef]
      exact e5
    have hcont_g : Continuous (fun t : ℝ => g ((1:ℂ) + (t:ℂ)*Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hmem : ((1:ℂ) + (t:ℂ)*Complex.I) ∉ S := by
        rw [hSfin]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, ?_⟩
        · exact hw_ne t
        · intro h
          have := congrArg Complex.re h
          simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
            Complex.I_re, mul_zero, add_zero, Complex.ofReal_im, Complex.I_im, mul_one,
            Complex.neg_re] at this
          rw [hz₀re] at this
          have := betalog_lt_one hβ10 t₀
          linarith
      have hinner : ContinuousAt (fun t : ℝ => (1:ℂ) + (t:ℂ)*Complex.I) t :=
        continuousAt_const.add ((Complex.continuous_ofReal.continuousAt).mul continuousAt_const)
      exact ContinuousAt.comp (f := fun t : ℝ => (1:ℂ) + (t:ℂ)*Complex.I)
        (hdiff _ (hw_reg1 t) (hw_reg2 t) hmem).continuousAt hinner
    have hprod : ∀ t : ℝ, Gg t * Pr t = g ((1:ℂ) + (t:ℂ)*Complex.I) * Complex.I := by
      intro t
      simp only [hGg, hPr, hg, div_eq_mul_inv, mul_inv]
      ring
    have hcont_prod : Continuous (fun t : ℝ => g ((1:ℂ) + (t:ℂ)*Complex.I) * Complex.I) :=
      hcont_g.mul continuous_const
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Gg t * Pr t) MeasureTheory.volume := by
      refine hcont_prod.aestronglyMeasurable.congr ?_
      filter_upwards with t
      exact (hprod t).symm
    exact (Commons.Analysis.Integral.integrable_of_log_le_lorentz (g := Gg) (P := Pr)
      (a := 1) (b := 0) (C := C₁) (K := K) (by norm_num) hC1.le hKnn hmeas hb hP).congr
      (Filter.Eventually.of_forall hprod)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβ_log2_pos : 0 < β / Real.log 2 := div_pos hβ hlog2pos
  have hβt₀_pos : 0 < β / Real.log (|t₀| + 2) := div_pos hβ (Real.log_pos (by linarith [abs_nonneg t₀]))
  set δmax : ℝ := β / Real.log (|t₀| + 2) + β / Real.log 2 with hδmax
  have hδmax_nn : 0 ≤ δmax := by rw [hδmax]; linarith
  have hδmax_le : δmax ≤ 3/10 := by
    rw [hδmax]
    have h1 : β / Real.log (|t₀| + 2) ≤ β / Real.log 2 :=
      div_le_div_of_nonneg_left hβ.le hlog2pos (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t₀]))
    have h3 : 2 * (β / Real.log 2) ≤ 3/10 := by
      rw [show 2 * (β / Real.log 2) = 2 * β / Real.log 2 by ring, div_le_iff₀ hlog2pos]
      have hlog2' : (2:ℝ)/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith
    linarith
  obtain ⟨Cconv, hCconvpos, hCconv⟩ := zeta_near_line_bound
  have hCconvnn : 0 ≤ Cconv := hCconvpos.le
  set Czb : ℝ := max (C₃ * (2 * |t₀| + 6) ^ 4)
      (Cconv * (Real.log (|t₀| + 2) / β) * (|t₀| + 3) ^ δmax) with hCzb
  have hCzb_nn : 0 ≤ Czb := by
    rw [hCzb]; exact le_trans (by positivity) (le_max_left _ _)
  have hzb : ∀ t : ℝ, ‖riemannZeta (1 + z₀ + Commons.Analysis.Complex.gam β t)‖
      ≤ Czb * (1 + |t|) ^ δmax := by
    intro t
    by_cases hτ : 3 ≤ |t₀ + t|
    · have harg : 1 + z₀ + Commons.Analysis.Complex.gam β t
          = ((1 - (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2)) : ℝ) : ℂ)
            + Complex.I * ((t₀ + t : ℝ) : ℂ) := by
        rw [hz₀]
        apply Complex.ext <;> simp [Commons.Analysis.Complex.gam, Commons.Analysis.Complex.phi] <;> ring
      rw [harg]
      have hδ0 : 0 < β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2) := by
        have h2 : 0 < β / Real.log (|t| + 2) := div_pos hβ (Real.log_pos (by linarith [abs_nonneg t]))
        linarith
      have hδhalf : β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2) ≤ 1/2 := by
        have hlog2' : (2:ℝ)/5 < Real.log 2 := by linarith [Real.log_two_gt_d9]
        have h1 : β / Real.log (|t₀| + 2) ≤ β / Real.log 2 :=
          div_le_div_of_nonneg_left hβ.le hlog2pos (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t₀]))
        have h2 : β / Real.log (|t| + 2) ≤ β / Real.log 2 :=
          div_le_div_of_nonneg_left hβ.le hlog2pos (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
        have h3 : 2 * (β / Real.log 2) ≤ 1/2 := by
          rw [show 2 * (β / Real.log 2) = 2 * β / Real.log 2 by ring, div_le_iff₀ hlog2pos]
          linarith
        linarith
      have hb := hCconv (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2)) (t₀ + t) hδ0 hδhalf hτ
      have hinvδ : 1 / (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2))
          ≤ Real.log (|t₀| + 2) / β := by
        have h2 : 0 < β / Real.log (|t| + 2) := div_pos hβ (Real.log_pos (by linarith [abs_nonneg t]))
        have hab : β / Real.log (|t₀| + 2)
            ≤ β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2) := by linarith
        calc 1 / (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2))
            = (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2))⁻¹ := one_div _
          _ ≤ (β / Real.log (|t₀| + 2))⁻¹ :=
              (inv_le_inv₀ hδ0 hβt₀_pos).mpr hab
          _ = Real.log (|t₀| + 2) / β := by rw [inv_div]
      have hexp_le : β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2) ≤ δmax := by
        rw [hδmax]
        have h2 : β / Real.log (|t| + 2) ≤ β / Real.log 2 :=
          div_le_div_of_nonneg_left hβ.le hlog2pos (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
        linarith
      have hsplit : (|t₀ + t| + 3) ^ (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2))
          ≤ (|t₀| + 3) ^ δmax * (1 + |t|) ^ δmax := by
        have hA : (|t₀ + t| + 3) ^ (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2))
            ≤ (|t₀| + |t| + 3) ^ (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2)) := by
          apply Real.rpow_le_rpow (by positivity) _ (by positivity)
          have := abs_add_le t₀ t; linarith
        have hB : (|t₀| + |t| + 3) ^ (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2))
            ≤ (|t₀| + |t| + 3) ^ δmax := by
          apply Real.rpow_le_rpow_of_exponent_le ?_ hexp_le
          have := abs_nonneg t₀; have := abs_nonneg t; linarith
        have hC : (|t₀| + |t| + 3) ^ δmax ≤ (|t₀| + 3) ^ δmax * (1 + |t|) ^ δmax := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          apply Real.rpow_le_rpow (by positivity) _ hδmax_nn
          nlinarith [abs_nonneg t₀, abs_nonneg t,
            mul_nonneg (abs_nonneg t₀) (abs_nonneg t),
            mul_nonneg (abs_nonneg t) (by norm_num : (0:ℝ) ≤ 2)]
        linarith
      have hstep : Cconv * (1 / (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2)))
            * (|t₀ + t| + 3) ^ (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2))
          ≤ Czb * (1 + |t|) ^ δmax := by
        calc Cconv * (1 / (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2)))
              * (|t₀ + t| + 3) ^ (β / Real.log (|t₀| + 2) + β / Real.log (|t| + 2))
            ≤ Cconv * (Real.log (|t₀| + 2) / β) * ((|t₀| + 3) ^ δmax * (1 + |t|) ^ δmax) := by
                simp only [mul_assoc]
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul hinvδ hsplit (Real.rpow_nonneg (by positivity) _)
                    (div_nonneg (Real.log_nonneg (by linarith [abs_nonneg t₀])) hβ.le)) hCconvnn
          _ = (Cconv * (Real.log (|t₀| + 2) / β) * (|t₀| + 3) ^ δmax) * (1 + |t|) ^ δmax := by ring
          _ ≤ Czb * (1 + |t|) ^ δmax := by
                apply mul_le_mul_of_nonneg_right (le_max_right _ _)
                exact Real.rpow_nonneg (by positivity) _
      exact le_trans hb hstep
    · have hlt : |t₀ + t| < 3 := not_le.mp hτ
      have htlt : |t| ≤ |t₀| + 3 := by
        have h : |t| ≤ |t₀| + |t₀ + t| := by
          calc |t| = |-t₀ + (t₀ + t)| := by rw [show -t₀ + (t₀ + t) = t by ring]
            _ ≤ |-t₀| + |t₀ + t| := abs_add_le _ _
            _ = |t₀| + |t₀ + t| := by rw [abs_neg]
        linarith only [h, hlt]
      have h0 := hznumγ t
      have h1 : (1:ℝ) ≤ (1 + |t|) ^ δmax :=
        Real.one_le_rpow (by linarith [abs_nonneg t]) hδmax_nn
      calc ‖riemannZeta (1 + z₀ + Commons.Analysis.Complex.gam β t)‖
          ≤ C₃ * (|t₀| + |t| + 3) ^ ((1:ℝ)/2) := h0
        _ ≤ C₃ * (2 * |t₀| + 6) ^ 4 := by
            apply mul_le_mul_of_nonneg_left _ hC3.le
            have hx : |t₀| + |t| + 3 ≤ 2 * |t₀| + 6 := by linarith only [htlt]
            have hb1 : (|t₀| + |t| + 3) ^ ((1:ℝ)/2) ≤ (2 * |t₀| + 6) ^ ((1:ℝ)/2) :=
              Real.rpow_le_rpow (by positivity) hx (by norm_num)
            have hb2 : (2 * |t₀| + 6) ^ ((1:ℝ)/2) ≤ (2 * |t₀| + 6) ^ 4 := by
              have h := Real.rpow_le_rpow_of_exponent_le (x := 2 * |t₀| + 6)
                (y := (1:ℝ)/2) (z := ((4:ℕ):ℝ))
                (by linarith [abs_nonneg t₀]) (by norm_num)
              simpa only [Real.rpow_natCast] using h
            exact le_trans hb1 hb2
        _ ≤ Czb := by rw [hCzb]; exact le_max_left _ _
        _ ≤ Czb * (1 + |t|) ^ δmax := le_mul_of_one_le_right hCzb_nn h1
  have hcurve : MeasureTheory.Integrable (fun t : ℝ =>
      g (Commons.Analysis.Complex.gam β t) * Commons.Analysis.Complex.gamDot β t) := by
    set Dtot : ℝ := B * Czb * ‖(riemannZeta (1 + z₀))⁻¹‖ * C₁ * ‖(z₀ ^ 2)⁻¹‖
      * Commons.Analysis.Complex.curveConst β * 2 ^ (δmax / 2) * (Real.log 3 + 3) with hDtot
    have hDtot_nn : 0 ≤ Dtot := by
      rw [hDtot]
      have h2p : 0 ≤ (2:ℝ) ^ (δmax / 2) := Real.rpow_nonneg (by norm_num) _
      have h3p : 0 ≤ Real.log 3 + 3 := by
        have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3); linarith only [this]
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · apply mul_nonneg
              · apply mul_nonneg
                · apply mul_nonneg
                  · exact hBnn
                  · exact hCzb_nn
                · exact norm_nonneg _
              · exact hC1.le
            · exact norm_nonneg _
          · exact (Commons.Analysis.Complex.curveConst_pos hβ).le
        · exact h2p
      · exact h3p
    have hgam_re : ∀ t : ℝ, (Commons.Analysis.Complex.gam β t).re = -(β / Real.log (|t| + 2)) :=
      fun t => Commons.Analysis.Complex.gam_re β t
    have hgam_im : ∀ t : ℝ, (Commons.Analysis.Complex.gam β t).im = t :=
      fun t => Commons.Analysis.Complex.gam_im β t
    have hgam_reg1 : ∀ t, -(β / Real.log (|(Commons.Analysis.Complex.gam β t).im| + 2))
        ≤ (Commons.Analysis.Complex.gam β t).re := by
      intro t; rw [hgam_im, hgam_re]
    have hgam_reg2 : ∀ t, (Commons.Analysis.Complex.gam β t).re ≤ 1 := by
      intro t; rw [hgam_re]
      have : 0 ≤ β / Real.log (|t| + 2) := div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t]))
      linarith
    have hζgam_inv : ∀ t, ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
        ≤ C₁ * (Real.log (2 + |t|) + 1) := by
      intro t
      have h := hinvb (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam_ne_zero hβ t)
        (hgam_reg1 t) (hgam_reg2 t)
      rw [hgam_im] at h
      calc ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
          ≤ C₁ * (Real.log (|t| + 2) + 1) := h
        _ = C₁ * (Real.log (2 + |t|) + 1) := by rw [add_comm 2 |t|]
    have hRgam : ∀ t, ‖(R : ℂ) ^ (z₀ + Commons.Analysis.Complex.gam β t)‖ ≤ 1 := by
      intro t
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ) < R)]
      calc R ^ (z₀ + Commons.Analysis.Complex.gam β t).re ≤ R ^ (0:ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ R)
            rw [Complex.add_re, hz₀re, hgam_re]
            have h1 : 0 ≤ β / Real.log (|t₀| + 2) := hβt₀_pos.le
            have h2 : 0 ≤ β / Real.log (|t| + 2) := div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t]))
            linarith
          _ = 1 := Real.rpow_zero R
    have hgamDot : ∀ t, ‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β t‖
        ≤ Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹ :=
      fun t => Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le hβ t
    have hbdd : ∀ t : ℝ, ‖g (Commons.Analysis.Complex.gam β t) * Commons.Analysis.Complex.gamDot β t‖
        ≤ Dtot * (1 + t^2) ^ (-((3:ℝ)/5)) := by
      intro t
      have h1m : ‖f z₀ (Commons.Analysis.Complex.gam β t)‖ ≤ B :=
        hbound z₀ _ hz₀reg1 hz₀reg2 (hgam_reg1 t) (hgam_reg2 t)
      have h2m : ‖riemannZeta (1 + z₀ + Commons.Analysis.Complex.gam β t)‖
          ≤ Czb * (1 + |t|) ^ δmax := hzb t
      have h4m : ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
          ≤ C₁ * (Real.log (2 + |t|) + 1) := hζgam_inv t
      have h5m : ‖(R : ℂ) ^ (z₀ + Commons.Analysis.Complex.gam β t)‖ ≤ 1 := hRgam t
      have hlog : Real.log (2 + |t|) + 1 ≤ (Real.log 3 + 3) * (1 + t^2) ^ ((1:ℝ)/4) := by
        have := Commons.Analysis.Integral.log_two_add_abs_le 0 t
        simpa using this
      have hrpow : ∀ x : ℝ, 0 ≤ x → (x ^ ((1:ℝ)/2)) ^ δmax = x ^ (δmax / 2) := by
        intro x hx
        rw [← Real.rpow_mul hx (1/2) δmax]
        congr 1; ring
      have hpow : (1 + |t|) ^ δmax ≤ 2 ^ (δmax / 2) * (1 + t^2) ^ (δmax / 2) := by
        have hbase : 1 + |t| ≤ Real.sqrt (2 * (1 + t^2)) := by
          have h2 : (1 + |t|)^2 ≤ 2 * (1 + t^2) := by
            have hsq : |t|^2 = t^2 := sq_abs t
            nlinarith only [sq_nonneg (1 - |t|), hsq, abs_nonneg t]
          calc 1 + |t| = Real.sqrt ((1 + |t|)^2) := (Real.sqrt_sq (by positivity)).symm
            _ ≤ Real.sqrt (2 * (1 + t^2)) := Real.sqrt_le_sqrt h2
        have hsq2 : Real.sqrt (2 * (1 + t^2)) = 2 ^ ((1:ℝ)/2) * (1 + t^2) ^ ((1:ℝ)/2) := by
          rw [Real.sqrt_eq_rpow, Real.mul_rpow (by norm_num) (by positivity)]
        calc (1 + |t|) ^ δmax ≤ (Real.sqrt (2 * (1 + t^2))) ^ δmax :=
              Real.rpow_le_rpow (by positivity) hbase hδmax_nn
          _ = (2 ^ ((1:ℝ)/2) * (1 + t^2) ^ ((1:ℝ)/2)) ^ δmax := by rw [hsq2]
          _ = 2 ^ (δmax / 2) * (1 + t^2) ^ (δmax / 2) := by
              rw [Real.mul_rpow (by positivity) (by positivity), hrpow 2 (by norm_num),
                hrpow (1 + t^2) (by positivity)]
      have hexp : δmax / 2 + 1/4 - 1 ≤ -((3:ℝ)/5) := by linarith only [hδmax_le]
      have hN2 : 0 ≤ Czb * (1 + |t|) ^ δmax :=
        mul_nonneg hCzb_nn (Real.rpow_nonneg (by positivity) _)
      have hlogpos : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
      have hN4 : 0 ≤ C₁ * (Real.log (2 + |t|) + 1) :=
        mul_nonneg hC1.le (by linarith [hlogpos])
      have hN6 : 0 ≤ ‖(z₀^2)⁻¹‖ := norm_nonneg _
      have hN7 : 0 ≤ Commons.Analysis.Complex.curveConst β * (1 + t^2)⁻¹ :=
        mul_nonneg (Commons.Analysis.Complex.curveConst_pos hβ).le (by positivity)
      have hA1 : 0 ≤ B * (Czb * (1 + |t|) ^ δmax) := mul_nonneg hBnn hN2
      have hA2 : 0 ≤ B * (Czb * (1 + |t|) ^ δmax) * ‖(riemannZeta (1 + z₀))⁻¹‖ :=
        mul_nonneg hA1 (norm_nonneg _)
      have hA3 : 0 ≤ B * (Czb * (1 + |t|) ^ δmax) * ‖(riemannZeta (1 + z₀))⁻¹‖
          * (C₁ * (Real.log (2 + |t|) + 1)) := mul_nonneg hA2 hN4
      have hA4 : 0 ≤ B * (Czb * (1 + |t|) ^ δmax) * ‖(riemannZeta (1 + z₀))⁻¹‖
          * (C₁ * (Real.log (2 + |t|) + 1)) * 1 := mul_nonneg hA3 zero_le_one
      have hA5 : 0 ≤ B * (Czb * (1 + |t|) ^ δmax) * ‖(riemannZeta (1 + z₀))⁻¹‖
          * (C₁ * (Real.log (2 + |t|) + 1)) * 1 * ‖(z₀^2)⁻¹‖ := mul_nonneg hA4 hN6
      have hstep3 : (1 + |t|) ^ δmax * (Real.log (2 + |t|) + 1) * (1 + t^2)⁻¹
          ≤ 2 ^ (δmax / 2) * (Real.log 3 + 3) * (1 + t^2) ^ (-((3:ℝ)/5)) := by
        have hAB : (1 + |t|) ^ δmax * (Real.log (2 + |t|) + 1)
            ≤ (2 ^ (δmax / 2) * (1 + t^2) ^ (δmax / 2))
              * ((Real.log 3 + 3) * (1 + t^2) ^ ((1:ℝ)/4)) :=
          mul_le_mul hpow hlog (by linarith [hlogpos])
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by positivity) _))
        have hkey : (1 + t^2) ^ (δmax / 2) * (1 + t^2) ^ ((1:ℝ)/4) * (1 + t^2)⁻¹
            = (1 + t^2) ^ (δmax / 2 + 1/4 - 1) := by
          rw [← Real.rpow_neg_one (1 + t^2),
            ← Real.rpow_add (by positivity : (0:ℝ) < 1 + t^2),
            ← Real.rpow_add (by positivity : (0:ℝ) < 1 + t^2)]
          ring_nf
        calc (1 + |t|) ^ δmax * (Real.log (2 + |t|) + 1) * (1 + t^2)⁻¹
            ≤ (2 ^ (δmax / 2) * (1 + t^2) ^ (δmax / 2))
                * ((Real.log 3 + 3) * (1 + t^2) ^ ((1:ℝ)/4)) * (1 + t^2)⁻¹ :=
                mul_le_mul_of_nonneg_right hAB (by positivity)
          _ = 2 ^ (δmax / 2) * (Real.log 3 + 3)
                * ((1 + t^2) ^ (δmax / 2) * (1 + t^2) ^ ((1:ℝ)/4) * (1 + t^2)⁻¹) := by ring
          _ = 2 ^ (δmax / 2) * (Real.log 3 + 3) * (1 + t^2) ^ (δmax / 2 + 1/4 - 1) := by rw [hkey]
          _ ≤ 2 ^ (δmax / 2) * (Real.log 3 + 3) * (1 + t^2) ^ (-((3:ℝ)/5)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg t]) hexp
      have hmul : ‖g (Commons.Analysis.Complex.gam β t) * Commons.Analysis.Complex.gamDot β t‖
          ≤ B * (Czb * (1 + |t|) ^ δmax) * ‖(riemannZeta (1 + z₀))⁻¹‖
            * (C₁ * (Real.log (2 + |t|) + 1)) * 1 * ‖(z₀^2)⁻¹‖
            * (Commons.Analysis.Complex.curveConst β * (1 + t^2)⁻¹) := by
        have hfac : g (Commons.Analysis.Complex.gam β t) * Commons.Analysis.Complex.gamDot β t
            = f z₀ (Commons.Analysis.Complex.gam β t)
              * (riemannZeta (1 + z₀ + Commons.Analysis.Complex.gam β t))
              * (riemannZeta (1 + z₀))⁻¹
              * (riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹
              * (R : ℂ) ^ (z₀ + Commons.Analysis.Complex.gam β t) * (z₀^2)⁻¹
              * (((Commons.Analysis.Complex.gam β t)^2)⁻¹ * Commons.Analysis.Complex.gamDot β t) := by
          simp only [hg, div_eq_mul_inv, mul_inv]
          ring
        rw [hfac]
        simp only [norm_mul]
        have h7m' : ‖((Commons.Analysis.Complex.gam β t)^2)⁻¹‖
            * ‖Commons.Analysis.Complex.gamDot β t‖
            ≤ Commons.Analysis.Complex.curveConst β * (1 + t^2)⁻¹ := by
          rw [← norm_mul]; exact hgamDot t
        have hX : ‖f z₀ (Commons.Analysis.Complex.gam β t)‖
              * ‖riemannZeta (1 + z₀ + Commons.Analysis.Complex.gam β t)‖
              * ‖(riemannZeta (1 + z₀))⁻¹‖
              * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
              * ‖(R : ℂ) ^ (z₀ + Commons.Analysis.Complex.gam β t)‖ * ‖(z₀^2)⁻¹‖
            ≤ B * (Czb * (1 + |t|) ^ δmax) * ‖(riemannZeta (1 + z₀))⁻¹‖
              * (C₁ * (Real.log (2 + |t|) + 1)) * 1 * ‖(z₀^2)⁻¹‖ := by
          refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1m h2m (norm_nonneg _) hBnn)
            le_rfl (norm_nonneg _) hA1) h4m (norm_nonneg _) hA2) h5m (norm_nonneg _) hA3)
            le_rfl (norm_nonneg _) hA4
        exact mul_le_mul hX h7m' (by positivity) hA5
      have hfin : B * (Czb * (1 + |t|) ^ δmax) * ‖(riemannZeta (1 + z₀))⁻¹‖
            * (C₁ * (Real.log (2 + |t|) + 1)) * 1 * ‖(z₀^2)⁻¹‖
            * (Commons.Analysis.Complex.curveConst β * (1 + t^2)⁻¹)
          ≤ Dtot * (1 + t^2) ^ (-((3:ℝ)/5)) := by
        rw [hDtot]
        have hCconst : 0 ≤ B * Czb * ‖(riemannZeta (1 + z₀))⁻¹‖ * C₁ * ‖(z₀^2)⁻¹‖
            * Commons.Analysis.Complex.curveConst β := by
          have e1 : 0 ≤ B * Czb := mul_nonneg hBnn hCzb_nn
          have e2 : 0 ≤ B * Czb * ‖(riemannZeta (1 + z₀))⁻¹‖ := mul_nonneg e1 (norm_nonneg _)
          have e3 : 0 ≤ B * Czb * ‖(riemannZeta (1 + z₀))⁻¹‖ * C₁ := mul_nonneg e2 hC1.le
          have e4 : 0 ≤ B * Czb * ‖(riemannZeta (1 + z₀))⁻¹‖ * C₁ * ‖(z₀^2)⁻¹‖ := mul_nonneg e3 (norm_nonneg _)
          exact mul_nonneg e4 (Commons.Analysis.Complex.curveConst_pos hβ).le
        calc B * (Czb * (1 + |t|) ^ δmax) * ‖(riemannZeta (1 + z₀))⁻¹‖
              * (C₁ * (Real.log (2 + |t|) + 1)) * 1 * ‖(z₀^2)⁻¹‖
              * (Commons.Analysis.Complex.curveConst β * (1 + t^2)⁻¹)
            = (B * Czb * ‖(riemannZeta (1 + z₀))⁻¹‖ * C₁ * ‖(z₀^2)⁻¹‖
                * Commons.Analysis.Complex.curveConst β)
              * ((1 + |t|) ^ δmax * (Real.log (2 + |t|) + 1) * (1 + t^2)⁻¹) := by ring
          _ ≤ (B * Czb * ‖(riemannZeta (1 + z₀))⁻¹‖ * C₁ * ‖(z₀^2)⁻¹‖
                * Commons.Analysis.Complex.curveConst β)
              * (2 ^ (δmax / 2) * (Real.log 3 + 3) * (1 + t^2) ^ (-((3:ℝ)/5))) :=
              mul_le_mul_of_nonneg_left hstep3 hCconst
          _ = B * Czb * ‖(riemannZeta (1 + z₀))⁻¹‖ * C₁ * ‖(z₀^2)⁻¹‖
                * Commons.Analysis.Complex.curveConst β
              * 2 ^ (δmax / 2) * (Real.log 3 + 3) * (1 + t^2) ^ (-((3:ℝ)/5)) := by ring
      exact le_trans hmul hfin
    have hmeas3 : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => g (Commons.Analysis.Complex.gam β t) * Commons.Analysis.Complex.gamDot β t)
        MeasureTheory.volume := by
      have hcont_ggam : Continuous (fun t : ℝ => g (Commons.Analysis.Complex.gam β t)) := by
        rw [continuous_iff_continuousAt]
        intro t
        have hmem : Commons.Analysis.Complex.gam β t ∉ S := by
          rw [hSfin]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          refine ⟨Commons.Analysis.Complex.gam_ne_zero hβ t, ?_⟩
          intro h
          have := congrArg Complex.re h
          rw [Commons.Analysis.Complex.gam_re, Complex.neg_re, hz₀re] at this
          have h2 : 0 ≤ β / Real.log (|t| + 2) :=
            div_nonneg hβ.le (Real.log_nonneg (by linarith [abs_nonneg t]))
          linarith [hβt₀_pos, h2]
        exact ContinuousAt.comp (f := Commons.Analysis.Complex.gam β)
          ((hdiff _ (hgam_reg1 t) (hgam_reg2 t) hmem).continuousAt)
          ((Commons.Analysis.Complex.gam_continuous β).continuousAt)
      have hgamDot_meas : MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ => Commons.Analysis.Complex.gamDot β t) (MeasureTheory.volume : Measure ℝ) :=
        (aestronglyMeasurable_deriv (Commons.Analysis.Complex.gam β) MeasureTheory.volume).congr
          (by filter_upwards [Commons.Analysis.Complex.ae_ne_zero] with t ht
              rw [(Commons.Analysis.Complex.hasDerivAt_gam (β := β) ht).deriv])
      exact hcont_ggam.aestronglyMeasurable.mul hgamDot_meas
    have hdom : MeasureTheory.Integrable (fun t : ℝ => Dtot * (1 + t^2) ^ (-((3:ℝ)/5))) := by
      simpa using
        (Commons.Analysis.Integral.integrable_one_add_sq_rpow_neg ((3:ℝ)/5) (by norm_num)).const_mul Dtot
    refine Integrable.mono' hdom hmeas3 ?_
    filter_upwards with t
    exact hbdd t
  have hint0 : MeasureTheory.Integrable (fun t : ℝ =>
      g (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t) := by
    have hae : (fun t : ℝ => g (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
        =ᵐ[volume] (fun t : ℝ => g (Commons.Analysis.Complex.gam β t) * Commons.Analysis.Complex.gamDot β t) := by
      filter_upwards [Commons.Analysis.Complex.ae_ne_zero] with t ht
      rw [Commons.Analysis.Complex.deriv_phi_curve (β := β) ht]
      simp only [Commons.Analysis.Complex.gam, Commons.Analysis.Complex.phi]
    exact hcurve.congr hae.symm
  have hhoriz : Filter.Tendsto (fun T : ℝ =>
      (∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) + (T:ℂ) * Complex.I))
        - (∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) - (T:ℂ) * Complex.I)))
      Filter.atTop (nhds 0) := by
    obtain ⟨Clog, clog, hClogpos, hclogpos, hlogreg⟩ := ETest.riemannZeta_bound_log_region
    obtain ⟨Cv, hCvpos, hCvspec⟩ := zeta_strip_conv_bound
    set Kz : ℝ := (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
      * (|t₀| + 3) ^ ((1:ℝ)/2) with hKz
    have hlog3nn : 0 ≤ Real.log (|t₀| + 3) + 1 := by
      have h : 0 ≤ Real.log (|t₀| + 3) := Real.log_nonneg (by linarith [abs_nonneg t₀])
      linarith
    have hlog3pos : 0 < Real.log (|t₀| + 3) + 1 := by
      have h : 0 < Real.log (|t₀| + 3) := Real.log_pos (by linarith [abs_nonneg t₀])
      linarith
    have hr3pos : 0 < (|t₀| + 3) ^ ((1:ℝ)/2) :=
      Real.rpow_pos_of_pos (by linarith [abs_nonneg t₀]) _
    have hKzpos : 0 < Kz := by
      rw [hKz]
      have hcp : 0 < Cv / clog + Clog + Cv + 1 := by
        have h := div_pos hCvpos hclogpos
        linarith only [h, hClogpos, hCvpos]
      exact mul_pos (mul_pos hcp hlog3pos) hr3pos
    have hzpt : ∀ T u s : ℝ, |t₀| + 4 ≤ T → |s| = T → -(β / Real.log (T + 2)) ≤ u → u ≤ 1 →
        ‖riemannZeta (1 + z₀ + ((u:ℂ) + (s:ℂ)*Complex.I))‖
          ≤ Kz * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1) := by
      intro T u s hT hs hu1 hu2
      have hTpos : 0 < T := by linarith [abs_nonneg t₀]
      have hlogT2 : 0 < Real.log (T + 2) := Real.log_pos (by linarith [abs_nonneg t₀])
      have hτge : 3 ≤ |t₀ + s| := by
        have h1 : |s| ≤ |t₀ + s| + |t₀| := by
          rw [show s = (t₀ + s) + (-t₀) by ring]
          simpa using abs_add_le (t₀ + s) (-t₀)
        rw [hs] at h1
        linarith only [h1, hT, abs_nonneg t₀]
      have hτ1 : 1 ≤ |t₀ + s| := by linarith only [hτge]
      have hlogτpos : 0 < Real.log (|t₀ + s| + 2) :=
        Real.log_pos (by linarith only [abs_nonneg (t₀ + s)])
      have hσlo : (1/2 : ℝ) ≤ 1 + z₀.re + u := by
        rw [hz₀re]
        have h1 : β / Real.log (T + 2) ≤ β / Real.log 2 :=
          div_le_div_of_nonneg_left hβ.le hlog2pos
            (Real.log_le_log (by norm_num) (by linarith only [hT, abs_nonneg t₀]))
        have h2 : β / Real.log (|t₀| + 2) ≤ β / Real.log 2 :=
          div_le_div_of_nonneg_left hβ.le hlog2pos
            (Real.log_le_log (by norm_num) (by linarith only [abs_nonneg t₀]))
        have hlog2' : (2:ℝ)/5 < Real.log 2 := by linarith only [Real.log_two_gt_d9]
        have h3 : 2 * (β / Real.log 2) ≤ 1/2 := by
          rw [show 2 * (β / Real.log 2) = 2 * β / Real.log 2 by ring, div_le_iff₀ hlog2pos]
          linarith only [hβ10, hlog2']
        linarith only [h1, h2, h3, hu1]
      have harg : 1 + z₀ + ((u:ℂ) + (s:ℂ)*Complex.I)
          = ((1 + z₀.re + u : ℝ) : ℂ) + ((t₀ + s : ℝ) : ℂ) * Complex.I := by
        rw [hz₀]
        apply Complex.ext <;>
          simp [Commons.Analysis.Complex.gam, Commons.Analysis.Complex.phi] <;> ring
      have hlogb : Real.log (|t₀ + s| + 2)
          ≤ (Real.log (|t₀| + 3) + 1) * (Real.log (T + 2) + 1) := by
        have h1 : |t₀ + s| + 2 ≤ (|t₀| + 3) * (T + 2) := by
          have h2 : |t₀ + s| ≤ |t₀| + T := by
            calc |t₀ + s| ≤ |t₀| + |s| := abs_add_le _ _
              _ = |t₀| + T := by rw [hs]
          nlinarith only [h2, abs_nonneg t₀, hT]
        calc Real.log (|t₀ + s| + 2) ≤ Real.log ((|t₀| + 3) * (T + 2)) :=
              Real.log_le_log (by linarith only [abs_nonneg (t₀ + s)]) h1
          _ = Real.log (|t₀| + 3) + Real.log (T + 2) :=
              Real.log_mul (by linarith only [abs_nonneg t₀]) (by linarith only [abs_nonneg t₀, hT])
          _ ≤ (Real.log (|t₀| + 3) + 1) * (Real.log (T + 2) + 1) := by
              have hA : 0 ≤ Real.log (|t₀| + 3) := Real.log_nonneg (by linarith only [abs_nonneg t₀])
              nlinarith only [hA, hlogT2.le]
      rw [harg]
      by_cases hcase : 1 - clog / Real.log (|t₀ + s| + 2) ≤ 1 + z₀.re + u
      · have hb := hlogreg (1 + z₀.re + u) (t₀ + s) hτ1 hcase
        have h1T : (1:ℝ) ≤ (1 + T) ^ ((1:ℝ)/2) :=
          Real.one_le_rpow (by linarith) (by norm_num)
        have hKzge : Clog * (Real.log (|t₀| + 3) + 1) ≤ Kz * (1 + T) ^ ((1:ℝ)/2) := by
          rw [hKz]
          have h2 : Clog ≤ Cv / clog + Clog + Cv + 1 := by
            have h := div_pos hCvpos hclogpos
            linarith only [hClogpos, hCvpos, h]
          have h3 : Clog * (Real.log (|t₀| + 3) + 1)
              ≤ (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1) :=
            mul_le_mul_of_nonneg_right h2 hlog3nn
          have h4 : (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
              ≤ (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
                * (1 + T) ^ ((1:ℝ)/2) := by
            have hnn : 0 ≤ (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1) := by
              have h := div_pos hCvpos hclogpos
              have hcp : 0 < Cv / clog + Clog + Cv + 1 := by linarith only [hClogpos, hCvpos, h]
              positivity
            calc (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
                = (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1) * 1 := by ring
              _ ≤ (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
                    * (1 + T) ^ ((1:ℝ)/2) := mul_le_mul_of_nonneg_left h1T hnn
          have h5 : (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
                * (1 + T) ^ ((1:ℝ)/2)
              ≤ (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
                * (|t₀| + 3) ^ ((1:ℝ)/2) * (1 + T) ^ ((1:ℝ)/2) := by
            have hr1 : (1:ℝ) ≤ (|t₀| + 3) ^ ((1:ℝ)/2) :=
              Real.one_le_rpow (by linarith only [abs_nonneg t₀]) (by norm_num)
            have hnn : 0 ≤ (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
                * (1 + T) ^ ((1:ℝ)/2) := by
              have h := div_pos hCvpos hclogpos
              have hcp : 0 < Cv / clog + Clog + Cv + 1 := by linarith only [hClogpos, hCvpos, h]
              positivity
            calc (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1) * (1 + T) ^ ((1:ℝ)/2)
                = (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
                    * (1 + T) ^ ((1:ℝ)/2) * 1 := by ring
              _ ≤ (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
                    * (1 + T) ^ ((1:ℝ)/2) * (|t₀| + 3) ^ ((1:ℝ)/2) :=
                  mul_le_mul_of_nonneg_left hr1 hnn
              _ = (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
                    * (|t₀| + 3) ^ ((1:ℝ)/2) * (1 + T) ^ ((1:ℝ)/2) := by ring
          linarith only [h3, h4, h5]
        calc ‖riemannZeta (↑(1 + z₀.re + u) + ↑(t₀ + s) * Complex.I)‖
            ≤ Clog * Real.log (|t₀ + s| + 2) := hb
          _ ≤ Clog * ((Real.log (|t₀| + 3) + 1) * (Real.log (T + 2) + 1)) :=
              mul_le_mul_of_nonneg_left hlogb hClogpos.le
          _ = Clog * (Real.log (|t₀| + 3) + 1) * (Real.log (T + 2) + 1) := by ring
          _ ≤ Kz * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1) :=
              mul_le_mul_of_nonneg_right hKzge (by linarith only [hlogT2.le])
      · push_neg at hcase
        have hdivpos : 0 < clog / Real.log (|t₀ + s| + 2) := div_pos hclogpos hlogτpos
        have hσlt : 1 + z₀.re + u < 1 := by linarith only [hcase, hdivpos]
        have hexppos : 0 < 1 - (1 + z₀.re + u) := by linarith only [hcase, hdivpos]
        have hb := hCvspec (1 + z₀.re + u) |t₀ + s| hσlo hσlt hτge
        have hsym : ((1 + z₀.re + u : ℝ) : ℂ) + ((t₀ + s : ℝ) : ℂ) * Complex.I
            = ((1 + z₀.re + u : ℝ) : ℂ) + Complex.I * ((t₀ + s : ℝ) : ℂ) := by rw [mul_comm]
        rw [hsym, ← norm_riemannZeta_abs_im (1 + z₀.re + u) (t₀ + s)]
        refine le_trans hb ?_
        have hinvσ : 1 / (1 - (1 + z₀.re + u)) ≤ Real.log (|t₀ + s| + 2) / clog := by
          have hcloglt : clog / Real.log (|t₀ + s| + 2) < 1 - (1 + z₀.re + u) := by
            linarith only [hcase]
          have hkey : clog < (1 - (1 + z₀.re + u)) * Real.log (|t₀ + s| + 2) :=
            (div_lt_iff₀ hlogτpos).mp hcloglt
          rw [div_le_div_iff₀ hexppos hclogpos]
          linarith only [hkey, mul_comm (1 - (1 + z₀.re + u)) (Real.log (|t₀ + s| + 2))]
        have hexp_le : 1 - (1 + z₀.re + u) ≤ 1/2 := by
          rw [hz₀re]
          have h1 : 0 ≤ β / Real.log (T + 2) :=
            div_nonneg hβ.le (Real.log_nonneg (by linarith only [hT, abs_nonneg t₀]))
          have h3 : β / Real.log (|t₀| + 2) + β / Real.log 2 ≤ 1/2 := by
            have h4 : β / Real.log (|t₀| + 2) ≤ β / Real.log 2 :=
              div_le_div_of_nonneg_left hβ.le hlog2pos
                (Real.log_le_log (by norm_num) (by linarith only [abs_nonneg t₀]))
            have h5 : 2 * (β / Real.log 2) ≤ 1/2 := by
              rw [show 2 * (β / Real.log 2) = 2 * β / Real.log 2 by ring, div_le_iff₀ hlog2pos]
              have hlog2' : (2:ℝ)/5 < Real.log 2 := by linarith only [Real.log_two_gt_d9]
              linarith only [hβ10, hlog2']
            linarith only [h4, h5]
          have h6 : β / Real.log (T + 2) ≤ β / Real.log 2 :=
            div_le_div_of_nonneg_left hβ.le hlog2pos
              (Real.log_le_log (by norm_num) (by linarith only [hT, abs_nonneg t₀]))
          linarith only [h1, h3, h6, hu1]
        have hpowτ : (|t₀ + s| + 3) ^ (1 - (1 + z₀.re + u))
            ≤ (|t₀| + 3) ^ ((1:ℝ)/2) * (1 + T) ^ ((1:ℝ)/2) := by
          have hbase : |t₀ + s| + 3 ≤ (|t₀| + 3) * (1 + T) := by
            have h2 : |t₀ + s| ≤ |t₀| + T := by
              calc |t₀ + s| ≤ |t₀| + |s| := abs_add_le _ _
                _ = |t₀| + T := by rw [hs]
            nlinarith only [h2, abs_nonneg t₀, hT]
          calc (|t₀ + s| + 3) ^ (1 - (1 + z₀.re + u))
              ≤ ((|t₀| + 3) * (1 + T)) ^ (1 - (1 + z₀.re + u)) :=
                Real.rpow_le_rpow (by positivity) hbase hexppos.le
            _ = (|t₀| + 3) ^ (1 - (1 + z₀.re + u)) * (1 + T) ^ (1 - (1 + z₀.re + u)) :=
                Real.mul_rpow (by linarith only [abs_nonneg t₀]) (by linarith only [hT, abs_nonneg t₀])
            _ ≤ (|t₀| + 3) ^ ((1:ℝ)/2) * (1 + T) ^ ((1:ℝ)/2) := by
                apply mul_le_mul
                · exact Real.rpow_le_rpow_of_exponent_le (by linarith only [abs_nonneg t₀]) hexp_le
                · exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hT, abs_nonneg t₀]) hexp_le
                · exact Real.rpow_nonneg (by linarith only [hT, abs_nonneg t₀]) _
                · exact Real.rpow_nonneg (by linarith only [abs_nonneg t₀]) _
        have hstep1 : Cv * (1 / (1 - (1 + z₀.re + u))) * (|t₀ + s| + 3) ^ (1 - (1 + z₀.re + u))
            ≤ (Cv / clog) * (Real.log (|t₀| + 3) + 1) * (Real.log (T + 2) + 1)
              * ((|t₀| + 3) ^ ((1:ℝ)/2) * (1 + T) ^ ((1:ℝ)/2)) := by
          have hCv1 : Cv * (1 / (1 - (1 + z₀.re + u))) ≤ (Cv / clog) * Real.log (|t₀ + s| + 2) := by
            calc Cv * (1 / (1 - (1 + z₀.re + u))) ≤ Cv * (Real.log (|t₀ + s| + 2) / clog) :=
                  mul_le_mul_of_nonneg_left hinvσ hCvpos.le
              _ = (Cv / clog) * Real.log (|t₀ + s| + 2) := by ring
          have hlogb2 : (Cv / clog) * Real.log (|t₀ + s| + 2)
              ≤ (Cv / clog) * ((Real.log (|t₀| + 3) + 1) * (Real.log (T + 2) + 1)) :=
            mul_le_mul_of_nonneg_left hlogb (by positivity)
          calc Cv * (1 / (1 - (1 + z₀.re + u))) * (|t₀ + s| + 3) ^ (1 - (1 + z₀.re + u))
              ≤ ((Cv / clog) * Real.log (|t₀ + s| + 2))
                  * ((|t₀| + 3) ^ ((1:ℝ)/2) * (1 + T) ^ ((1:ℝ)/2)) :=
                mul_le_mul hCv1 hpowτ (Real.rpow_nonneg (by linarith only [abs_nonneg (t₀+s)]) _)
                  (by positivity)
            _ ≤ ((Cv / clog) * ((Real.log (|t₀| + 3) + 1) * (Real.log (T + 2) + 1)))
                  * ((|t₀| + 3) ^ ((1:ℝ)/2) * (1 + T) ^ ((1:ℝ)/2)) :=
                mul_le_mul_of_nonneg_right hlogb2 (by positivity)
            _ = (Cv / clog) * (Real.log (|t₀| + 3) + 1) * (Real.log (T + 2) + 1)
                  * ((|t₀| + 3) ^ ((1:ℝ)/2) * (1 + T) ^ ((1:ℝ)/2)) := by ring
        refine le_trans hstep1 ?_
        rw [hKz]
        have hclogCv : Cv / clog ≤ (Cv / clog + Clog + Cv + 1) := by
          have hcp : 0 < Cv / clog := div_pos hCvpos hclogpos
          linarith only [hClogpos, hCvpos, hcp]
        calc (Cv / clog) * (Real.log (|t₀| + 3) + 1) * (Real.log (T + 2) + 1)
                * ((|t₀| + 3) ^ ((1:ℝ)/2) * (1 + T) ^ ((1:ℝ)/2))
            = (Cv / clog) * (Real.log (|t₀| + 3) + 1) * (|t₀| + 3) ^ ((1:ℝ)/2)
                * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1) := by ring
          _ ≤ (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1) * (|t₀| + 3) ^ ((1:ℝ)/2)
                * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1) := by
              have e1 : 0 ≤ Real.log (T + 2) + 1 := by linarith only [hlogT2.le]
              have e2 : 0 ≤ (1 + T) ^ ((1:ℝ)/2) := Real.rpow_nonneg (by linarith) _
              have h1 : (Cv / clog) * (Real.log (|t₀| + 3) + 1)
                  ≤ (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1) :=
                mul_le_mul_of_nonneg_right hclogCv hlog3nn
              have h2 : (Cv / clog) * (Real.log (|t₀| + 3) + 1) * (|t₀| + 3) ^ ((1:ℝ)/2)
                  ≤ (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
                    * (|t₀| + 3) ^ ((1:ℝ)/2) :=
                mul_le_mul_of_nonneg_right h1 hr3pos.le
              have h3 : (Cv / clog) * (Real.log (|t₀| + 3) + 1) * (|t₀| + 3) ^ ((1:ℝ)/2)
                    * (1 + T) ^ ((1:ℝ)/2)
                  ≤ (Cv / clog + Clog + Cv + 1) * (Real.log (|t₀| + 3) + 1)
                    * (|t₀| + 3) ^ ((1:ℝ)/2) * (1 + T) ^ ((1:ℝ)/2) :=
                mul_le_mul_of_nonneg_right h2 e2
              exact mul_le_mul_of_nonneg_right h3 e1
    set Kg : ℝ := B * Kz * ‖(riemannZeta (1 + z₀))⁻¹‖ * C₁ * R * ‖(z₀ ^ 2)⁻¹‖ with hKg
    have hKgnn : 0 ≤ Kg := by
      rw [hKg]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hBnn hKzpos.le)
        (norm_nonneg _)) hC1.le) (by linarith)) (norm_nonneg _)
    have hgbnd : ∀ T u s : ℝ, |t₀| + 4 ≤ T → |s| = T → -(β / Real.log (T + 2)) ≤ u → u ≤ 1 →
        ‖g ((u:ℂ) + (s:ℂ)*Complex.I)‖
          ≤ Kg * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1)^2 / T^2 := by
      intro T u s hT hs hu1 hu2
      have hTpos : 0 < T := by linarith [abs_nonneg t₀]
      have hlogT2 : 0 < Real.log (T + 2) := Real.log_pos (by linarith [abs_nonneg t₀])
      set w : ℂ := (u:ℂ) + (s:ℂ)*Complex.I with hw
      have hwre : w.re = u := by simp [hw]
      have hwim : w.im = s := by simp [hw]
      have hwne : w ≠ 0 := by
        intro hh
        have h1 : w.im = 0 := by rw [hh]; simp
        rw [hwim] at h1
        have hT0 : T = 0 := by rw [← hs, h1]; simp
        linarith only [hT0, hTpos]
      have hwreg1 : -(β / Real.log (|w.im| + 2)) ≤ w.re := by rw [hwim, hwre, hs]; exact hu1
      have hwreg2 : w.re ≤ 1 := by rw [hwre]; exact hu2
      have hf : ‖f z₀ w‖ ≤ B := hbound z₀ w hz₀reg1 hz₀reg2 hwreg1 hwreg2
      have hz : ‖riemannZeta (1 + z₀ + w)‖
          ≤ Kz * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1) := by
        have h := hzpt T u s hT hs hu1 hu2
        rwa [← hw] at h
      have hzinv : ‖(riemannZeta (1 + w))⁻¹‖ ≤ C₁ * (Real.log (T + 2) + 1) := by
        have h := hinvb w hwne hwreg1 hwreg2
        rw [hwim, hs] at h
        exact h
      have hR : ‖(R : ℂ) ^ (z₀ + w)‖ ≤ R := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ) < R)]
        have hexp : (z₀ + w).re ≤ 1 := by
          rw [Complex.add_re, hz₀re, hwre]
          linarith only [hβt₀_pos.le, hu2]
        calc R ^ (z₀ + w).re ≤ R ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
          _ = R := Real.rpow_one R
      have hw2 : ‖(w ^ 2)⁻¹‖ ≤ (T ^ 2)⁻¹ := by
        rw [norm_inv, norm_pow]
        have hnorm : ‖w‖ ^ 2 = u ^ 2 + s ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim]; ring
        rw [hnorm, ← sq_abs s, hs]
        exact inv_anti₀ (by positivity) (by nlinarith only [sq_nonneg u])
      have hfac : g w = f z₀ w * riemannZeta (1 + z₀ + w) * (riemannZeta (1 + z₀))⁻¹
          * (riemannZeta (1 + w))⁻¹ * (R : ℂ) ^ (z₀ + w) * (z₀ ^ 2)⁻¹ * (w ^ 2)⁻¹ := by
        rw [hg]; simp only [div_eq_mul_inv, mul_inv]; ring
      rw [hfac]
      simp only [norm_mul]
      have hzb : 0 ≤ Kz * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1) := by
        have h1 : 0 ≤ (1 + T) ^ ((1:ℝ)/2) := Real.rpow_nonneg (by linarith) _
        have h2 : 0 ≤ Real.log (T + 2) + 1 := by linarith only [hlogT2.le]
        positivity
      have hc1 : 0 ≤ B * (Kz * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1)) :=
        mul_nonneg hBnn hzb
      have hmul1 : ‖f z₀ w‖ * ‖riemannZeta (1 + z₀ + w)‖
          ≤ B * (Kz * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1)) :=
        mul_le_mul hf hz (norm_nonneg _) hBnn
      have hmul2 : ‖f z₀ w‖ * ‖riemannZeta (1 + z₀ + w)‖ * ‖(riemannZeta (1 + z₀))⁻¹‖
          ≤ B * (Kz * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1))
            * ‖(riemannZeta (1 + z₀))⁻¹‖ :=
        mul_le_mul_of_nonneg_right hmul1 (norm_nonneg _)
      have hmul3 : ‖f z₀ w‖ * ‖riemannZeta (1 + z₀ + w)‖ * ‖(riemannZeta (1 + z₀))⁻¹‖
          * ‖(riemannZeta (1 + w))⁻¹‖
          ≤ B * (Kz * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1))
            * ‖(riemannZeta (1 + z₀))⁻¹‖ * (C₁ * (Real.log (T + 2) + 1)) :=
        mul_le_mul hmul2 hzinv (norm_nonneg _) (by positivity)
      have hmul4 : ‖f z₀ w‖ * ‖riemannZeta (1 + z₀ + w)‖ * ‖(riemannZeta (1 + z₀))⁻¹‖
          * ‖(riemannZeta (1 + w))⁻¹‖ * ‖(R : ℂ) ^ (z₀ + w)‖
          ≤ B * (Kz * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1))
            * ‖(riemannZeta (1 + z₀))⁻¹‖ * (C₁ * (Real.log (T + 2) + 1)) * R :=
        mul_le_mul hmul3 hR (norm_nonneg _) (by positivity)
      have hmul5 : ‖f z₀ w‖ * ‖riemannZeta (1 + z₀ + w)‖ * ‖(riemannZeta (1 + z₀))⁻¹‖
          * ‖(riemannZeta (1 + w))⁻¹‖ * ‖(R : ℂ) ^ (z₀ + w)‖ * ‖(z₀ ^ 2)⁻¹‖
          ≤ B * (Kz * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1))
            * ‖(riemannZeta (1 + z₀))⁻¹‖ * (C₁ * (Real.log (T + 2) + 1)) * R * ‖(z₀ ^ 2)⁻¹‖ :=
        mul_le_mul_of_nonneg_right hmul4 (norm_nonneg _)
      have hmul6 : ‖f z₀ w‖ * ‖riemannZeta (1 + z₀ + w)‖ * ‖(riemannZeta (1 + z₀))⁻¹‖
          * ‖(riemannZeta (1 + w))⁻¹‖ * ‖(R : ℂ) ^ (z₀ + w)‖ * ‖(z₀ ^ 2)⁻¹‖ * ‖(w ^ 2)⁻¹‖
          ≤ B * (Kz * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1))
            * ‖(riemannZeta (1 + z₀))⁻¹‖ * (C₁ * (Real.log (T + 2) + 1)) * R * ‖(z₀ ^ 2)⁻¹‖
            * (T ^ 2)⁻¹ :=
        mul_le_mul hmul5 hw2 (norm_nonneg _) (by positivity)
      refine le_trans hmul6 (le_of_eq ?_)
      rw [hKg, div_eq_mul_inv]
      ring
    have hInt : ∀ᶠ T : ℝ in Filter.atTop,
        ‖(∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) + (T:ℂ) * Complex.I))
          - (∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) - (T:ℂ) * Complex.I))‖
        ≤ (2 * Kg * (1 + β / Real.log 2)) * (1 + T) ^ ((1:ℝ)/2)
            * (Real.log (T + 2) + 1)^2 / T^2 := by
      filter_upwards [Filter.eventually_ge_atTop (|t₀| + 4)] with T hT
      have hTpos : 0 < T := by linarith [abs_nonneg t₀]
      have hlogT2 : 0 < Real.log (T + 2) :=
        Real.log_pos (by linarith only [abs_nonneg t₀, hT])
      have hbpos : 0 < β / Real.log (T + 2) := div_pos hβ hlogT2
      have ha_le : -(β / Real.log (T + 2)) ≤ 1 := by linarith only [hbpos]
      have habs : |(1:ℝ) - (-(β / Real.log (T + 2)))| = 1 + β / Real.log (T + 2) := by
        rw [sub_neg_eq_add, abs_of_pos (by linarith only [hbpos])]
      have hlenle : 1 + β / Real.log (T + 2) ≤ 1 + β / Real.log 2 := by
        have h1 : Real.log 2 ≤ Real.log (T + 2) := Real.log_le_log (by norm_num) (by linarith)
        have h2 : β / Real.log (T + 2) ≤ β / Real.log 2 :=
          div_le_div_of_nonneg_left hβ.le hlog2pos h1
        linarith only [h2]
      set S : ℝ := Kg * (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1)^2 / T^2 with hSdef
      have hSnn : 0 ≤ S := by
        rw [hSdef]
        have h1 : 0 ≤ (1 + T) ^ ((1:ℝ)/2) := Real.rpow_nonneg (by linarith) _
        have h2 : 0 ≤ Real.log (T + 2) + 1 := by linarith only [hlogT2.le]
        positivity
      have hsingle : ∀ s : ℝ, |s| = T →
          ‖∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) + (s:ℂ)*Complex.I)‖
            ≤ S * (1 + β / Real.log 2) := by
        intro s hs
        have hmain : ‖∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) + (s:ℂ)*Complex.I)‖
            ≤ S * (1 + β / Real.log (T + 2)) := by
          have h := intervalIntegral.norm_integral_le_of_norm_le_const
            (a := -(β / Real.log (T + 2))) (b := (1:ℝ)) (C := S)
            (f := fun u : ℝ => g ((u:ℂ) + (s:ℂ)*Complex.I)) (fun u hu => ?_)
          · rwa [habs] at h
          · rw [Set.uIoc_of_le ha_le] at hu
            have hh := hgbnd T u s hT hs hu.1.le hu.2
            rwa [hSdef]
        exact le_trans hmain (mul_le_mul_of_nonneg_left hlenle hSnn)
      have hb1 := hsingle T (abs_of_pos hTpos)
      have hb2 : ‖∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) - (T:ℂ) * Complex.I)‖
            ≤ S * (1 + β / Real.log 2) := by
        have hIe : (∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) - (T:ℂ) * Complex.I))
            = ∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) + ((-(T):ℝ):ℂ) * Complex.I) := by
          refine intervalIntegral.integral_congr (fun u _ => ?_)
          congr 1; push_cast; ring
        rw [hIe]
        exact hsingle (-T) (by rw [abs_neg, abs_of_pos hTpos])
      calc ‖(∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) + (T:ℂ) * Complex.I))
            - (∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) - (T:ℂ) * Complex.I))‖
          ≤ ‖∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) + (T:ℂ) * Complex.I)‖
            + ‖∫ u in (-(β / Real.log (T + 2)))..(1:ℝ), g ((u:ℂ) - (T:ℂ) * Complex.I)‖ :=
            norm_sub_le _ _
        _ ≤ S * (1 + β / Real.log 2) + S * (1 + β / Real.log 2) := add_le_add hb1 hb2
        _ = (2 * Kg * (1 + β / Real.log 2)) * (1 + T) ^ ((1:ℝ)/2)
              * (Real.log (T + 2) + 1)^2 / T^2 := by
            rw [hSdef, div_eq_mul_inv]; ring
    have hC0nn : 0 ≤ 2 * Kg * (1 + β / Real.log 2) := by
      have hp : 0 < 1 + β / Real.log 2 := by
        have h := div_pos hβ hlog2pos
        linarith only [h]
      exact mul_nonneg (mul_nonneg (by norm_num) hKgnn) hp.le
    have hlim : Filter.Tendsto (fun T : ℝ =>
        (2 * Kg * (1 + β / Real.log 2)) * (1 + T) ^ ((1:ℝ)/2)
          * (Real.log (T + 2) + 1)^2 / T^2)
        Filter.atTop (nhds 0) := by
      have hbdd : ∀ᶠ T : ℝ in Filter.atTop,
          (2 * Kg * (1 + β / Real.log 2)) * (1 + T) ^ ((1:ℝ)/2)
            * (Real.log (T + 2) + 1)^2 / T^2
            ≤ (2 * Kg * (1 + β / Real.log 2)) * (81 * 2 ^ ((1:ℝ)/2)) / T := by
        filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with T hT
        have hTpos : 0 < T := by linarith
        have h1 : (1 + T) ^ ((1:ℝ)/2) ≤ 2 ^ ((1:ℝ)/2) * T ^ ((1:ℝ)/2) := by
          rw [← Real.mul_rpow (by norm_num) (le_of_lt hTpos)]
          exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        have hlog : Real.log (T + 2) + 1 ≤ 9 * T ^ ((1:ℝ)/4) := by
          have h3 : Real.log (T + 2) ≤ (T + 2) ^ ((1:ℝ)/4) / (1/4) :=
            Real.log_le_rpow_div (by linarith) (by norm_num)
          have h4 : (T + 2) ^ ((1:ℝ)/4) ≤ 3 ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4) := by
            rw [← Real.mul_rpow (by norm_num) (le_of_lt hTpos)]
            exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
          have h5 : (3:ℝ) ^ ((1:ℝ)/4) ≤ 2 := by
            rw [Real.rpow_le_iff_le_log (by norm_num) (by norm_num)]
            nlinarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3),
              Real.log_two_gt_d9]
          have h6 : (0:ℝ) ≤ T ^ ((1:ℝ)/4) := Real.rpow_nonneg (le_of_lt hTpos) _
          rw [div_eq_mul_inv] at h3
          rw [show ((1:ℝ)/4)⁻¹ = 4 by norm_num] at h3
          have hlo : Real.log (T + 2) ≤ 8 * T ^ ((1:ℝ)/4) := by nlinarith only [h3, h4, h5, h6]
          have hge1 : (1:ℝ) ≤ T ^ ((1:ℝ)/4) := Real.one_le_rpow hT (by norm_num)
          linarith only [hlo, hge1]
        have hsq : (Real.log (T + 2) + 1)^2 ≤ 81 * T ^ ((1:ℝ)/2) := by
          have hl0 : 0 ≤ Real.log (T + 2) + 1 := by
            have h : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
            linarith
          have h10 : (Real.log (T + 2) + 1)^2 ≤ (9 * T ^ ((1:ℝ)/4))^2 :=
            pow_le_pow_left₀ hl0 hlog 2
          have h11 : (9 * T ^ ((1:ℝ)/4))^2 = 81 * T ^ ((1:ℝ)/2) := by
            rw [mul_pow]
            rw [show (T ^ ((1:ℝ)/4))^2 = T ^ ((1:ℝ)/2) by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hTpos)]
              norm_num]
            norm_num
          rwa [h11] at h10
        have hkey : (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1)^2
            ≤ 81 * 2 ^ ((1:ℝ)/2) * T := by
          have hprod := mul_le_mul h1 hsq (by positivity) (by positivity)
          have hTs : T ^ ((1:ℝ)/2) * T ^ ((1:ℝ)/2) = T := by
            rw [← Real.rpow_add hTpos, show (1:ℝ)/2 + 1/2 = 1 by norm_num, Real.rpow_one]
          calc (1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1)^2
              ≤ (2 ^ ((1:ℝ)/2) * T ^ ((1:ℝ)/2)) * (81 * T ^ ((1:ℝ)/2)) := hprod
            _ = 81 * 2 ^ ((1:ℝ)/2) * (T ^ ((1:ℝ)/2) * T ^ ((1:ℝ)/2)) := by ring
            _ = 81 * 2 ^ ((1:ℝ)/2) * T := by rw [hTs]
        calc (2 * Kg * (1 + β / Real.log 2)) * (1 + T) ^ ((1:ℝ)/2)
              * (Real.log (T + 2) + 1)^2 / T^2
            = (2 * Kg * (1 + β / Real.log 2))
                * ((1 + T) ^ ((1:ℝ)/2) * (Real.log (T + 2) + 1)^2) / T^2 := by ring
          _ ≤ (2 * Kg * (1 + β / Real.log 2)) * (81 * 2 ^ ((1:ℝ)/2) * T) / T^2 := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hkey hC0nn
          _ = (2 * Kg * (1 + β / Real.log 2)) * (81 * 2 ^ ((1:ℝ)/2)) / T := by
              field_simp
      refine squeeze_zero' ?_ hbdd ?_
      · filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with T hT
        exact div_nonneg (mul_nonneg (mul_nonneg hC0nn (Real.rpow_nonneg (by linarith) _))
          (sq_nonneg _)) (by positivity)
      · have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul
          ((2 * Kg * (1 + β / Real.log 2)) * (81 * 2 ^ ((1:ℝ)/2)))
        rw [mul_zero] at h
        exact h.congr (fun T => by ring)
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _)) hInt hlim)

  have key := Commons.Analysis.Complex.contour_shift_residue_multi (β := β) (c := 1) hβ (by norm_num)
    g S res hS hdiff hres hint1 hint0 hhoriz
  have hderiveq : (∫ t : ℝ, g (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
      = ∫ t : ℝ, g (Commons.Analysis.Complex.gam β t) * Commons.Analysis.Complex.gamDot β t := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Commons.Analysis.Complex.ae_ne_zero] with t ht
    rw [Commons.Analysis.Complex.deriv_phi_curve (β := β) ht]
    simp only [Commons.Analysis.Complex.gam, Commons.Analysis.Complex.phi]
  have hsumres : (∑ s ∈ S, res s) = f z₀ 0 * (R : ℂ) ^ z₀ / z₀ ^ 2
      + f z₀ (-z₀) / (riemannZeta (1 + z₀) * riemannZeta (1 - z₀) * z₀ ^ 4) := by
    rw [hSfin, Finset.sum_insert (by simp [hz₀ne])]
    rw [hresdef]; simp [hz₀ne]
  have key' : (∫ t : ℝ, g ((1:ℂ) + (t:ℂ) * Complex.I) * Complex.I)
      = (∫ t : ℝ, g (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
        + 2 * Real.pi * Complex.I * ∑ s ∈ S, res s := by
    have h : ((1:ℝ):ℂ) = (1:ℂ) := by norm_num
    simpa only [h] using key
  rw [key', hderiveq, hsumres]

end

end Commons.NumberTheory.Zeta
