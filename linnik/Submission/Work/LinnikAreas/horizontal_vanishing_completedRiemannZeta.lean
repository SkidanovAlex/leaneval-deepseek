import Mathlib
import Submission.Work.LinnikAreas.ZetaTentPrelude
import Submission.Work.LinnikAreas.zeta1_goodHeight_horizontal_vanishing
import Submission.Work.LinnikAreas.logDeriv_completedRiemannZeta_eq

namespace Work.LinnikAreas

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-! ## Auxiliary lemmas -/

/-- `logDeriv riemannZeta₁` is continuous at every point where `riemannZeta₁` does not vanish. -/
lemma continuousAt_logDeriv_riemannZeta₁ {s : ℂ} (hs : riemannZeta₁ s ≠ 0) :
    ContinuousAt (logDeriv riemannZeta₁) s := by
  have hd : ContinuousAt (deriv riemannZeta₁) s :=
    differentiable_riemannZeta₁.deriv.continuous.continuousAt
  have h := hd.div differentiable_riemannZeta₁.continuous.continuousAt hs
  simpa only [logDeriv] using h

/-- `Γℝ` is differentiable at every point where it does not vanish. -/
lemma differentiableAt_Gammaℝ_of_ne_zero {s : ℂ} (hs : Complex.Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    apply hs
    rw [Complex.Gammaℝ_eq_zero_iff]
    refine ⟨m, ?_⟩
    have h2 : s = 2 * (s / 2) := by ring
    rw [h2, hm]
    ring
  rw [show Complex.Gammaℝ = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)
      from funext fun z => Complex.Gammaℝ_def z]
  refine DifferentiableAt.mul ?_ ?_
  · have hz : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
    exact hz.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact (Complex.differentiableAt_Gamma (s / 2) hne).comp s (by fun_prop)

/-- Functional equation for the logarithmic derivative of `Γℝ`:
`(Γℝ'/Γℝ)(s+2) = (Γℝ'/Γℝ)(s) + 1/s`. -/
lemma logDeriv_Gammaℝ_add_two {s : ℂ} (hs : s ≠ 0) (hG : Complex.Gammaℝ s ≠ 0) :
    logDeriv Complex.Gammaℝ (s + 2) = logDeriv Complex.Gammaℝ s + s⁻¹ := by
  have hd : DifferentiableAt ℂ Complex.Gammaℝ s := differentiableAt_Gammaℝ_of_ne_zero hG
  have hG2 : Complex.Gammaℝ (s + 2) ≠ 0 := by
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    apply hG
    rw [Complex.Gammaℝ_eq_zero_iff]
    refine ⟨n + 1, ?_⟩
    have h1 : s = -(2 * ↑n) - 2 := by linear_combination hn
    rw [h1]
    push_cast
    ring
  have hd2 : DifferentiableAt ℂ Complex.Gammaℝ (s + 2) := differentiableAt_Gammaℝ_of_ne_zero hG2
  have hcomp : logDeriv (fun t : ℂ => Complex.Gammaℝ (t + 2)) s
      = logDeriv Complex.Gammaℝ (s + 2) := by
    have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun t : ℂ => t + 2) (x := s)
      hd2 (by fun_prop)
    have hder : deriv (fun t : ℂ => t + 2) s = 1 := by simp
    rw [hder, mul_one] at h
    simpa [Function.comp_def] using h
  have hE : (fun t : ℂ => Complex.Gammaℝ (t + 2))
      =ᶠ[nhds s] (fun t : ℂ => Complex.Gammaℝ t * (t / 2 / (Real.pi : ℂ))) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht
    rw [Complex.Gammaℝ_add_two ht]
    ring
  have hcongr : logDeriv (fun t : ℂ => Complex.Gammaℝ (t + 2)) s
      = logDeriv (fun t : ℂ => Complex.Gammaℝ t * (t / 2 / (Real.pi : ℂ))) s :=
    Filter.EventuallyEq.eq_of_nhds (logDeriv_congr_nhds hE)
  have hne2 : s / 2 / (Real.pi : ℂ) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    exact div_ne_zero (div_ne_zero hs h2) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [← hcomp, hcongr]
  erw [logDeriv_mul s hG hne2 hd (by fun_prop)]
  congr 1
  have hfun : (fun t : ℂ => t / 2 / (Real.pi : ℂ))
      = fun t : ℂ => ((2 * (Real.pi : ℂ))⁻¹) * t := by
    funext t; ring
  rw [hfun]
  have hconst : logDeriv (fun t : ℂ => ((2 * (Real.pi : ℂ))⁻¹) * t) s = s⁻¹ := by
    have h := logDeriv_const_mul (x := s) (f := fun t : ℂ => t)
      ((2 * (Real.pi : ℂ))⁻¹) (by simp [Real.pi_ne_zero])
    simpa using h
  exact hconst

/-- The pointwise identity linking the logarithmic derivatives of the completed and the
principal `ζ`-functions, in the shifted form adapted to the segment `Re s ∈ [-1/2, 2]`:
`(Λ'/Λ)(s) = (Γℝ'/Γℝ)(s+2) - 1/s - 1/(s-1) + (ζ₁'/ζ₁)(s)`. -/
lemma logDeriv_completedRiemannZeta_eq_shift {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hsre : -(1 : ℝ) < s.re) (hG : Complex.Gammaℝ s ≠ 0) (hζ : riemannZeta₁ s ≠ 0) :
    logDeriv completedRiemannZeta s
      = logDeriv Complex.Gammaℝ (s + 2) - s⁻¹ - (s - 1)⁻¹ + logDeriv riemannZeta₁ s := by
  have hz : riemannZeta s ≠ 0 := by
    rw [riemannZeta_eq_inv_sub_mul hs1]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs1)) hζ
  have h1 := logDeriv_completedRiemannZeta_eq hs0 hs1 hsre hz
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h2 : logDeriv riemannZeta s = -(s - 1)⁻¹ + logDeriv riemannZeta₁ s := by
    have hE : riemannZeta =ᶠ[nhds s] fun t : ℂ => (t - 1)⁻¹ * riemannZeta₁ t := by
      filter_upwards [isOpen_ne.mem_nhds hs1] with t ht
      exact riemannZeta_eq_inv_sub_mul ht
    rw [Filter.EventuallyEq.eq_of_nhds (logDeriv_congr_nhds hE)]
    erw [logDeriv_mul (f := fun t : ℂ => (t - 1)⁻¹) (g := riemannZeta₁) s
      (inv_ne_zero hne) hζ
      (((differentiableAt_id (𝕜 := ℂ) (x := s)).sub_const 1).inv hne)
      differentiable_riemannZeta₁.differentiableAt]
    have hld : logDeriv (fun t : ℂ => (t - 1)⁻¹) s = -(s - 1)⁻¹ := by
      have h := logDeriv_comp (f := fun z : ℂ => z⁻¹) (g := fun t : ℂ => t - 1) (x := s)
        (differentiableAt_inv hne) (by fun_prop)
      simp only [Function.comp_def] at h
      rw [h]
      have hd : deriv (fun t : ℂ => t - 1) s = 1 := by simp
      rw [hd, mul_one, logDeriv_inv]
      ring_nf
    rw [hld]
  have h3 := logDeriv_Gammaℝ_add_two hs0 hG
  rw [h1, h2]
  have h4 : logDeriv Complex.Gammaℝ s = logDeriv Complex.Gammaℝ (s + 2) - s⁻¹ := by
    rw [h3]; ring
  rw [h4]
  ring

/-- `Γℝ` is analytic at every point of the open right half-plane. -/
lemma analyticAt_gammaR_of_pos_re {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ Complex.Gammaℝ w := by
  have hA : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) w := by
    refine DifferentiableOn.analyticAt (s := Set.univ)
      (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) ?_ Filter.univ_mem
    intro z _
    have hz : DifferentiableAt ℂ (fun z : ℂ => -z / 2) z := by fun_prop
    exact (hz.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableWithinAt
  have hmem : {z : ℂ | 0 < z.re} ∈ nhds (w / 2) := by
    refine IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) ?_
    show (0:ℝ) < (w / 2).re
    have h1 : (w / 2).re = w.re / 2 := by rw [Complex.div_re]; norm_num; ring_nf
    rw [h1]; linarith
  have hB : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) w := by
    refine AnalyticAt.comp (x := w) (f := fun z : ℂ => z / 2) (g := Complex.Gamma) ?_ (by fun_prop)
    refine DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re}) (f := Complex.Gamma) ?_ hmem
    intro z hz
    refine (Complex.differentiableAt_Gamma z (fun m hm => ?_)).differentiableWithinAt
    have hz' : (0 : ℝ) < z.re := hz
    rw [hm] at hz'
    simp at hz'
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  exact (hA.mul hB).congr (Filter.EventuallyEq.of_eq (funext fun z => (Complex.Gammaℝ_def z).symm))

/-- `logDeriv Γℝ` is continuous on the open right half-plane. -/
lemma continuousAt_logDeriv_gammaR_of_pos_re {w : ℂ} (hw : 0 < w.re) :
    ContinuousAt (logDeriv Complex.Gammaℝ) w := by
  have hAn := analyticAt_gammaR_of_pos_re hw
  have hne : Complex.Gammaℝ w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hw
  have h1 : ContinuousAt (deriv Complex.Gammaℝ / Complex.Gammaℝ) w :=
    hAn.deriv.continuousAt.div hAn.continuousAt hne
  simpa only [logDeriv] using h1

/-- `(log (t+3) + 1)/(1 + t^2) -> 0` as `t -> +inf`. -/
lemma tendsto_log_add_three_div_sq :
    Tendsto (fun u : ℝ => (Real.log (u + 3) + 1) / (1 + u ^ 2)) atTop (nhds 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hcomp : Tendsto (fun u : ℝ => Real.log (u + 3) / (u + 3)) atTop (nhds 0) := by
    have h := h0.comp (tendsto_atTop_add_const_right atTop (3:ℝ) tendsto_id)
    simpa [Function.comp_def] using h
  refine squeeze_zero' (g := fun u : ℝ => 8 * (Real.log (u + 3) / (u + 3))) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
    have h : 0 ≤ Real.log (u + 3) := Real.log_nonneg (by linarith)
    exact div_nonneg (by linarith) (by positivity)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
    have hL1 : 1 ≤ Real.log (u + 3) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hLnn : 0 ≤ Real.log (u + 3) := by linarith
    have h1 : (0:ℝ) < 1 + u^2 := by positivity
    have h2 : (0:ℝ) < u + 3 := by linarith
    rw [← mul_div_assoc]
    rw [div_le_div_iff₀ h1 h2]
    have hA : Real.log (u + 3) + 1 ≤ 2 * Real.log (u + 3) := by linarith
    have hB : u + 3 ≤ 4 * (1 + u^2) := by nlinarith [hu, sq_nonneg u]
    have s1 : (Real.log (u + 3) + 1) * (u + 3) ≤ (2 * Real.log (u + 3)) * (u + 3) :=
      mul_le_mul_of_nonneg_right hA (by linarith)
    have s2 : (2 * Real.log (u + 3)) * (u + 3) ≤ 2 * Real.log (u + 3) * (4 * (1 + u^2)) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    linarith [s1, s2]
  · have h := hcomp.const_mul (8:ℝ)
    simpa using h

/-- **The archimedean correction term is negligible horizontally.** For a function `g` with
`|g T| -> infty`, the integral over `[-1/2, 2]` of
`((Γℝ'/Γℝ)(s+2) - 1/s - 1/(s-1)) * tentPhi(s)` with `s = x + i g T` tends to `0`. -/
lemma correction_integral_vanishing {q : ℕ} (hq : 2 ≤ q) {g : ℝ → ℝ}
    (hg : ∀ T : ℝ, 1 ≤ T → 2 ≤ |g T|)
    (hginf : Tendsto (fun T : ℝ => |g T|) atTop atTop) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        (logDeriv Complex.Gammaℝ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2)
          - ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)⁻¹
          - (((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1)⁻¹) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
            ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I))
      atTop (nhds 0) := by
  obtain ⟨M, hMpos, hM⟩ := Commons.NumberTheory.Linnik.exists_norm_tentPhi_bound
    (L := (11/2 : ℝ)) (K := (3/10 : ℝ)) (by norm_num) (by norm_num) hq
  have hlim : Tendsto (fun u : ℝ => (Real.log (u + 3) + 1) / (1 + u ^ 2)) atTop (nhds 0) :=
    tendsto_log_add_three_div_sq
  have hlim' : Tendsto (fun T : ℝ => (Real.log (|g T| + 3) + 1) / (1 + |g T| ^ 2))
      atTop (nhds 0) := hlim.comp hginf
  have hfinal : Tendsto (fun T : ℝ =>
      (5/2) * (8 * M * ((Real.log (|g T| + 3) + 1) / (1 + |g T| ^ 2)))) atTop (nhds 0) := by
    simpa using (hlim'.const_mul (8 * M)).const_mul (5/2)
  have hpt : ∀ T : ℝ, 1 ≤ T → ∀ x : ℝ, x ∈ Set.uIoc (-1/2 : ℝ) 2 →
      ‖(logDeriv Complex.Gammaℝ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2)
          - ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)⁻¹
          - (((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1)⁻¹) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
            ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖
      ≤ 8 * Real.log (|g T| + 3) * (M / (1 + (g T)^2)) := by
    intro T hT x hx
    have hu : (2:ℝ) ≤ |g T| := hg T hT
    rw [Set.uIoc_of_le (by norm_num : (-1/2:ℝ) ≤ 2)] at hx
    have hx1 : -(1/2 : ℝ) < x := by linarith [hx.1]
    have hx2 : x ≤ 2 := hx.2
    have hL1 : 1 ≤ Real.log (|g T| + 3) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hLpos : 0 < Real.log (|g T| + 3) := by linarith
    have hre : ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I).re = x := by simp
    have him : ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I).im = g T := by simp
    have hgm : ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2)
        = (((x + 2 : ℝ) : ℂ) + Complex.I * ((g T : ℝ) : ℂ)) := by
      push_cast; ring
    have hnorm1 : ‖logDeriv Complex.Gammaℝ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2)‖
        ≤ Real.log Real.pi / 2 + (1/2) * (Real.log (2 + |g T|) + 8) := by
      rw [hgm]
      exact Commons.NumberTheory.DirichletCharacter.norm_logDeriv_Gammaℝ_le (x+2) (g T)
        (by linarith) (by linarith)
    have hnorm2 : ‖((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)⁻¹‖ ≤ (1/2 : ℝ) := by
      have hge : (2:ℝ) ≤ ‖(x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I‖ := by
        have h := Complex.abs_im_le_norm ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)
        rw [him] at h
        linarith
      rw [norm_inv]
      have := (inv_le_inv₀ (by linarith : (0:ℝ) < ‖(x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I‖)
        (by norm_num : (0:ℝ) < 2)).mpr hge
      norm_num at this ⊢
      exact this
    have hnorm3 : ‖(((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1)⁻¹‖ ≤ (1/2 : ℝ) := by
      have him' : (((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1).im = g T := by simp
      have hge : (2:ℝ) ≤ ‖((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1‖ := by
        have h := Complex.abs_im_le_norm (((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1)
        rw [him'] at h
        linarith
      rw [norm_inv]
      have := (inv_le_inv₀
        (by linarith : (0:ℝ) < ‖((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1‖)
        (by norm_num : (0:ℝ) < 2)).mpr hge
      norm_num at this ⊢
      exact this
    have hPhi : ‖Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
        ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖ ≤ M / (1 + (g T)^2) := by
      have hb := hM _ (by rw [hre]; linarith)
      have hsq : (g T)^2 ≤ ‖((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, Complex.add_im, Complex.mul_im,
          sub_zero, add_zero]
        nlinarith [sq_nonneg x]
      exact hb.trans (div_le_div_of_nonneg_left hMpos.le (by positivity) (by linarith))
    rw [norm_mul]
    have hA : ‖logDeriv Complex.Gammaℝ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2)
        - ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)⁻¹
        - (((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1)⁻¹‖
        ≤ 8 * Real.log (|g T| + 3) := by
      have hpi : Real.log Real.pi / 2 ≤ 2 := by
        have hpi' : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
        linarith [Real.pi_lt_four]
      have hlog2 : Real.log (2 + |g T|) ≤ Real.log (|g T| + 3) :=
        Real.log_le_log (by positivity) (by linarith)
      have h1 : ‖logDeriv Complex.Gammaℝ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2)‖
          ≤ 2 + (1/2) * (Real.log (|g T| + 3) + 8) := by linarith [hnorm1, hpi, hlog2]
      calc ‖logDeriv Complex.Gammaℝ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2)
            - ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)⁻¹
            - (((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1)⁻¹‖
          ≤ ‖logDeriv Complex.Gammaℝ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2)
              - ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)⁻¹‖
            + ‖(((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1)⁻¹‖ := norm_sub_le _ _
        _ ≤ (‖logDeriv Complex.Gammaℝ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2)‖
              + ‖((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)⁻¹‖) + (1/2:ℝ) := by
              linarith [norm_sub_le (logDeriv Complex.Gammaℝ
                ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2))
                (((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)⁻¹), hnorm3]
        _ ≤ ((2 + (1/2) * (Real.log (|g T| + 3) + 8)) + 1/2) + 1/2 := by linarith [h1, hnorm2]
        _ ≤ 8 * Real.log (|g T| + 3) := by linarith [hL1]
    have hmain : ‖logDeriv Complex.Gammaℝ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2)
        - ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)⁻¹
        - (((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1)⁻¹‖
        * ‖Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
            ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖
        ≤ 8 * Real.log (|g T| + 3) * (M / (1 + (g T)^2)) := by
      have h8L : (0:ℝ) ≤ 8 * Real.log (|g T| + 3) := by linarith
      have hM0 : (0:ℝ) ≤ M / (1 + (g T)^2) := div_nonneg hMpos.le (by positivity)
      have := mul_le_mul hA hPhi (norm_nonneg _) h8L
      linarith [this]
    exact hmain
  have hbnd : ∀ᶠ T in atTop,
      ‖∫ x : ℝ in (-1/2)..2,
        (logDeriv Complex.Gammaℝ ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I + 2)
          - ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)⁻¹
          - (((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I) - 1)⁻¹) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
            ((x : ℂ) + ((g T : ℝ) : ℂ) * Complex.I)‖
      ≤ (5/2) * (8 * M * ((Real.log (|g T| + 3) + 1) / (1 + |g T| ^ 2))) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (hpt T hT)
    rw [show |(2:ℝ) - (-1/2)| = 5/2 by norm_num] at h1
    have hLnn : 0 ≤ Real.log (|g T| + 3) := Real.log_nonneg (by have := hg T hT; linarith)
    have hsq : (g T)^2 = |g T|^2 := (sq_abs (g T)).symm
    have hstep : 8 * Real.log (|g T| + 3) * (M / (1 + (g T)^2)) * (5/2)
        ≤ (5/2) * (8 * M * ((Real.log (|g T| + 3) + 1) / (1 + |g T| ^ 2))) := by
      rw [hsq]
      have hD : (0:ℝ) < 1 + |g T|^2 := by positivity
      rw [show 8 * Real.log (|g T| + 3) * (M / (1 + |g T|^2))
          = 8 * M * Real.log (|g T| + 3) / (1 + |g T|^2) by field_simp]
      rw [show (5/2) * (8 * M * ((Real.log (|g T| + 3) + 1) / (1 + |g T|^2)))
          = (5/2) * (8 * M * (Real.log (|g T| + 3) + 1) / (1 + |g T|^2)) by ring]
      have h2 : 8 * M * Real.log (|g T| + 3) ≤ 8 * M * (Real.log (|g T| + 3) + 1) := by
        have h3 : Real.log (|g T| + 3) ≤ Real.log (|g T| + 3) + 1 := by linarith
        linarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 8 * M)]
      have h4 : 8 * M * Real.log (|g T| + 3) / (1 + |g T|^2)
          ≤ 8 * M * (Real.log (|g T| + 3) + 1) / (1 + |g T|^2) :=
        div_le_div_of_nonneg_right h2 (le_of_lt hD)
      linarith [h4]
    linarith [h1, hstep]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _)) hbnd hfinal)

/-- Decomposition of the `Λ`-side integrand into the `ζ₁`-side integrand plus the
archimedean correction, for `s = x + i v` with `|v| ≥ 2`. -/
lemma integral_decomp {q : ℕ} {v : ℝ} (hv : 2 ≤ |v|)
    (hζ : ∀ x : ℝ, riemannZeta₁ ((x : ℂ) + (v : ℂ) * Complex.I) ≠ 0) :
    (∫ x : ℝ in (-1/2)..2, logDeriv completedRiemannZeta ((x : ℂ) + (v : ℂ) * Complex.I) *
        Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q ((x : ℂ) + (v : ℂ) * Complex.I))
      = (∫ x : ℝ in (-1/2)..2, logDeriv riemannZeta₁ ((x : ℂ) + (v : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q ((x : ℂ) + (v : ℂ) * Complex.I))
        + ∫ x : ℝ in (-1/2)..2,
            (logDeriv Complex.Gammaℝ ((x : ℂ) + (v : ℂ) * Complex.I + 2)
              - ((x : ℂ) + (v : ℂ) * Complex.I)⁻¹
              - (((x : ℂ) + (v : ℂ) * Complex.I) - 1)⁻¹) *
              Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
                ((x : ℂ) + (v : ℂ) * Complex.I) := by
  set Φ : ℂ → ℂ := Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q with hΦdef
  have hPhid : Differentiable ℂ Φ := Commons.NumberTheory.Linnik.tentPhi_diff (11/2) (3/10) q
  have hvne : v ≠ 0 := by intro h; rw [h] at hv; norm_num at hv
  have him : ∀ x : ℝ, ((x : ℂ) + (v : ℂ) * Complex.I).im = v := by intro x; simp
  have hGam : ∀ x : ℝ, Complex.Gammaℝ ((x : ℂ) + (v : ℂ) * Complex.I) ≠ 0 := by
    intro x h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have h2 := congrArg Complex.im hn
    rw [him x] at h2
    simp at h2
    exact hvne h2
  have hs0 : ∀ x : ℝ, (x : ℂ) + (v : ℂ) * Complex.I ≠ 0 := by
    intro x h
    have h2 := congrArg Complex.im h
    rw [him x] at h2
    simp at h2
    exact hvne h2
  have hs1 : ∀ x : ℝ, (x : ℂ) + (v : ℂ) * Complex.I ≠ 1 := by
    intro x h
    have h2 := congrArg Complex.im h
    rw [him x] at h2
    simp at h2
    exact hvne h2
  have hpt : Set.EqOn
      (fun x : ℝ => logDeriv completedRiemannZeta ((x : ℂ) + (v : ℂ) * Complex.I) *
        Φ ((x : ℂ) + (v : ℂ) * Complex.I))
      (fun x : ℝ => logDeriv riemannZeta₁ ((x : ℂ) + (v : ℂ) * Complex.I) *
          Φ ((x : ℂ) + (v : ℂ) * Complex.I)
        + (logDeriv Complex.Gammaℝ ((x : ℂ) + (v : ℂ) * Complex.I + 2)
            - ((x : ℂ) + (v : ℂ) * Complex.I)⁻¹
            - (((x : ℂ) + (v : ℂ) * Complex.I) - 1)⁻¹) *
            Φ ((x : ℂ) + (v : ℂ) * Complex.I))
      (Set.uIcc (-1/2) 2) := by
    intro x hx
    simp only []
    rw [Set.uIcc_of_le (by norm_num : (-1/2:ℝ) ≤ 2)] at hx
    have hre : ((x : ℂ) + (v : ℂ) * Complex.I).re = x := by simp
    have hsre : -(1:ℝ) < ((x : ℂ) + (v : ℂ) * Complex.I).re := by rw [hre]; linarith [hx.1]
    rw [logDeriv_completedRiemannZeta_eq_shift (hs0 x) (hs1 x) hsre (hGam x) (hζ x)]
    ring
  have hcont1 : ContinuousOn (fun x : ℝ =>
      logDeriv riemannZeta₁ ((x : ℂ) + (v : ℂ) * Complex.I) * Φ ((x : ℂ) + (v : ℂ) * Complex.I))
      (Set.uIcc (-1/2) 2) := by
    intro x _
    have h1 : ContinuousAt (logDeriv riemannZeta₁) ((x : ℂ) + (v : ℂ) * Complex.I) :=
      continuousAt_logDeriv_riemannZeta₁ (hζ x)
    have h2 : ContinuousAt (fun y : ℝ => (y : ℂ) + (v : ℂ) * Complex.I) x := by fun_prop
    have h3 : ContinuousAt (fun y : ℝ => logDeriv riemannZeta₁ ((y : ℂ) + (v : ℂ) * Complex.I)) x :=
      ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + (v : ℂ) * Complex.I) h1 h2
    have h4 : ContinuousAt (fun y : ℝ => Φ ((y : ℂ) + (v : ℂ) * Complex.I)) x :=
      ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + (v : ℂ) * Complex.I)
        hPhid.continuous.continuousAt h2
    exact (h3.mul h4).continuousWithinAt
  have hcont2 : ContinuousOn (fun x : ℝ =>
      (logDeriv Complex.Gammaℝ ((x : ℂ) + (v : ℂ) * Complex.I + 2)
        - ((x : ℂ) + (v : ℂ) * Complex.I)⁻¹
        - (((x : ℂ) + (v : ℂ) * Complex.I) - 1)⁻¹) * Φ ((x : ℂ) + (v : ℂ) * Complex.I))
      (Set.uIcc (-1/2) 2) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1/2:ℝ) ≤ 2)] at hx
    have h2 : ContinuousAt (fun y : ℝ => (y : ℂ) + (v : ℂ) * Complex.I) x := by fun_prop
    have hre : ((x : ℂ) + (v : ℂ) * Complex.I + 2).re = x + 2 := by simp
    have h3 : ContinuousAt (fun y : ℝ => logDeriv Complex.Gammaℝ ((y : ℂ) + (v : ℂ) * Complex.I + 2)) x :=
      ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + (v : ℂ) * Complex.I + 2)
        (continuousAt_logDeriv_gammaR_of_pos_re (by rw [hre]; linarith [hx.1])) (by fun_prop)
    have h4 : ContinuousAt (fun y : ℝ => ((y : ℂ) + (v : ℂ) * Complex.I)⁻¹) x :=
      h2.inv₀ (hs0 x)
    have h5 : ContinuousAt (fun y : ℝ => (((y : ℂ) + (v : ℂ) * Complex.I) - 1)⁻¹) x :=
      (h2.sub_const 1).inv₀ (sub_ne_zero.mpr (hs1 x))
    have h6 : ContinuousAt (fun y : ℝ => Φ ((y : ℂ) + (v : ℂ) * Complex.I)) x :=
      ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + (v : ℂ) * Complex.I)
        hPhid.continuous.continuousAt h2
    exact (((h3.sub h4).sub h5).mul h6).continuousWithinAt
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_add hcont1.intervalIntegrable hcont2.intervalIntegrable]

theorem horizontal_vanishing_completedRiemannZeta {q : ℕ} (hq : 2 ≤ q) {c : ℝ} (hc : 0 < c)
    {T' : ℝ → ℝ} (hT' : ∀ T : ℝ, 1 ≤ T → T + 1 ≤ T' T)
    (hsep : ∀ T : ℝ, 1 ≤ T → ∀ ρ : ℂ, riemannZeta₁ ρ = 0 →
      c / Real.log (T' T + 3) ≤ |ρ.im - T' T| ∧ c / Real.log (T' T + 3) ≤ |ρ.im + T' T|)
    (hVan1 : Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        logDeriv riemannZeta₁ ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
            ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)) Filter.atTop (nhds 0))
    (hVan2 : Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        logDeriv riemannZeta₁ ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
            ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)) Filter.atTop (nhds 0)) :
    (Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        logDeriv completedRiemannZeta ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
            ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)) Filter.atTop (nhds 0)) ∧
    (Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        logDeriv completedRiemannZeta ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
            ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)) Filter.atTop (nhds 0)) := by
  have hT'2 : ∀ T : ℝ, 1 ≤ T → 2 ≤ |T' T| := by
    intro T hT
    rw [abs_of_nonneg (by have := hT' T hT; linarith)]
    have := hT' T hT
    linarith
  have hT'inf : Tendsto (fun T : ℝ => |T' T|) atTop atTop := by
    have h1 : Tendsto (fun T : ℝ => T + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_id
    refine tendsto_atTop_mono' atTop ?_ h1
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    rw [abs_of_nonneg (by have := hT' T hT; linarith)]
    exact hT' T hT
  have hposlog : ∀ T : ℝ, 1 ≤ T → (0:ℝ) < c / Real.log (T' T + 3) := by
    intro T hT
    refine div_pos hc (Real.log_pos ?_)
    have := hT' T hT
    linarith
  have hzetaP : ∀ T : ℝ, 1 ≤ T → ∀ x : ℝ,
      riemannZeta₁ ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro T hT x h
    have h1 := (hsep T hT ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) h).1
    have him : ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I).im = T' T := by simp
    rw [him, sub_self, abs_zero] at h1
    linarith [hposlog T hT]
  have hzetaM : ∀ T : ℝ, 1 ≤ T → ∀ x : ℝ,
      riemannZeta₁ ((x : ℂ) + (((-(T' T) : ℝ)) : ℂ) * Complex.I) ≠ 0 := by
    intro T hT x h
    have h2 := (hsep T hT ((x : ℂ) + (((-(T' T) : ℝ)) : ℂ) * Complex.I) h).2
    have him : ((x : ℂ) + (((-(T' T) : ℝ)) : ℂ) * Complex.I).im = -(T' T) := by simp
    rw [him] at h2
    have hzero : -(T' T) + T' T = (0:ℝ) := by ring
    rw [hzero, abs_zero] at h2
    linarith [hposlog T hT]
  have hkeyP : ∀ T : ℝ, 1 ≤ T →
      (∫ x : ℝ in (-1/2)..2, logDeriv completedRiemannZeta ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in (-1/2)..2, logDeriv riemannZeta₁ ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) *
            Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I))
        + ∫ x : ℝ in (-1/2)..2,
            (logDeriv Complex.Gammaℝ ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I + 2)
              - ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)⁻¹
              - (((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) - 1)⁻¹) *
              Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
                ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) :=
    fun T hT => integral_decomp (hT'2 T hT) (hzetaP T hT)
  have hkeyM : ∀ T : ℝ, 1 ≤ T →
      (∫ x : ℝ in (-1/2)..2, logDeriv completedRiemannZeta ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in (-1/2)..2, logDeriv riemannZeta₁ ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) *
            Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I))
        + ∫ x : ℝ in (-1/2)..2,
            (logDeriv Complex.Gammaℝ ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I + 2)
              - ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)⁻¹
              - (((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) - 1)⁻¹) *
              Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
                ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) := by
    intro T hT
    have hv : (2:ℝ) ≤ |-(T' T)| := by rw [abs_neg]; exact hT'2 T hT
    have h := integral_decomp (q := q) (v := -(T' T)) hv (hzetaM T hT)
    simpa [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using h
  constructor
  · have hsum : Tendsto (fun T : ℝ =>
        (∫ x : ℝ in (-1/2)..2, logDeriv riemannZeta₁ ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) *
              Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
                ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I))
        + ∫ x : ℝ in (-1/2)..2,
            (logDeriv Complex.Gammaℝ ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I + 2)
              - ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)⁻¹
              - (((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) - 1)⁻¹) *
              Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
                ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)) atTop (nhds 0) := by
      simpa using hVan1.add (correction_integral_vanishing hq hT'2 hT'inf)
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    exact (hkeyP T hT).symm
  · have hcorr : Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        (logDeriv Complex.Gammaℝ ((x : ℂ) + (((-(T' T) : ℝ)) : ℂ) * Complex.I + 2)
          - ((x : ℂ) + (((-(T' T) : ℝ)) : ℂ) * Complex.I)⁻¹
          - (((x : ℂ) + (((-(T' T) : ℝ)) : ℂ) * Complex.I) - 1)⁻¹) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
            ((x : ℂ) + (((-(T' T) : ℝ)) : ℂ) * Complex.I)) atTop (nhds 0) :=
      correction_integral_vanishing (q := q) hq (g := fun T => -(T' T))
        (fun T hT => by rw [abs_neg]; exact hT'2 T hT) (by simpa using hT'inf)
    have hcorr' : Tendsto (fun T : ℝ => ∫ x : ℝ in (-1/2)..2,
        (logDeriv Complex.Gammaℝ ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I + 2)
          - ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)⁻¹
          - (((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) - 1)⁻¹) *
          Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
            ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)) atTop (nhds 0) := by
      refine hcorr.congr' ?_
      filter_upwards with T
      apply intervalIntegral.integral_congr
      intro x _
      simp [Complex.ofReal_neg, neg_mul, sub_eq_add_neg]
    have hsum : Tendsto (fun T : ℝ =>
        (∫ x : ℝ in (-1/2)..2, logDeriv riemannZeta₁ ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) *
              Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
                ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I))
        + ∫ x : ℝ in (-1/2)..2,
            (logDeriv Complex.Gammaℝ ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I + 2)
              - ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)⁻¹
              - (((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) - 1)⁻¹) *
              Commons.NumberTheory.Linnik.tentPhi (11/2) (3/10) q
                ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)) atTop (nhds 0) := by
      simpa using hVan2.add hcorr'
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    exact (hkeyM T hT).symm

end
end Work.LinnikAreas
