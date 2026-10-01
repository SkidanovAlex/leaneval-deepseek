import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Submission.Commons.Analysis.Complex.gamma_integral_cpow
import Submission.Commons.Analysis.Complex.laplace_inversion_smooth
import Submission.Commons.Analysis.Complex.integrable_laplace_vertical

/-!
# The Perron/cpow kernel integral

We prove the Laplace ("Bromwich") inversion of the power `s ^ (-α)` for a smooth,
compactly supported function `f`:

`(1/2π) ∫_τ (c + iτ)^{-α} (∫_t e^{(c+iτ)t} f t) dτ = (1/Γ(α)) ∫_0^∞ t^{α-1} f t`,

and use it to evaluate the `cpow`-kernel integral appearing in the
Friedlander–Iwaniec proof.
-/

namespace Commons.Analysis.Perron

open MeasureTheory Real
open Commons.Analysis.Complex
open scoped Topology

noncomputable section

theorem integrable_rpow_mul_exp_neg_ite (α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Integrable (fun v : ℝ => if 0 < v then v ^ (α - 1) * Real.exp (-(c * v)) else 0) := by
  have hbase : IntegrableOn (fun v : ℝ => v ^ (α - 1) * Real.exp (-(c * v))) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := α - 1) (b := c)
      (by linarith) (by norm_num) hc
    refine h.congr_fun ?_ measurableSet_Ioi
    intro v hv
    simp only [Set.mem_Ioi] at hv
    simp only [Real.rpow_one]
    congr 1
    ring
  have h2 : Integrable ((Set.Ioi (0:ℝ)).indicator
      (fun v : ℝ => v ^ (α - 1) * Real.exp (-(c * v)))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hbase
  refine h2.congr ?_
  filter_upwards with v
  by_cases hv : 0 < v
  · rw [Set.indicator_of_mem (by exact hv)]
    simp only [if_pos hv]
  · rw [Set.indicator_of_notMem (by simpa using hv)]
    simp only [if_neg hv]

theorem continuous_laplaceVertical (c : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hcpt : HasCompactSupport f) :
    Continuous (fun τ : ℝ => ∫ t : ℝ, Complex.exp (((c:ℂ)+τ*Complex.I)*(t:ℂ)) * f t) := by
  have hfc : Continuous f := hf.continuous
  have hK : IsCompact (tsupport f) := hcpt.isCompact
  have hzero : ∀ t ∉ tsupport f, f t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport ht
  have heq : (fun τ : ℝ => ∫ t : ℝ, Complex.exp (((c:ℂ)+τ*Complex.I)*(t:ℂ)) * f t)
      = fun τ : ℝ => ∫ t in tsupport f, Complex.exp (((c:ℂ)+τ*Complex.I)*(t:ℂ)) * f t := by
    funext τ
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => by rw [hzero t ht, mul_zero])).symm
  rw [heq]
  apply continuous_parametric_integral_of_continuous
  · fun_prop
  · exact hK

set_option maxHeartbeats 400000 in
theorem bromwich_cpow_positive (c : ℝ) (hc : 0 < c) (α : ℝ) (hα : 0 < α) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcpt : HasCompactSupport f) :
    (1 / (2 * Real.pi)) * ∫ τ : ℝ, (((c : ℂ) + τ * Complex.I)) ^ (-(α : ℂ))
        * (∫ t : ℝ, Complex.exp ((((c : ℂ) + τ * Complex.I)) * (t : ℂ)) * f t)
      = (1 / Complex.Gamma (α : ℂ)) *
          ∫ t : ℝ in Set.Ioi 0, ((t : ℂ)) ^ ((α : ℂ) - 1) * f t := by
  have hGcont : Continuous (fun τ : ℝ =>
      ∫ t : ℝ, Complex.exp ((((c : ℂ) + τ * Complex.I)) * (t : ℂ)) * f t) :=
    continuous_laplaceVertical c hf hcpt
  set G : ℝ → ℂ := fun τ => ∫ t : ℝ, Complex.exp ((((c : ℂ) + τ * Complex.I)) * (t : ℂ)) * f t with hGdef
  have hGint' : Integrable G := integrable_laplace_vertical c hf hcpt
  have hGcont' : Continuous G := hGcont
  set Φ : ℝ → ℝ → ℂ := fun τ v => if 0 < v then (v : ℂ) ^ ((α:ℂ) - 1)
        * Complex.exp (-(((c : ℂ) + τ * Complex.I) * (v : ℂ))) * G τ else 0 with hΦdef
  have hΦint : Integrable (Function.uncurry Φ) (volume.prod volume) := by
    have hB : Integrable (fun v : ℝ => if 0 < v then v ^ (α - 1) * Real.exp (-(c * v)) else 0) :=
      integrable_rpow_mul_exp_neg_ite α c hα hc
    have hgn : Integrable (fun τ => ‖G τ‖) := hGint'.norm
    have hprod : Integrable (fun p : ℝ × ℝ =>
        ‖G p.1‖ * (if 0 < p.2 then p.2 ^ (α - 1) * Real.exp (-(c * p.2)) else 0))
        (volume.prod volume) := hgn.mul_prod hB
    refine Integrable.mono' hprod ?_ ?_
    · apply Measurable.aestronglyMeasurable
      apply Measurable.ite
      · exact measurableSet_lt measurable_const measurable_snd
      · have h1 : Measurable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ ((α:ℂ) - 1)) := by fun_prop
        have h2 : Measurable (fun p : ℝ × ℝ =>
            Complex.exp (-(((c : ℂ) + p.1 * Complex.I) * (p.2 : ℂ)))) := by
          apply Complex.measurable_exp.comp
          fun_prop
        have h3 : Measurable (fun p : ℝ × ℝ => G p.1) := hGcont'.measurable.comp measurable_fst
        exact (h1.mul h2).mul h3
      · exact measurable_const
    · filter_upwards with p
      rw [show Function.uncurry Φ p = Φ p.1 p.2 from rfl]
      simp only [hΦdef]
      rcases lt_or_ge (0:ℝ) p.2 with hv | hv
      · rw [if_pos hv, if_pos hv]
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_exp]
        have hre : (-(((c : ℂ) + p.1 * Complex.I) * (p.2 : ℂ))).re = -(c * p.2) := by
          simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.add_im,
            Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
            sub_zero]
          ring
        rw [hre]
        have hre2 : (((α:ℂ) - 1)).re = α - 1 := by simp
        rw [hre2]
        rw [mul_comm (‖G p.1‖)]
      · rw [if_neg (not_lt.mpr hv), if_neg (not_lt.mpr hv), norm_zero, mul_zero]
  have hΓne : Complex.Gamma (α:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hα)
  have hΓ : ∀ τ : ℝ, (((c : ℂ) + τ * Complex.I)) ^ (-(α : ℂ))
      = (1 / Complex.Gamma (α : ℂ)) *
        ∫ v : ℝ in Set.Ioi 0, (v : ℂ) ^ ((α:ℂ) - 1)
          * Complex.exp (-(((c : ℂ) + τ * Complex.I) * (v : ℂ))) := by
    intro τ
    have hz : 0 < (((c : ℂ) + τ * Complex.I)).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_one, mul_zero, sub_zero, zero_mul, add_zero]
      exact hc
    have hg := gamma_integral_cpow (a := (α:ℂ)) (z := (((c : ℂ) + τ * Complex.I)))
      (by simpa using hα) hz
    rw [hg, one_div, ← mul_assoc, inv_mul_cancel₀ hΓne, one_mul]
  have hK : ∀ τ : ℝ, (((c : ℂ) + τ * Complex.I)) ^ (-(α : ℂ)) * G τ
      = (1 / Complex.Gamma (α : ℂ)) * ∫ v : ℝ, Φ τ v := by
    intro τ
    rw [hΓ τ, mul_assoc]
    congr 1
    rw [← integral_indicator measurableSet_Ioi]
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with v
    simp only [hΦdef]
    by_cases hv : 0 < v
    · rw [if_pos hv, Set.indicator_of_mem (by exact hv)]
    · rw [if_neg hv, Set.indicator_of_notMem (by simpa using hv), zero_mul]
  -- inversion identity
  have h2pi : (2 * (Real.pi:ℂ)) ≠ 0 := by
    have h : (2:ℂ) * (Real.pi:ℂ) ≠ 0 := by
      apply mul_ne_zero; norm_num
      exact_mod_cast Real.pi_ne_zero
    simpa using h
  have hinv : ∀ v : ℝ, (∫ τ : ℝ,
      Complex.exp (-(((c : ℂ) + τ * Complex.I) * (v : ℂ))) * G τ) = 2 * Real.pi * f v := by
    intro v
    have hc0 : (-c) ≠ 0 := by linarith
    have hbase := laplace_inversion_smooth hf hcpt (-c) v hc0
    set F : ℝ → ℂ := fun γ => (∫ t : ℝ,
        Complex.exp (-((((-c : ℝ):ℂ) + γ * Complex.I) * (t : ℂ))) * f t)
        * Complex.exp ((((-c : ℝ):ℂ) + γ * Complex.I) * (v : ℂ)) with hFdef
    have hFpt : ∀ τ : ℝ, F (-τ) = G τ * Complex.exp (-(((c : ℂ) + τ * Complex.I) * (v : ℂ))) := by
      intro τ
      simp only [hFdef, hGdef]
      congr 1
      · apply integral_congr_ae
        filter_upwards with t
        congr 1
        push_cast
        ring
      · congr 1
        push_cast
        ring
    have hneg : (∫ γ : ℝ, F γ) = ∫ τ : ℝ, F (-τ) := (integral_neg_eq_self F volume).symm
    rw [hneg, show (∫ τ : ℝ, F (-τ))
        = ∫ τ : ℝ, G τ * Complex.exp (-(((c : ℂ) + τ * Complex.I) * (v : ℂ))) from
          integral_congr_ae (Filter.Eventually.of_forall hFpt)] at hbase
    have hkey : (2 * (Real.pi:ℂ)) * f v
        = ∫ τ : ℝ, G τ * Complex.exp (-(((c : ℂ) + τ * Complex.I) * (v : ℂ))) := by
      rw [hbase, ← mul_assoc, mul_one_div_cancel h2pi, one_mul]
    have hcomm : (∫ τ : ℝ, G τ * Complex.exp (-(((c : ℂ) + τ * Complex.I) * (v : ℂ))))
        = ∫ τ : ℝ, Complex.exp (-(((c : ℂ) + τ * Complex.I) * (v : ℂ))) * G τ := by
      apply integral_congr_ae; filter_upwards with τ; ring
    rw [hcomm] at hkey
    rw [hkey]
  -- assemble
  rw [show (∫ τ : ℝ, (((c : ℂ) + τ * Complex.I)) ^ (-(α : ℂ)) * G τ)
      = ∫ τ : ℝ, (1 / Complex.Gamma (α : ℂ)) * ∫ v : ℝ, Φ τ v from
        integral_congr_ae (Filter.Eventually.of_forall hK)]
  rw [integral_const_mul]
  rw [integral_integral_swap hΦint]
  have hHvan : ∀ v ∉ Set.Ioi (0:ℝ), (∫ τ : ℝ, Φ τ v) = 0 := by
    intro v hv
    have hv' : ¬ (0 < v) := by simpa using hv
    rw [show (∫ τ : ℝ, Φ τ v) = ∫ _τ : ℝ, (0:ℂ) from
      integral_congr_ae (Filter.Eventually.of_forall (fun τ => by
        simp only [hΦdef, if_neg hv']))]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hHvan]
  have hinner : ∀ v ∈ Set.Ioi (0:ℝ), (∫ τ : ℝ, Φ τ v)
      = (v : ℂ) ^ ((α:ℂ) - 1) * (2 * Real.pi * f v) := by
    intro v hv
    have hv' : 0 < v := hv
    have hΦv : (∫ τ : ℝ, Φ τ v) = ∫ τ : ℝ, ((v : ℂ) ^ ((α:ℂ) - 1)
        * Complex.exp (-(((c : ℂ) + τ * Complex.I) * (v : ℂ)))) * G τ := by
      apply integral_congr_ae
      filter_upwards with τ
      simp only [hΦdef, if_pos hv']
    rw [hΦv]
    rw [show (fun τ : ℝ => (v : ℂ) ^ ((α:ℂ) - 1)
          * Complex.exp (-(((c : ℂ) + τ * Complex.I) * (v : ℂ))) * G τ)
        = (fun τ : ℝ => (v : ℂ) ^ ((α:ℂ) - 1)
          * (Complex.exp (-(((c : ℂ) + τ * Complex.I) * (v : ℂ))) * G τ)) from
          funext (fun τ => by ring)]
    rw [integral_const_mul]
    congr 1
    exact hinv v
  rw [setIntegral_congr_fun measurableSet_Ioi hinner]
  rw [show (∫ v in Set.Ioi (0:ℝ), (v : ℂ) ^ ((α:ℂ) - 1) * (2 * Real.pi * f v))
      = 2 * Real.pi * ∫ v in Set.Ioi (0:ℝ), (v : ℂ) ^ ((α:ℂ) - 1) * f v from by
        rw [← integral_const_mul]; apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv; ring]
  field_simp



/-- **The `cpow` kernel integral.**  For `0 < γ'`, `0 < α` and a smooth compactly
supported `ψ`, the Bromwich-type integral of the kernel `s ^ (-α) e^{sZ}` against the
two-sided Laplace transform of `ψ` equals the one-sided `Γ`-integral of `ψ (· - Z)`. -/
theorem integral_cpow_kernel (γ' : ℝ) (hγ' : 0 < γ') (α : ℝ) (hα : 0 < α)
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (Z : ℝ) :
    (1 / (2 * Real.pi)) * ∫ τ : ℝ, (((γ' : ℂ) + τ * Complex.I)) ^ (-(α : ℂ))
        * Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (Z : ℂ))
        * (∫ u : ℝ, Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (u : ℂ)) * ψ u)
      = (1 / Complex.Gamma (α : ℂ)) *
          ∫ u : ℝ in Set.Ioi 0, ((u : ℂ)) ^ ((α : ℂ) - 1) * ψ (u - Z) := by
  -- `ψ (· - Z)` is again smooth with compact support
  have hf_sub : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ψ (t - Z)) :=
    hψ.comp (contDiff_id.sub contDiff_const)
  have hcpt_sub : HasCompactSupport (fun t : ℝ => ψ (t - Z)) := by
    have h := hψc.comp_homeomorph (Homeomorph.subRight Z)
    simpa [Function.comp_def] using h
  -- the shift `e^{sZ} ∫ e^{su} ψ u = ∫ e^{st} ψ (t - Z)`
  have hshift : ∀ τ : ℝ,
      Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (Z : ℂ))
        * (∫ u : ℝ, Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (u : ℂ)) * ψ u)
      = ∫ t : ℝ, Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (t : ℂ)) * ψ (t - Z) := by
    intro τ
    rw [← integral_const_mul]
    have hpt : (fun u : ℝ => Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (Z : ℂ))
          * (Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (u : ℂ)) * ψ u))
        = (fun u : ℝ => (fun t : ℝ => Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (t : ℂ))
            * ψ (t - Z)) (u + Z)) := by
      funext u
      simp only
      have h1 : Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (Z : ℂ))
            * Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (u : ℂ))
          = Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * ((u + Z : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      have h2 : (u + Z) - Z = u := by ring
      calc Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (Z : ℂ))
            * (Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (u : ℂ)) * ψ u)
          = (Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (Z : ℂ))
              * Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (u : ℂ))) * ψ u := by ring
        _ = Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * ((u + Z : ℝ) : ℂ)) * ψ u := by rw [h1]
        _ = Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * ((u + Z : ℝ) : ℂ))
              * ψ ((u + Z) - Z) := by rw [h2]
    rw [hpt]
    exact integral_add_right_eq_self
      (fun t : ℝ => Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (t : ℂ)) * ψ (t - Z)) Z
  -- reduce the target's left-hand side to the general Bromwich form
  have hcongr : (∫ τ : ℝ, (((γ' : ℂ) + τ * Complex.I)) ^ (-(α : ℂ))
        * Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (Z : ℂ))
        * (∫ u : ℝ, Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (u : ℂ)) * ψ u))
      = ∫ τ : ℝ, (((γ' : ℂ) + τ * Complex.I)) ^ (-(α : ℂ))
        * (∫ t : ℝ, Complex.exp ((((γ' : ℂ) + τ * Complex.I)) * (t : ℂ))
            * (fun t : ℝ => ψ (t - Z)) t) := by
    apply integral_congr_ae
    filter_upwards with τ
    rw [mul_assoc, hshift τ]
  rw [hcongr]
  exact bromwich_cpow_positive γ' hγ' α hα hf_sub hcpt_sub

end

end Commons.Analysis.Perron