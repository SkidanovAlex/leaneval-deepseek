import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_one_sub
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_norm_le_re_ge_three_halves
import Submission.Commons.NumberTheory.DirichletCharacter.leftEdge_logDeriv_bound
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale
import Submission.Commons.Analysis.Complex.laplace_transform_bound_complex
import Submission.Commons.Analysis.Fourier.vertical_laplace_eq_zero
import Submission.Commons.Analysis.Integral.integral_log_lorentz_le
import Submission.Commons.Analysis.Integral.integrable_log_lorentz
import Submission.Commons.Analysis.Integral.integrable_inv_sq_add
import Submission.Commons.Topology.ContinuousOn.indicator_Ioo_continuous
import Submission.Commons.NumberTheory.DirichletCharacter.norm_logDeriv_LFunction_leftEdge_add_logN_le

open MeasureTheory intervalIntegral
open scoped Real Topology

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Norm bound for the vertical integral of `L'/L` against a Laplace transform

For a primitive non-trivial Dirichlet character `χ` and a compactly supported `C²` weight `f`
(with `f 0 = 0`), the integral over `t ∈ ℝ` of `(L'/L)(χ, -1/2 + it)` against the Laplace
transform `∫₀^{x₀} exp(-(s - (-1/2 + it)) L u) f u du` is estimated by

`(3 B x₀ / L²) * 2000 * (log (2 + ‖s‖) + 1)`.

The proof has four ingredients:
* the Laplace-transform bound `laplace_transform_bound_complex` applied to the inner integral;
* the vanishing `∫_t Φ(-1/2 + it) dt = 0` (`vertical_laplace_eq_zero`), which allows the
  `-log N` term in the functional equation to be discarded: indeed
  `logDeriv L(χ)(s) = -log N - logDeriv L(χ⁻¹)(1-s) - …`, and the constant `-log N` is
  annihilated by the vanishing integral;
* the pointwise bound `‖logDeriv L(χ)(-1/2+it) + log N‖ ≤ 100 (log (2 + |t|) + 1)`
  (`norm_logDeriv_LFunction_leftEdge_add_logN_le`);
* the Lorentz-type integral estimate `integral_log_lorentz_le`.
-/

theorem norm_integral_logDeriv_L_lefthalf_le {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {L : ℝ} (hL : 1 < L) {s : ℂ} (hs : 1 < s.re) :
    ‖∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
          (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I) *
        (∫ u : ℝ in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) * (L:ℂ)) * (u:ℂ))) * f u)‖
      ≤ (3 * B * x₀ / L ^ 2) * 2000 * (Real.log (2 + ‖s‖) + 1) := by
  have hL0 : (0:ℝ) < L := by linarith
  set a : ℝ := s.re + 1/2 with hadef
  set b : ℝ := s.im with hbdef
  have ha : (3:ℝ)/2 < a := by rw [hadef]; linarith
  have ha0 : 0 < a := by linarith
  have hCnn : (0:ℝ) ≤ 3 * B * x₀ / L ^ 2 := by positivity
  set K : ℝ → ℂ := fun t => (∫ u : ℝ in (0:ℝ)..x₀,
      Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) * (L:ℂ)) * (u:ℂ))) * f u) with hKdef
  set R : ℝ → ℂ := fun t => logDeriv (DirichletCharacter.LFunction χ)
      (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I) + ((Real.log (N:ℝ)) : ℂ) with hRdef
  -- re / im of s - (-1/2 + it)
  have hre : ∀ t : ℝ, (s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)).re = a := by
    intro t
    simp only [hadef, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    ring
  have him : ∀ t : ℝ, (s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)).im = s.im - t := by
    intro t
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
  -- pointwise Laplace bound
  have hKbound : ∀ t : ℝ, ‖K t‖ ≤ (3 * B * x₀ / L ^ 2) * (a ^ 2 + (t - b) ^ 2)⁻¹ := by
    intro t
    have hzre : 0 < (((s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) * (L:ℂ))).re := by
      rw [Complex.mul_re, Complex.ofReal_im, hre t, mul_zero, sub_zero]
      rw [Complex.ofReal_re]
      exact mul_pos ha0 hL0
    have h := Commons.Analysis.Complex.laplace_transform_bound_complex
      (z := ((s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) * (L:ℂ)))
      hx₀ hB hcont hf2 hBnd hvan hf0 hzre
    have hKt : K t = ∫ u : ℝ in (0:ℝ)..x₀,
        Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) * (L:ℂ)) * (u:ℂ))) * f u := by
      rw [hKdef]
    rw [hKt]
    have hLnorm : ‖(((L:ℝ)):ℂ)‖ = L := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
    have hzn : ‖((s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) * (L:ℂ))‖ ^ 2
        = L^2 * (a^2 + (t - b)^2) := by
      rw [norm_mul, hLnorm, mul_pow, Complex.sq_norm, Complex.normSq_apply, hre t, him t, hbdef]
      ring
    rw [hzn] at h
    have hval : 3 * B * x₀ / (L ^ 2 * (a ^ 2 + (t - b) ^ 2))
        = (3 * B * x₀ / L ^ 2) * (a ^ 2 + (t - b) ^ 2)⁻¹ := by
      rw [div_mul_eq_div_div, div_eq_mul_inv]
    rw [hval] at h
    exact h
  -- continuity of K
  have hKcont : Continuous K := by
    rw [hKdef]
    have hGcont : Continuous (fun v : ℝ => if v ∈ Set.Ioo (0:ℝ) x₀ then f v else 0) :=
      Commons.Topology.ContinuousOn.indicator_Ioo_continuous hx₀ hcont hvan hf0
    have hexp : Continuous (fun p : ℝ × ℝ =>
        Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (p.1:ℂ) * Complex.I)) * (L:ℂ)) * (p.2:ℂ)))) := by
      apply Complex.continuous_exp.comp
      fun_prop
    have hjoint : Continuous (Function.uncurry (fun (t : ℝ) (v : ℝ) =>
        Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) * (L:ℂ)) * (v:ℂ))) *
          (if v ∈ Set.Ioo (0:ℝ) x₀ then f v else 0))) :=
      hexp.mul (hGcont.comp continuous_snd)
    have hcontpar := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) hjoint 0 x₀
    have heq : (fun t : ℝ => ∫ v : ℝ in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) * (L:ℂ)) * (v:ℂ))) *
            (if v ∈ Set.Ioo (0:ℝ) x₀ then f v else 0))
        = (fun t : ℝ => ∫ v : ℝ in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) * (L:ℂ)) * (v:ℂ))) * f v) := by
      funext t
      apply intervalIntegral.integral_congr_ae
      filter_upwards with v hv
      have hv' : v ∈ Set.Ioc (0:ℝ) x₀ := by
        rwa [Set.uIoc_of_le (le_of_lt hx₀)] at hv
      have hgv : (if v ∈ Set.Ioo (0:ℝ) x₀ then f v else 0) = f v := by
        rcases eq_or_lt_of_le hv'.2 with h | h
        · rw [h, hvan x₀ le_rfl]; simp
        · rw [if_pos (Set.mem_Ioo.mpr ⟨hv'.1, h⟩)]
      rw [hgv]
    rw [← heq]
    exact hcontpar
  -- integrability of K
  have hKint : Integrable K := by
    refine Integrable.mono' (g := fun t : ℝ => (3 * B * x₀ / L ^ 2) * (a ^ 2 + (t - b) ^ 2)⁻¹)
      ?_ hKcont.aestronglyMeasurable ?_
    · exact (Commons.Analysis.Integral.integrable_inv_sq_add a b (ne_of_gt ha0)).const_mul (3 * B * x₀ / L ^ 2)
    · filter_upwards with t using hKbound t
  -- ∫ K = 0
  have hKzero : (∫ t : ℝ, K t) = 0 := by
    rw [hKdef]
    have hure : 0 < (s - ((-1/2:ℝ):ℂ)).re := by
      rw [Complex.sub_re, Complex.ofReal_re]
      linarith
    have h := Commons.Analysis.Fourier.vertical_laplace_eq_zero hx₀ hB hcont hf2 hBnd hvan hf0 (u := s - ((-1/2:ℝ):ℂ)) hure hL0
    have key : (∫ t : ℝ, ∫ v : ℝ in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) * (L:ℂ)) * (v:ℂ))) * f v)
        = (∫ t : ℝ, ∫ v : ℝ in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((-1/2:ℝ):ℂ)) - (t:ℂ) * Complex.I) * (L:ℂ) * (v:ℂ))) * f v) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      apply intervalIntegral.integral_congr_ae
      filter_upwards with v _
      congr 2
      ring
    rw [key]
    exact h
  -- pointwise bound on R
  have hRbound : ∀ t : ℝ, ‖R t‖ ≤ 100 * (Real.log (2 + |t|) + 1) := by
    intro t
    rw [hRdef]
    exact Commons.NumberTheory.DirichletCharacter.norm_logDeriv_LFunction_leftEdge_add_logN_le χ hχ hχprim t
  have hRcont : Continuous R := by
    rw [hRdef]
    have h1 : Continuous (fun t : ℝ => logDeriv (DirichletCharacter.LFunction χ)
        (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) :=
      Commons.NumberTheory.DirichletCharacter.continuous_logDeriv_LFunction_of_re_eq_neg_half χ hχ hχprim
    exact h1.add continuous_const
  -- integrability of R * K
  have hRKpoint : ∀ t : ℝ, ‖R t * K t‖
      ≤ 100 * (3 * B * x₀ / L ^ 2) * ((Real.log (2 + |t|) + 1) / (a ^ 2 + (t - b) ^ 2)) := by
    intro t
    rw [norm_mul]
    have hlog : (0:ℝ) ≤ 100 * (Real.log (2 + |t|) + 1) := by
      have h0 : (0:ℝ) ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
      linarith
    have h1 : ‖R t‖ * ‖K t‖ ≤ (100 * (Real.log (2 + |t|) + 1)) *
        ((3 * B * x₀ / L ^ 2) * (a ^ 2 + (t - b) ^ 2)⁻¹) :=
      mul_le_mul (hRbound t) (hKbound t) (norm_nonneg _) hlog
    calc ‖R t‖ * ‖K t‖ ≤ (100 * (Real.log (2 + |t|) + 1)) *
          ((3 * B * x₀ / L ^ 2) * (a ^ 2 + (t - b) ^ 2)⁻¹) := h1
      _ = 100 * (3 * B * x₀ / L ^ 2) * ((Real.log (2 + |t|) + 1) / (a ^ 2 + (t - b) ^ 2)) := by ring
  have hDint : Integrable (fun t : ℝ => 100 * (3 * B * x₀ / L ^ 2) *
      ((Real.log (2 + |t|) + 1) / (a ^ 2 + (t - b) ^ 2))) :=
    (Commons.Analysis.Integral.integrable_log_lorentz a b ha0).const_mul (100 * (3 * B * x₀ / L ^ 2))
  have hRKint : Integrable (fun t : ℝ => R t * K t) := by
    refine Integrable.mono' hDint (hRcont.mul hKcont).aestronglyMeasurable ?_
    filter_upwards with t using hRKpoint t
  -- split the integral
  have hsplit : (∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
        (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I) * K t)
      = ∫ t : ℝ, R t * K t := by
    have hpt : ∀ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
          (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I) * K t
        = R t * K t - ((Real.log (N:ℝ)) : ℂ) * K t := by
      intro t; rw [hRdef]; ring
    calc (∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
            (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I) * K t)
        = ∫ t : ℝ, (R t * K t - ((Real.log (N:ℝ)) : ℂ) * K t) := by
          apply MeasureTheory.integral_congr_ae; filter_upwards with t; exact hpt t
      _ = (∫ t : ℝ, R t * K t) - ∫ t : ℝ, ((Real.log (N:ℝ)) : ℂ) * K t :=
          MeasureTheory.integral_sub hRKint (hKint.const_mul ((Real.log (N:ℝ)) : ℂ))
      _ = (∫ t : ℝ, R t * K t) - ((Real.log (N:ℝ)) : ℂ) * ∫ t : ℝ, K t := by
          rw [MeasureTheory.integral_const_mul]
      _ = ∫ t : ℝ, R t * K t := by simp [hKzero]
  -- main chain
  have hmain : ‖∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
        (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I) * K t‖
      ≤ (3 * B * x₀ / L ^ 2) * 2000 * (Real.log (2 + ‖s‖) + 1) := by
    calc ‖∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
          (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I) * K t‖
        = ‖∫ t : ℝ, R t * K t‖ := by rw [hsplit]
      _ ≤ ∫ t : ℝ, ‖R t * K t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, 100 * (3 * B * x₀ / L ^ 2) *
            ((Real.log (2 + |t|) + 1) / (a ^ 2 + (t - b) ^ 2)) := by
          apply integral_mono_of_nonneg
          · filter_upwards with t using norm_nonneg (R t * K t)
          · exact hDint
          · filter_upwards with t using hRKpoint t
      _ = 100 * (3 * B * x₀ / L ^ 2) *
            ∫ t : ℝ, ((Real.log (2 + |t|) + 1) / (a ^ 2 + (t - b) ^ 2)) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ 100 * (3 * B * x₀ / L ^ 2) * (20 * (Real.log (2 + |b|) + 1)) :=
          mul_le_mul_of_nonneg_left (Commons.Analysis.Integral.integral_log_lorentz_le a b ha) (by positivity)
      _ = (3 * B * x₀ / L ^ 2) * 2000 * (Real.log (2 + |b|) + 1) := by ring
      _ ≤ (3 * B * x₀ / L ^ 2) * 2000 * (Real.log (2 + ‖s‖) + 1) := by
          have hb : Real.log (2 + |b|) ≤ Real.log (2 + ‖s‖) := by
            apply Real.log_le_log (by positivity)
            have : |b| ≤ ‖s‖ := by
              rw [hbdef]; exact Complex.abs_im_le_norm s
            linarith
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  have hgoal_conv : (∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
        (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I) *
        (∫ u : ℝ in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)) * (L:ℂ)) * (u:ℂ))) * f u))
      = ∫ t : ℝ, logDeriv (DirichletCharacter.LFunction χ)
        (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I) * K t := by
    apply MeasureTheory.integral_congr_ae; filter_upwards with t; rw [hKdef]
  rw [hgoal_conv]
  exact hmain

end Commons.NumberTheory.DirichletCharacter
