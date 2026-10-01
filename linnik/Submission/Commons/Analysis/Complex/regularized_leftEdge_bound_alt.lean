import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_one_sub
import Submission.Commons.NumberTheory.DirichletCharacter.leftEdge_logDeriv_bound
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_rightHalf_kernel_zero
import Submission.Commons.NumberTheory.DirichletCharacter.gammaFactor_kernel_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.psi_kernel_bound
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_norm_le_re_ge_three_halves
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale
import Submission.Commons.Analysis.Integral.regK_cplx_const_diff_integral_swap
import Submission.Commons.Analysis.Calculus.laplace_second_IBP_alt
import Submission.Commons.Analysis.Calculus.derivWithin_endpoint_le
import Submission.Commons.NumberTheory.DirichletCharacter.norm_logDeriv_LFunction_leftEdge_add_logN_le

open Complex MeasureTheory intervalIntegral Filter Set Topology
open scoped Real Topology BigOperators

set_option maxHeartbeats 800000

namespace Commons.Analysis.Complex

noncomputable section

open DirichletCharacter

/-! ## Clash-free archimedean/`Γℝ` helpers

These reproduce a handful of small lemmas that live only in the (clash-carrying) module
`completedLFunction_zeroNearHeight`, so that the functional-equation reduction of `L'/L` on
the left edge can be rebuilt without importing that module. -/

/-- Algebraic rearrangement used to isolate the `f 0`-regularization. -/
private lemma sq_mul_sub_div_self {z x y : ℂ} (hz : z ≠ 0) : z^2 * (x - y / z) = z^2 * x - z * y := by
  field_simp

private lemma differentiableAt_GammaR_of_ne_zero' {u : ℂ} (hu : Complex.Gammaℝ u ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ u := by
  have h : DifferentiableAt ℂ (fun s => (Complex.Gammaℝ s)⁻¹) u :=
    Complex.differentiable_Gammaℝ_inv.differentiableAt
  have hinv : DifferentiableAt ℂ (fun s => ((Complex.Gammaℝ s)⁻¹)⁻¹) u := h.inv (inv_ne_zero hu)
  have hfun : (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) = Complex.Gammaℝ := by
    funext s; rw [inv_inv]
  rwa [hfun] at hinv

private lemma GammaR_neg_half_ne_zero (t : ℝ) :
    Complex.Gammaℝ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hre := congrArg Complex.re hn
  simp at hre
  have h2 : ((2 * n : ℕ) : ℝ) = 1 / 2 := by push_cast; linarith
  have h4 : ((4 * n : ℕ) : ℝ) = 1 := by push_cast; linarith
  have h4' : 4 * n = 1 := by exact_mod_cast h4
  omega

private lemma gammaFactor_neg_half_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (t : ℝ) :
    DirichletCharacter.gammaFactor χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [hE.gammaFactor_def]
    exact GammaR_neg_half_ne_zero t
  · rw [hO.gammaFactor_def]
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, Complex.one_re]
    norm_num

private lemma differentiableAt_gammaFactor_neg_half {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (t : ℝ) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ)
      (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
  rcases χ.even_or_odd with hE | hO
  · rw [show DirichletCharacter.gammaFactor χ = Complex.Gammaℝ from funext hE.gammaFactor_def]
    exact differentiableAt_GammaR_of_ne_zero' (GammaR_neg_half_ne_zero t)
  · rw [show DirichletCharacter.gammaFactor χ = (fun w : ℂ => Complex.Gammaℝ (w + 1)) from
      funext hO.gammaFactor_def]
    refine (differentiableAt_GammaR_of_ne_zero' ?_).comp _ (by fun_prop)
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, Complex.one_re]
    norm_num

private lemma gammaFactor_ne_zero_of_pos_re' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.one_re]
    linarith

private lemma differentiableAt_gammaFactor_of_re_pos' {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  rcases χ.even_or_odd with h | h
  · rw [show DirichletCharacter.gammaFactor χ = Complex.Gammaℝ from funext h.gammaFactor_def]
    exact differentiableAt_GammaR_of_ne_zero' (Complex.Gammaℝ_ne_zero_of_re_pos hs)
  · rw [show DirichletCharacter.gammaFactor χ = fun u => Complex.Gammaℝ (u + 1) from
      funext (fun u => h.gammaFactor_def u)]
    refine (differentiableAt_GammaR_of_ne_zero' ?_).comp s (by fun_prop)
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.one_re]
    linarith

private lemma logDeriv_mul' (f g : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (hf0 : f z ≠ 0) (hg0 : g z ≠ 0) :
    logDeriv (f * g) z = logDeriv f z + logDeriv g z := by
  have h1 : logDeriv (f * g) z = (deriv f z * g z + f z * deriv g z) / (f z * g z) := by
    rw [logDeriv_apply, deriv_mul hf hg, Pi.mul_apply]
  rw [h1, logDeriv_apply, logDeriv_apply]
  field_simp

private lemma logDeriv_completedLFunction_eq_add_archimedean' {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs0 : s ≠ 0) (hsre : 0 < s.re)
    (hs : DirichletCharacter.LFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.gammaFactor χ) s +
        logDeriv (DirichletCharacter.LFunction χ) s := by
  have hU : {u : ℂ | 0 < u.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hsre
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 s]
      (fun u => DirichletCharacter.gammaFactor χ u * DirichletCharacter.LFunction χ u) :=
    Filter.eventually_of_mem hU (fun u hu => by
      have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu
      have hγ : DirichletCharacter.gammaFactor χ u ≠ 0 := gammaFactor_ne_zero_of_pos_re' χ hu
      have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ u (Or.inl hu0)
      show DirichletCharacter.completedLFunction χ u =
        DirichletCharacter.gammaFactor χ u * DirichletCharacter.LFunction χ u
      rw [h]
      exact (mul_div_cancel₀ (a := DirichletCharacter.completedLFunction χ u) hγ).symm)
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  exact logDeriv_mul' _ _ s (differentiableAt_gammaFactor_of_re_pos' χ hsre)
    (DirichletCharacter.differentiableAt_LFunction χ s (Or.inr hχ))
    (gammaFactor_ne_zero_of_pos_re' χ hsre) hs

/-- **Functional equation for the logarithmic derivative of `L(χ)` on `Re s = -1/2`.**
Clash-free reproduction of `LFunction_logDeriv_negHalf_FE`. -/
private theorem LFunction_logDeriv_negHalf_FE' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (t : ℝ) :
    logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)
      = - (Real.log (N : ℝ) : ℂ)
        - logDeriv (DirichletCharacter.LFunction χ⁻¹) ((3/2:ℝ) - (t : ℂ) * Complex.I)
        - (logDeriv (DirichletCharacter.gammaFactor χ⁻¹) ((3/2:ℝ) - (t : ℂ) * Complex.I)
            + logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) := by
  set s : ℂ := ((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = (-1/2 : ℝ) := by
    rw [hsdef]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one]
    norm_num
  have h1s : (1 : ℂ) - s = ((3/2:ℝ):ℂ) - (t : ℂ) * Complex.I := by
    rw [hsdef]; push_cast; ring
  have h1sre : ((1 : ℂ) - s).re = (3/2 : ℝ) := by
    rw [h1s]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one]
    norm_num
  have h1s_ne : (1 : ℂ) - s ≠ 0 := by
    intro h; rw [h] at h1sre; norm_num at h1sre
  have hN1 : N ≠ 1 := by rintro rfl; exact hχ (Subsingleton.elim χ 1)
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by rw [inv_inv]
      _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
      _ = 1 := by simp
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 := by
    rw [hsdef]
    exact Commons.NumberTheory.DirichletCharacter.LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim t
  have hLc : DirichletCharacter.LFunction (χ⁻¹) (1 - s) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ⁻¹) (Or.inl hχinv)
      (by rw [h1sre]; norm_num)
  have hΛs : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro h
    apply hLs
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1), h, zero_div]
  have hΛcs : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0 :=
    Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re (χ⁻¹)
      (by rw [h1sre]; norm_num)
  have hγs : DirichletCharacter.gammaFactor χ s ≠ 0 := by
    rw [hsdef]; exact gammaFactor_neg_half_ne_zero χ t
  have hγdiff : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
    rw [hsdef]; exact differentiableAt_gammaFactor_neg_half χ t
  have hsplit : logDeriv (DirichletCharacter.LFunction χ) s =
      logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (DirichletCharacter.gammaFactor χ) s := by
    have hfun : DirichletCharacter.LFunction χ =
        (fun z => DirichletCharacter.completedLFunction χ z / DirichletCharacter.gammaFactor χ z) :=
      funext (fun z => DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN1))
    rw [hfun]
    exact logDeriv_div (f := DirichletCharacter.completedLFunction χ)
      (g := DirichletCharacter.gammaFactor χ) s hΛs hγs
      ((DirichletCharacter.differentiable_completedLFunction (χ := χ) hχ) s) hγdiff
  have hFE : logDeriv (DirichletCharacter.completedLFunction χ) s =
      -(Real.log (N : ℝ) : ℂ) -
        logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s) :=
    Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_one_sub χ hχprim hΛs hΛcs
  have hsplit2 : logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s) =
      logDeriv (DirichletCharacter.gammaFactor (χ⁻¹)) (1 - s) +
        logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) :=
    logDeriv_completedLFunction_eq_add_archimedean' (χ := χ⁻¹) hχinv h1s_ne
      (by rw [h1sre]; norm_num) hLc
  rw [← h1s, hsplit, hFE, hsplit2]
  ring

private lemma regK_aemeasurable_logDeriv_gammaFactor_comp {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (σ : ℝ) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    AEStronglyMeasurable
      (fun u : ℝ => logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + ((φ u : ℝ) : ℂ) * Complex.I))
      volume := by
  have hline : Measurable (fun u : ℝ => (σ : ℂ) + ((φ u : ℝ) : ℂ) * Complex.I) := by fun_prop
  have h : Measurable
      (fun u : ℝ => logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + ((φ u : ℝ) : ℂ) * Complex.I)) := by
    have heq : (fun u : ℝ => logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + ((φ u : ℝ) : ℂ) * Complex.I))
        = (fun u : ℝ => deriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + ((φ u : ℝ) : ℂ) * Complex.I) /
DirichletCharacter.gammaFactor χ ((σ : ℂ) + ((φ u : ℝ) : ℂ) * Complex.I)) := by
      funext u; rw [logDeriv_apply]
    rw [heq]
    exact ((measurable_deriv (DirichletCharacter.gammaFactor χ)).comp hline).div
      ((Commons.NumberTheory.Linnik.measurable_gammaFactor χ).comp hline)
  exact h.aestronglyMeasurable

/-- `(exp(-(a+iu)λ) - 1)/(a+iu)²` is the common kernel, written as `PsiKernelBound.gK`. -/
private lemma regK_kernel_eq_gK (a lam u : ℝ) :
    (Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2) = PsiKernelBound.gK a lam u := by
  rw [PsiKernelBound.gK, div_eq_mul_inv]

/-- Continuity of the kernel. -/
private lemma regK_continuous_kernel (a lam : ℝ) (ha : 0 < a) :
    Continuous (fun u : ℝ =>
      (Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2)) := by
  refine Continuous.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro u
    refine pow_ne_zero 2 ?_
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith

/-- Integrability of `(logDeriv γF χ⁻¹)(3/2 - i(b-u)) + (logDeriv γF χ)(-1/2 + i(b-u))`
against the kernel. -/
private lemma regK_integrable_gammaSum_mul_kernel {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a lam b : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ =>
      (logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (((3/2:ℝ):ℂ) - (((b - u : ℝ)):ℂ) * Complex.I)
        + logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (((b - u : ℝ)):ℂ) * Complex.I)) *
      ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2))) volume := by
  have hdom : Integrable (fun u : ℝ =>
      (30:ℝ) * ((Real.log (2 + |b - u| / 2) + 7) * ‖PsiKernelBound.gK a lam u‖)) volume :=
    (PsiKernelBound.integrable_log_gK a lam b ha).const_mul 30
  refine Integrable.mono' hdom ?_ ?_
  · -- aemeasurability
    have h1 : AEStronglyMeasurable
        (fun u : ℝ => logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (((3/2:ℝ):ℂ) + (((u - b : ℝ)):ℂ) * Complex.I)) volume :=
      regK_aemeasurable_logDeriv_gammaFactor_comp (χ := χ⁻¹) (3/2) (fun u => u - b) (by fun_prop)
    have h1' : AEStronglyMeasurable
        (fun u : ℝ => logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (((3/2:ℝ):ℂ) - (((b - u : ℝ)):ℂ) * Complex.I)) volume := by
      refine h1.congr (Filter.Eventually.of_forall (fun u => ?_))
      congr 1
      push_cast; ring
    have h2 : AEStronglyMeasurable
        (fun u : ℝ => logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (((b - u : ℝ)):ℂ) * Complex.I)) volume :=
      regK_aemeasurable_logDeriv_gammaFactor_comp (χ := χ) (-1/2) (fun u => b - u) (by fun_prop)
    exact (h1'.add h2).mul (regK_continuous_kernel a lam ha).aestronglyMeasurable
  · -- pointwise bound
    filter_upwards with u
    have hb1 := Commons.NumberTheory.Linnik.norm_logDeriv_gammaFactor_at_three_halves (χ := χ⁻¹) (b - u)
    have hb2 := Commons.NumberTheory.Linnik.norm_logDeriv_gammaFactor_left χ (b - u)
    have hsum : ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (((3/2:ℝ):ℂ) - (((b - u : ℝ)):ℂ) * Complex.I)
          + logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (((b - u : ℝ)):ℂ) * Complex.I)‖
        ≤ (Real.log (2 + |b - u|) / 2 + 14) + 13 * (Real.log (2 + |b - u|) + 1) :=
      le_trans (norm_add_le _ _) (add_le_add hb1 hb2)
    have hlog : Real.log (2 + |b - u|) ≤ Real.log 2 + Real.log (2 + |b - u| / 2) := by
      have habs : (0:ℝ) ≤ |b - u| := abs_nonneg _
      have h1 : 2 + |b - u| ≤ 2 * (2 + |b - u| / 2) := by linarith
      have h2 : (0:ℝ) < 2 + |b - u| := by linarith
      have h3 : (0:ℝ) < 2 + |b - u| / 2 := by linarith
      calc Real.log (2 + |b - u|) ≤ Real.log (2 * (2 + |b - u| / 2)) := Real.log_le_log h2 h1
        _ = Real.log 2 + Real.log (2 + |b - u| / 2) := Real.log_mul (by norm_num) h3.ne'
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    have hLu : 0 ≤ Real.log (2 + |b - u| / 2) := Real.log_nonneg (by linarith [abs_nonneg (b - u)])
    have hkey : (Real.log (2 + |b - u|) / 2 + 14) + 13 * (Real.log (2 + |b - u|) + 1)
        ≤ 30 * (Real.log (2 + |b - u| / 2) + 7) := by
      nlinarith [hlog, hlog2, hlog2le, hLu]
    calc ‖(logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (((3/2:ℝ):ℂ) - (((b - u : ℝ)):ℂ) * Complex.I)
              + logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (((b - u : ℝ)):ℂ) * Complex.I)) *
            ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
              (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2))‖
          = ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (((3/2:ℝ):ℂ) - (((b - u : ℝ)):ℂ) * Complex.I)
              + logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (((b - u : ℝ)):ℂ) * Complex.I)‖ *
            ‖((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
              (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2))‖ := norm_mul _ _
        _ ≤ ((Real.log (2 + |b - u|) / 2 + 14) + 13 * (Real.log (2 + |b - u|) + 1)) *
            ‖((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
              (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2))‖ :=
          mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
        _ ≤ (30 * (Real.log (2 + |b - u| / 2) + 7)) *
            ‖((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
              (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2))‖ :=
          mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
        _ = (30:ℝ) * ((Real.log (2 + |b - u| / 2) + 7) * ‖PsiKernelBound.gK a lam u‖) := by
          rw [regK_kernel_eq_gK a lam u]; ring

theorem regK_logDeriv_LFunction_negHalf_regK_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (a lam b : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    ‖∫ u : ℝ, logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (((b - u : ℝ)):ℂ) * Complex.I) *
        ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
          (((a : ℂ) + (u : ℂ) * Complex.I)^2))‖ ≤ 400 := by
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by rw [inv_inv]
      _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
      _ = 1 := by simp
  set F : ℝ → ℂ := fun u => logDeriv (DirichletCharacter.LFunction χ)
      (((-1/2:ℝ):ℂ) + (((b - u : ℝ)):ℂ) * Complex.I) *
      ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2)) with hF
  set g1 : ℝ → ℂ := fun u => (-((Real.log (N:ℝ)) : ℂ)) *
      ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2)) with hg1
  set g2 : ℝ → ℂ := fun u => logDeriv (DirichletCharacter.LFunction χ⁻¹)
      (((3/2:ℝ):ℂ) - (((b - u : ℝ)):ℂ) * Complex.I) *
      ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2)) with hg2
  set g3 : ℝ → ℂ := fun u =>
      (logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (((3/2:ℝ):ℂ) - (((b - u : ℝ)):ℂ) * Complex.I)
        + logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (((b - u : ℝ)):ℂ) * Complex.I)) *
      ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2)) with hg3
  -- integrability of the kernel
  have hKint : Integrable (fun u : ℝ =>
      (Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2)) volume := by
    simpa only [PsiKernelBound.gK, div_eq_mul_inv] using PsiKernelBound.integrable_gK a lam ha
  have hKzero : (∫ u : ℝ,
      (Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2)) = 0 := by
    simpa only [PsiKernelBound.gK, div_eq_mul_inv] using PsiKernelBound.integral_gK_zero a lam ha hlam
  -- integrability of g1
  have hI1 : Integrable g1 := by
    simp only [hg1]
    exact hKint.const_mul (-((Real.log (N:ℝ)) : ℂ))
  -- integrability of g2
  have hmeasL2 : AEStronglyMeasurable (fun u : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ⁻¹) (((3/2:ℝ):ℂ) - (((b - u : ℝ)):ℂ) * Complex.I)) volume := by
    have hF2 : Differentiable ℂ (DirichletCharacter.LFunction χ⁻¹) :=
      DirichletCharacter.differentiable_LFunction hχinv
    have heq : (fun u : ℝ => logDeriv (DirichletCharacter.LFunction χ⁻¹)
          (((3/2:ℝ):ℂ) - (((b - u : ℝ)):ℂ) * Complex.I))
        = (fun u : ℝ => deriv (DirichletCharacter.LFunction χ⁻¹)
              (((3/2:ℝ):ℂ) - (((b - u : ℝ)):ℂ) * Complex.I) /
            DirichletCharacter.LFunction χ⁻¹ (((3/2:ℝ):ℂ) - (((b - u : ℝ)):ℂ) * Complex.I)) := by
      funext u; rw [logDeriv_apply]
    rw [heq]
    exact (((measurable_deriv (DirichletCharacter.LFunction χ⁻¹)).comp (by fun_prop)).div
      (hF2.continuous.measurable.comp (by fun_prop))).aestronglyMeasurable
  have hI2 : Integrable g2 := by
    simp only [hg2]
    refine Integrable.mono' (hKint.norm.const_mul (20:ℝ)) ?_ ?_
    · exact hmeasL2.mul (regK_continuous_kernel a lam ha).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_norm_le_re_ge_three_halves (χ⁻¹) (s := _) (by simp)
  -- integrability of g3
  have hI3 : Integrable g3 := by
    have h := regK_integrable_gammaSum_mul_kernel (χ := χ) a lam b ha
    rwa [hg3]
  -- pointwise identity
  have hF_eq : F =ᵐ[volume] (fun u : ℝ => g1 u - g2 u - g3 u) := by
    refine Filter.Eventually.of_forall (fun u => ?_)
    simp only [hF, hg1, hg2, hg3]
    rw [LFunction_logDeriv_negHalf_FE' χ hχ hχprim (b - u)]
    ring
  -- splitting of the integral
  have hsplit : (∫ u : ℝ, g1 u - g2 u - g3 u)
      = (∫ u : ℝ, g1 u) - (∫ u : ℝ, g2 u) - (∫ u : ℝ, g3 u) := by
    rw [MeasureTheory.integral_sub (f := fun u => g1 u - g2 u) (g := g3) (hI1.sub hI2) hI3,
        MeasureTheory.integral_sub (f := g1) (g := g2) hI1 hI2]
  have hg1zero : (∫ u : ℝ, g1 u) = 0 := by
    simp only [hg1]
    rw [MeasureTheory.integral_const_mul, hKzero, mul_zero]
  have hg2zero : (∫ u : ℝ, g2 u) = 0 := by
    have h := Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_rightHalf_kernel_zero (χ⁻¹) hχinv a lam b ha hlam
    rwa [hg2]
  have hg3bound : ‖∫ u : ℝ, g3 u‖ ≤ 400 := by
    have h := Commons.NumberTheory.DirichletCharacter.gammaFactor_kernel_bound χ hχprim a lam b ha hlam
    rwa [hg3]
  have hgoal : (∫ u : ℝ, F u) = -(∫ u : ℝ, g3 u) := by
    have h1 : (∫ u : ℝ, F u) = (∫ u : ℝ, g1 u - g2 u - g3 u) :=
      MeasureTheory.integral_congr_ae hF_eq
    rw [h1, hsplit, hg1zero, hg2zero]
    ring
  rw [hgoal, norm_neg]
  exact hg3bound


theorem regularized_leftEdge_bound_alt {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {L : ℝ} (hL : 1 < L) {s : ℂ} (hs : (0:ℝ) < s.re + 1/2) :
    ‖∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) *
        ((∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
          - f 0 / ((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)))‖
      ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / L ^ 2 * 2000 * (Real.log (2 + ‖s‖) + 1) 
    := by
  have hL0 : (0:ℝ) < L := by linarith
  set a : ℝ := s.re + 1/2 with hadef
  set b : ℝ := s.im with hbdef
  have ha : 0 < a := by rw [hadef]; exact hs
  -- The left-edge logarithmic derivative, as a function of the imaginary part.
  set hfun : ℝ → ℂ := fun t =>
    logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I) with hfundef
  -- The full integrand of the target.
  set F : ℝ → ℂ := fun τ =>
    logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) *
      ((∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
        - f 0 / ((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))) with hFdef
  have hF_eq : ∀ τ : ℝ, F τ = hfun τ *
      ((∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
        - f 0 / ((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))) := by
    intro τ; rw [hFdef, hfundef]
  -- The regularized Laplace transform in the `u`-variable.
  set Psi : ℝ → ℂ := fun u =>
    (∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((a:ℂ) + (u:ℂ) * Complex.I) * (L:ℂ)) * (t:ℂ))) * f t)
      - f 0 / (((a:ℂ) + (u:ℂ) * Complex.I) * (L:ℂ)) with hPsibdef
  -- The explicit right-hand side of the two integrations by parts.
  set A : ℝ → ℂ := fun u =>
    derivWithin f (Set.Ioi 0) 0 * (1 - Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * ((L*x₀:ℝ):ℂ))))
      + ∫ σ in (0:ℝ)..x₀,
          (Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * ((L*σ:ℝ):ℂ)))
            - Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * ((L*x₀:ℝ):ℂ)))) * iteratedDeriv 2 f σ
    with hAdef
  -- Complex-valued `u ↦ a + i u` is never zero.
  have hw_ne : ∀ u : ℝ, (((a:ℂ) + (u:ℂ) * Complex.I)) ≠ 0 := by
    intro u h
    have := congrArg Complex.re h
    simp at this
    exact ha.ne' this
  -- Step 1: complex conjugation of the shift `τ ↦ b - u`.
  have hwu : ∀ u : ℝ, s - (((-1/2:ℝ):ℂ) + ((b - u : ℝ):ℂ) * Complex.I)
      = (a:ℂ) + (u:ℂ) * Complex.I := by
    intro u
    rw [hadef, hbdef]
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.sub_im, Complex.add_im,
        Complex.mul_im] <;> ring
  -- Step 2: two integrations by parts, in `u`-variable form.
  have hIbp : ∀ u : ℝ, (((a:ℂ)+(u:ℂ)*Complex.I) * (L:ℂ))^2 * Psi u = A u := by
    intro u
    have hwre : 0 < (((a:ℂ) + (u:ℂ) * Complex.I)).re := by
      rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      norm_num
      exact ha
    have h := Commons.Analysis.Calculus.laplace_second_IBP_alt (x₀ := x₀) (B := B) hx₀ hB hcont hf2 hBnd hvan
      (L := L) hL0 (w := ((a:ℂ) + (u:ℂ) * Complex.I)) hwre
    have hz : (((a:ℂ) + (u:ℂ) * Complex.I) * (L:ℂ)) ≠ 0 :=
      mul_ne_zero (hw_ne u) (by exact_mod_cast hL0.ne')
    have hker : ∀ τ : ℝ, Complex.exp (-(((a:ℂ) + (u:ℂ)*Complex.I) * ((L*τ:ℝ):ℂ)))
        = Complex.exp (-(((a:ℂ) + (u:ℂ)*Complex.I) * (L:ℂ) * (τ:ℂ))) := by
      intro τ; congr 1; rw [Complex.ofReal_mul]; ring
    rw [hPsibdef, hAdef]
    simp only
    rw [sq_mul_sub_div_self hz]
    simp_rw [hker]
    exact h
  -- Measurability and growth bound for `hfun`.
  have hhfun_meas : Measurable hfun := by
    rw [hfundef]
    have h1 : Measurable (logDeriv (DirichletCharacter.LFunction χ)) := by
      have heq : logDeriv (DirichletCharacter.LFunction χ)
          = fun z => deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z := by
        funext z; rw [logDeriv_apply]
      rw [heq]
      exact (measurable_deriv _).div
        ((DirichletCharacter.differentiable_LFunction hχ).continuous.measurable)
    exact h1.comp (by fun_prop)
  have hhfun_bound : ∀ t : ℝ,
      ‖hfun t‖ ≤ (Real.log (N:ℝ) + 100) * (Real.log (2 + |t|) + 1) := by
    intro t
    rw [hfundef]
    simp only
    have h := Commons.NumberTheory.DirichletCharacter.norm_logDeriv_LFunction_leftEdge_add_logN_le
      χ hχ hχprim t
    have hlog : (0:ℝ) ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    have hN : 0 ≤ Real.log (N:ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    have hkey : ‖logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)‖
        ≤ 100 * (Real.log (2 + |t|) + 1) + Real.log (N:ℝ) := by
      have h2 : logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)
          = (logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)
              + ((Real.log (N:ℝ)):ℂ)) - ((Real.log (N:ℝ)):ℂ) := by ring
      rw [h2]
      have h3 : ‖(logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)
              + ((Real.log (N:ℝ)):ℂ)) - ((Real.log (N:ℝ)):ℂ)‖
          ≤ ‖logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)
              + ((Real.log (N:ℝ)):ℂ)‖ + Real.log (N:ℝ) := by
        calc ‖(logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)
                + ((Real.log (N:ℝ)):ℂ)) - ((Real.log (N:ℝ)):ℂ)‖
            ≤ ‖logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)
                + ((Real.log (N:ℝ)):ℂ)‖ + ‖((Real.log (N:ℝ)):ℂ)‖ := norm_sub_le _ _
          _ = ‖logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)
                + ((Real.log (N:ℝ)):ℂ)‖ + Real.log (N:ℝ) := by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN]
      linarith [h, h3]
    calc ‖logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t:ℂ) * Complex.I)‖
        ≤ 100 * (Real.log (2 + |t|) + 1) + Real.log (N:ℝ) := hkey
      _ ≤ (Real.log (N:ℝ) + 100) * (Real.log (2 + |t|) + 1) := by nlinarith [hlog, hN]
  -- Step 3: substitution τ ↦ b - u and unfolding of the integrand.
  have hsubst : (∫ τ : ℝ, F τ) = ∫ u : ℝ, F (b - u) :=
    (integral_sub_left_eq_self F volume b).symm
  have hpoint : ∀ u : ℝ, F (b - u) = hfun (b - u) * Psi u := by
    intro u
    rw [hFdef, hPsibdef, hfundef]
    simp only
    rw [hwu u]
  have hpoint_int : (∫ u : ℝ, F (b - u)) = ∫ u : ℝ, hfun (b - u) * Psi u := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    exact hpoint u
  have hPsi_eq : ∀ u : ℝ, Psi u = A u / (((a:ℂ)+(u:ℂ)*Complex.I) * (L:ℂ))^2 := by
    intro u
    have hz : (((a:ℂ)+(u:ℂ)*Complex.I) * (L:ℂ)) ≠ 0 :=
      mul_ne_zero (hw_ne u) (by exact_mod_cast hL0.ne')
    rw [eq_div_iff (pow_ne_zero 2 hz)]
    rw [mul_comm]
    exact hIbp u
  have hstep4 : (∫ u : ℝ, hfun (b - u) * Psi u)
      = ∫ u : ℝ, hfun (b - u) * (A u / (((a:ℂ)+(u:ℂ)*Complex.I) * (L:ℂ))^2) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [hPsi_eq u]
  have hstep5 : (∫ u : ℝ, hfun (b - u) * (A u / (((a:ℂ)+(u:ℂ)*Complex.I) * (L:ℂ))^2))
      = ((L:ℂ)^2)⁻¹ * (∫ u : ℝ, hfun (b - u) * (A u / (((a:ℂ)+(u:ℂ)*Complex.I))^2)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    have hz : (((a:ℂ)+(u:ℂ)*Complex.I)) ≠ 0 := hw_ne u
    have hLc : ((L:ℂ)) ≠ 0 := by exact_mod_cast hL0.ne'
    field_simp
  -- Step 4: the Fubini swap.
  set Pbig : ℝ → ℂ := fun σ => ∫ u : ℝ, hfun (b - u) *
      ((Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * ((L*σ:ℝ):ℂ))) - 1)
        / (((a:ℂ) + (u:ℂ) * Complex.I)^2)) with hPbigdef
  have hPbound : ∀ σ : ℝ, 0 < σ → σ ≤ x₀ → ‖Pbig σ‖ ≤ 400 := by
    intro σ hσ0 hσx
    have h := regK_logDeriv_LFunction_negHalf_regK_bound
      χ hχ hχprim a (L*σ) b ha (by positivity)
    rw [hPbigdef]; simp only [hfundef]
    exact h
  have hiter2 : iteratedDeriv 2 f = deriv (deriv f) := by
    ext x
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  have hSwapped : (∫ u : ℝ, hfun (b - u) * (A u / (((a:ℂ) + (u:ℂ) * Complex.I))^2))
      = (-(derivWithin f (Set.Ioi 0) 0)) * Pbig x₀
        + ∫ σ in (0:ℝ)..x₀, iteratedDeriv 2 f σ * (Pbig σ - Pbig x₀) := by
    have h := Commons.Analysis.Integral.regK_cplx_const_diff_integral_swap
      (h := hfun) (g := iteratedDeriv 2 f) (Ch := Real.log (N:ℝ) + 100) (B := B)
      (c := derivWithin f (Set.Ioi 0) 0) (b := b)
      (by rw [hiter2]; exact measurable_deriv (deriv f))
      (by positivity) hhfun_meas hhfun_bound ha hx₀ hL0 hB hBnd
    simp only [hAdef, hPbigdef] at h ⊢
    exact h
  -- Step 5: bounds.
  have hbound1 : ‖(-(derivWithin f (Set.Ioi 0) 0)) * Pbig x₀‖
      ≤ ‖derivWithin f (Set.Ioi 0) 0‖ * 400 := by
    rw [norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_left (hPbound x₀ hx₀ le_rfl) (norm_nonneg _)
  have hbound2 : ‖∫ σ in (0:ℝ)..x₀, iteratedDeriv 2 f σ * (Pbig σ - Pbig x₀)‖
      ≤ 800 * B * x₀ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := x₀)
      (C := 800 * B) (f := fun σ : ℝ => iteratedDeriv 2 f σ * (Pbig σ - Pbig x₀)) ?_
    · simpa [abs_of_pos hx₀] using this
    · intro σ hσ
      rw [uIoc_of_le hx₀.le] at hσ
      rcases lt_or_eq_of_le hσ.2 with hlt | heq
      · have h1 : ‖iteratedDeriv 2 f σ‖ ≤ B := hBnd σ ⟨hσ.1, hlt⟩
        have h2 : ‖Pbig σ - Pbig x₀‖ ≤ 800 := by
          refine le_trans (norm_sub_le _ _) ?_
          have h3 := hPbound σ hσ.1 (le_of_lt hlt)
          have h4 := hPbound x₀ hx₀ le_rfl
          linarith
        rw [norm_mul]
        nlinarith [norm_nonneg (iteratedDeriv 2 f σ), norm_nonneg (Pbig σ - Pbig x₀), hB]
      · subst heq
        simp only [sub_self, mul_zero, norm_zero]
        positivity
  have hQbound : ‖∫ u : ℝ, hfun (b - u) * (A u / (((a:ℂ) + (u:ℂ) * Complex.I))^2)‖
      ≤ ‖derivWithin f (Set.Ioi 0) 0‖ * 400 + 800 * B * x₀ := by
    rw [hSwapped]
    exact le_trans (norm_add_le _ _) (add_le_add hbound1 hbound2)
  have hc_bound : ‖derivWithin f (Set.Ioi 0) 0‖ ≤ ‖f 0‖ / x₀ + B * x₀ :=
    (Commons.Analysis.Calculus.derivWithin_endpoint_le hx₀ hcont hf2 hBnd hvan).1
  have hLn : ‖(((L:ℂ))^2)⁻¹‖ = (L^2)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
  change ‖∫ τ : ℝ, F τ‖ ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / L ^ 2 * 2000 *
      (Real.log (2 + ‖s‖) + 1)
  calc ‖∫ τ : ℝ, F τ‖
      = ‖∫ u : ℝ, F (b - u)‖ := by rw [hsubst]
    _ = ‖∫ u : ℝ, hfun (b - u) * Psi u‖ := by rw [hpoint_int]
    _ = ‖∫ u : ℝ, hfun (b - u) * (A u / (((a:ℂ)+(u:ℂ)*Complex.I) * (L:ℂ))^2)‖ := by
          rw [hstep4]
    _ = ‖((L:ℂ)^2)⁻¹ * (∫ u : ℝ, hfun (b - u) * (A u / (((a:ℂ)+(u:ℂ)*Complex.I))^2))‖ := by
          rw [hstep5]
    _ = ‖(((L:ℂ))^2)⁻¹‖ * ‖∫ u : ℝ, hfun (b - u) * (A u / (((a:ℂ)+(u:ℂ)*Complex.I))^2)‖ :=
          norm_mul _ _
    _ ≤ (L^2)⁻¹ * (‖derivWithin f (Set.Ioi 0) 0‖ * 400 + 800 * B * x₀) := by
          rw [hLn]
          exact mul_le_mul_of_nonneg_left hQbound (by positivity)
    _ ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / L ^ 2 * 2000 * (Real.log (2 + ‖s‖) + 1) := by
          have hY : (1:ℝ) ≤ Real.log (2 + ‖s‖) + 1 := by
            have h0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
            linarith
          have hstep : (L^2)⁻¹ * (‖derivWithin f (Set.Ioi 0) 0‖ * 400 + 800 * B * x₀)
              ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / L ^ 2 * 2000 := by
            have hnum : ‖derivWithin f (Set.Ioi 0) 0‖ * 400 + 800 * B * x₀
                ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) * 2000 := by
              have h400 : ‖derivWithin f (Set.Ioi 0) 0‖ * 400
                  ≤ (‖f 0‖ / x₀ + B * x₀) * 400 :=
                mul_le_mul_of_nonneg_right hc_bound (by norm_num)
              have he : (‖f 0‖ / x₀ + B * x₀) * 400 + 800 * B * x₀
                  = 400 * (‖f 0‖ / x₀) + 1200 * (B * x₀) := by ring
              have hf : (3 * B * x₀ + 2 * ‖f 0‖ / x₀) * 2000
                  = 4000 * (‖f 0‖ / x₀) + 6000 * (B * x₀) := by ring
              have h1 : 0 ≤ ‖f 0‖ / x₀ := div_nonneg (norm_nonneg (f 0)) hx₀.le
              have h2 : 0 ≤ B * x₀ := mul_nonneg hB hx₀.le
              linarith
            calc (L^2)⁻¹ * (‖derivWithin f (Set.Ioi 0) 0‖ * 400 + 800 * B * x₀)
                = (‖derivWithin f (Set.Ioi 0) 0‖ * 400 + 800 * B * x₀) / L^2 := by ring
              _ ≤ ((3 * B * x₀ + 2 * ‖f 0‖ / x₀) * 2000) / L^2 :=
                  div_le_div_of_nonneg_right hnum (by positivity)
              _ = (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / L ^ 2 * 2000 := by ring
          calc (L^2)⁻¹ * (‖derivWithin f (Set.Ioi 0) 0‖ * 400 + 800 * B * x₀)
              ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / L ^ 2 * 2000 := hstep
            _ ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / L ^ 2 * 2000 * (Real.log (2 + ‖s‖) + 1) :=
                le_mul_of_one_le_right (by positivity) hY


end

end Commons.Analysis.Complex
