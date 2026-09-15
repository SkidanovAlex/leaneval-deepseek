import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_horizontal_segment_bound
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_horizontal_segment_bound_neg
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le

open Complex DirichletCharacter MeasureTheory
open scoped Real Topology Interval
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

section Helpers
variable {N : ℕ} [NeZero N]

private lemma digamma_strip_le (z : ℂ) (hre1 : -(1/4 : ℝ) ≤ z.re) (hre2 : z.re ≤ 8)
    (him : 1 ≤ |z.im|) : ‖Complex.digamma z‖ ≤ Real.log (2 + |z.im|) + 3 := by
  by_cases h : (1/2 : ℝ) ≤ z.re
  · have hb := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le z.re z.im h hre2
    have hb' : ‖Complex.digamma z‖ ≤ Real.log (2 + |z.im|) + 2 := by
      rw [Complex.re_add_im z] at hb
      exact hb
    linarith
  · push Not at h
    have hz : ∀ m : ℕ, z ≠ -(m : ℂ) := by
      intro m hm
      have h0 : z.im = 0 := by rw [hm]; simp
      rw [h0] at him
      exact absurd him (by norm_num)
    have hshift := Complex.digamma_apply_add_one z hz
    have h1 : Complex.digamma z = Complex.digamma (z + 1) - z⁻¹ := by
      rw [hshift]; ring
    have hre1' : (1/2 : ℝ) ≤ (z + 1).re := by simp [Complex.add_re]; linarith
    have hre2' : (z + 1).re ≤ 8 := by simp [Complex.add_re]; linarith
    have him' : (z + 1).im = z.im := by simp
    have hb := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le (z+1).re (z+1).im hre1' hre2'
    have hb' : ‖Complex.digamma (z + 1)‖ ≤ Real.log (2 + |z.im|) + 2 := by
      rw [Complex.re_add_im (z+1), him'] at hb
      exact hb
    have hznorm : (1:ℝ) ≤ ‖z‖ := le_trans him (Complex.abs_im_le_norm z)
    have hinv : ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      rw [inv_le_one₀ (by linarith : (0:ℝ) < ‖z‖)]
      exact hznorm
    rw [h1]
    calc ‖Complex.digamma (z + 1) - z⁻¹‖ ≤ ‖Complex.digamma (z + 1)‖ + ‖z⁻¹‖ := norm_sub_le _ _
      _ ≤ (Real.log (2 + |z.im|) + 2) + 1 := add_le_add hb' hinv
      _ = Real.log (2 + |z.im|) + 3 := by ring


private lemma Gamma_ne_zero_of_im_ne_zero {z : ℂ} (h : z.im ≠ 0) : Gamma z ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := (Complex.Gamma_eq_zero_iff z).mp h0
  apply h
  rw [hn]; simp

private lemma pi_c_ne_zero : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

private lemma norm_complex_log_pi : ‖Complex.log (Real.pi : ℂ)‖ = Real.log Real.pi := by
  have hpi : (0:ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  rw [show Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) from (Complex.ofReal_log hpi).symm]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact Real.log_nonneg (by linarith [Real.pi_gt_three])

private lemma logDeriv_cpow_neg_half (s : ℂ) :
    logDeriv (fun t : ℂ => (Real.pi : ℂ) ^ (-t/2)) s =
      -(1/2 : ℂ) * Complex.log (Real.pi : ℂ) := by
  have hne : (Real.pi : ℂ) ^ (-s/2) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl pi_c_ne_zero)
  rw [logDeriv_apply]
  have hd : deriv (fun t : ℂ => -t/2) s = -(1/2) := by
    have hfun : (fun t : ℂ => -t/2) = fun t => (-(1/2)) * t := by funext t; ring
    rw [hfun, deriv_const_mul_field]; simp
  have hderiv : deriv (fun t : ℂ => (Real.pi : ℂ) ^ (-t/2)) s =
      Complex.log (Real.pi : ℂ) * (-(1/2)) * (Real.pi : ℂ) ^ (-s/2) := by
    calc deriv (fun t : ℂ => (Real.pi : ℂ) ^ (-t/2)) s
        = Complex.log (Real.pi : ℂ) * deriv (fun t : ℂ => -t/2) s *
            (Real.pi : ℂ) ^ (-s/2) :=
          Complex.deriv_const_cpow (c := (Real.pi : ℂ)) (x := s) (f := fun t : ℂ => -t/2)
            (by fun_prop)
      _ = Complex.log (Real.pi : ℂ) * (-(1/2)) * (Real.pi : ℂ) ^ (-s/2) := by rw [hd]
  rw [hderiv, div_eq_mul_inv, mul_inv_cancel_right₀ hne]
  ring

private lemma logDeriv_Gamma_half (s : ℂ) (hs : Gamma (s/2) ≠ 0) :
    logDeriv (fun t : ℂ => Gamma (t/2)) s = (1/2) * digamma (s/2) := by
  have hne : ∀ m : ℕ, s/2 ≠ -(m : ℂ) := by
    intro m hm
    exact hs ((Complex.Gamma_eq_zero_iff (s/2)).mpr ⟨m, hm⟩)
  have hdiff : DifferentiableAt ℂ Gamma (s/2) := differentiableAt_Gamma (s/2) hne
  have h := logDeriv_comp (f := Gamma) (g := fun t : ℂ => t/2) (x := s) hdiff (by fun_prop)
  have hd : deriv (fun t : ℂ => t/2) s = (1/2 : ℂ) := by
    have hfun : (fun t : ℂ => t/2) = fun t => (1/2) * t := by funext t; ring
    rw [hfun, deriv_const_mul_field]; simp
  calc logDeriv (fun t : ℂ => Gamma (t/2)) s
      = logDeriv Gamma (s/2) * deriv (fun t : ℂ => t/2) s := h
    _ = digamma (s/2) * (1/2) := by rw [digamma_def, hd]
    _ = (1/2) * digamma (s/2) := by ring

private lemma logDeriv_gammaFactor_even {χ : DirichletCharacter ℂ N} (hχ : χ.Even) (s : ℂ)
    (hs : Gamma (s/2) ≠ 0) :
    logDeriv (gammaFactor χ) s = -(1/2 : ℂ) * Complex.log (Real.pi : ℂ) + (1/2) * digamma (s/2) := by
  have hfun : gammaFactor χ = Gammaℝ := by
    funext t; exact Even.gammaFactor_def hχ t
  have hGR : Gammaℝ = fun t : ℂ => (Real.pi : ℂ) ^ (-t/2) * Gamma (t/2) := by
    funext t; rw [Gammaℝ_def]
  rw [hfun, hGR]
  have hne : (Real.pi : ℂ) ^ (-s/2) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl pi_c_ne_zero)
  have hf : DifferentiableAt ℂ (fun t : ℂ => (Real.pi : ℂ) ^ (-t/2)) s :=
    (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => -t/2) s).const_cpow (Or.inl pi_c_ne_zero)
  have hg : DifferentiableAt ℂ (fun t : ℂ => Gamma (t/2)) s := by
    have hne' : ∀ m : ℕ, s/2 ≠ -(m : ℂ) := by
      intro m hm; exact hs ((Complex.Gamma_eq_zero_iff (s/2)).mpr ⟨m, hm⟩)
    exact (differentiableAt_Gamma (s/2) hne').comp s (by fun_prop)
  rw [logDeriv_mul s hne hs hf hg, logDeriv_cpow_neg_half s, logDeriv_Gamma_half s hs]

private lemma logDeriv_cpow_affine (a b : ℂ) (s : ℂ) :
    logDeriv (fun t : ℂ => (Real.pi : ℂ) ^ (a*t + b)) s = a * Complex.log (Real.pi : ℂ) := by
  have hne : (Real.pi : ℂ) ^ (a*s + b) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl pi_c_ne_zero)
  rw [logDeriv_apply]
  have hd : deriv (fun t : ℂ => a*t + b) s = a := by
    have hfun : (fun t : ℂ => a*t + b) = fun t => a * t + b := by funext t; ring
    rw [hfun, deriv_add_const, deriv_const_mul_field]; simp
  have hderiv : deriv (fun t : ℂ => (Real.pi : ℂ) ^ (a*t+b)) s =
      Complex.log (Real.pi : ℂ) * a * (Real.pi : ℂ) ^ (a*s+b) := by
    calc deriv (fun t : ℂ => (Real.pi : ℂ) ^ (a*t+b)) s
        = Complex.log (Real.pi : ℂ) * deriv (fun t : ℂ => a*t+b) s *
            (Real.pi : ℂ) ^ (a*s+b) :=
          Complex.deriv_const_cpow (c := (Real.pi : ℂ)) (x := s) (f := fun t : ℂ => a*t+b)
            (by fun_prop)
      _ = Complex.log (Real.pi : ℂ) * a * (Real.pi : ℂ) ^ (a*s+b) := by rw [hd]
  rw [hderiv, div_eq_mul_inv, mul_inv_cancel_right₀ hne]
  ring

private lemma logDeriv_Gamma_affine (a : ℂ) (b : ℂ) (s : ℂ) (ha : a ≠ 0)
    (h : Gamma (a*s + b) ≠ 0) :
    logDeriv (fun t : ℂ => Gamma (a*t + b)) s = a * digamma (a*s + b) := by
  have hne : ∀ m : ℕ, a*s + b ≠ -(m : ℂ) := by
    intro m hm
    exact h ((Complex.Gamma_eq_zero_iff (a*s+b)).mpr ⟨m, hm⟩)
  have hdiff : DifferentiableAt ℂ Gamma (a*s + b) := differentiableAt_Gamma (a*s+b) hne
  have hcomp : (fun t : ℂ => Gamma (a*t+b)) = Gamma ∘ (fun t : ℂ => a*t+b) := rfl
  have hd : deriv (fun t : ℂ => a*t + b) s = a := by
    have hfun : (fun t : ℂ => a*t + b) = fun t => a * t + b := by funext t; ring
    rw [hfun, deriv_add_const, deriv_const_mul_field]; simp
  calc logDeriv (fun t : ℂ => Gamma (a*t+b)) s
      = logDeriv Gamma (a*s+b) * deriv (fun t : ℂ => a*t+b) s :=
        logDeriv_comp (f := Gamma) (g := fun t : ℂ => a*t+b) (x := s) hdiff (by fun_prop)
    _ = digamma (a*s+b) * a := by rw [digamma_def, hd]
    _ = a * digamma (a*s+b) := by rw [mul_comm]

private lemma logDeriv_gammaFactor_odd {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) (s : ℂ)
    (hs : Gamma ((s+1)/2) ≠ 0) :
    logDeriv (gammaFactor χ) s =
      -(1/2 : ℂ) * Complex.log (Real.pi : ℂ) + (1/2) * digamma ((s+1)/2) := by
  have hfun : gammaFactor χ = fun t : ℂ => Gammaℝ (t+1) := by
    funext t; exact Odd.gammaFactor_def hχ t
  have hGR : (fun t : ℂ => Gammaℝ (t+1)) =
      fun t : ℂ => (Real.pi : ℂ) ^ ((-(1/2))*t + (-(1/2))) * Gamma ((1/2)*t + (1/2)) := by
    funext t; rw [Gammaℝ_def]; ring_nf
  rw [hfun, hGR]
  have hne : (Real.pi : ℂ) ^ ((-(1/2))*s + (-(1/2))) ≠ 0 :=
    (Complex.cpow_ne_zero_iff).mpr (Or.inl pi_c_ne_zero)
  have hs' : Gamma ((1/2)*s + (1/2)) ≠ 0 := by
    convert hs using 2; ring
  have hf : DifferentiableAt ℂ
      (fun t : ℂ => (Real.pi : ℂ) ^ ((-(1/2))*t + (-(1/2)))) s :=
    (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => (-(1/2))*t + (-(1/2))) s).const_cpow
      (Or.inl pi_c_ne_zero)
  have hg : DifferentiableAt ℂ (fun t : ℂ => Gamma ((1/2)*t + (1/2))) s := by
    have hne' : ∀ m : ℕ, (1/2)*s + (1/2) ≠ -(m : ℂ) := by
      intro m hm; exact hs' ((Complex.Gamma_eq_zero_iff ((1/2)*s+(1/2))).mpr ⟨m, hm⟩)
    exact (differentiableAt_Gamma ((1/2)*s + (1/2)) hne').comp s (by fun_prop)
  rw [logDeriv_mul s hne hs' hf hg, logDeriv_cpow_affine (-(1/2)) (-(1/2)) s,
    logDeriv_Gamma_affine (1/2) (1/2) s (by norm_num)]
  · congr 2; ring
  · convert hs using 2; ring


/-- The logarithmic derivative of the archimedean Gamma factor is bounded by `3 log (N (|v|+3))`
on the horizontal segment `{x + iv : -1/2 ≤ x ≤ 2}` for `2 ≤ |v|`. -/
private lemma norm_logDeriv_gammaFactor_le (χ : DirichletCharacter ℂ N)
    (v : ℝ) (hv : 2 ≤ |v|) (x : ℝ) (hx1 : -(1/2 : ℝ) ≤ x) (hx2 : x ≤ 2) :
    ‖logDeriv (gammaFactor χ) ((x : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      3 * Real.log (N * (|v| + 3)) := by
  set s : ℂ := (x : ℂ) + (v : ℂ) * Complex.I with hs
  have hsim : s.im = v := by simp [hs]
  have hsre : s.re = x := by simp [hs]
  have hv0 : 0 < |v| := by linarith
  have hvne : v ≠ 0 := abs_pos.mp hv0
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hTN : (5:ℝ) ≤ (N:ℝ) * (|v| + 3) := by
    have hT3 : (5:ℝ) ≤ |v| + 3 := by linarith
    calc (5:ℝ) = 1 * 5 := by ring
      _ ≤ (N:ℝ) * (|v| + 3) := mul_le_mul hN1 hT3 (by norm_num) (by linarith)
  have hLpi : Real.log Real.pi ≤ Real.log ((N:ℝ) * (|v| + 3)) := by
    exact Real.log_le_log Real.pi_pos
      (le_trans (le_of_lt Real.pi_lt_four) (le_trans (by norm_num) hTN))
  have hL1 : (1:ℝ) ≤ Real.log ((N:ℝ) * (|v| + 3)) := by
    have he : Real.exp 1 ≤ (N:ℝ) * (|v| + 3) :=
      (le_of_lt Real.exp_one_lt_three).trans ((by norm_num : (3:ℝ) ≤ 5).trans hTN)
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log ((N:ℝ) * (|v| + 3)) := Real.log_le_log (Real.exp_pos 1) he
  have hlogT : Real.log (2 + |v/2|) ≤ Real.log ((N:ℝ) * (|v| + 3)) := by
    apply Real.log_le_log (by positivity)
    have h1 : |v/2| = |v| / 2 := by rw [abs_div]; norm_num
    rw [h1]
    have h2 : (2:ℝ) + |v|/2 ≤ |v| + 3 := by linarith [abs_nonneg v]
    have h3 : (|v| + 3 : ℝ) ≤ (N:ℝ) * (|v| + 3) := by
      have := mul_le_mul_of_nonneg_right hN1 (by linarith [abs_nonneg v] : (0:ℝ) ≤ |v| + 3)
      simpa using this
    linarith
  have hkey : ∀ z : ℂ, z.im = v/2 → -(1/4:ℝ) ≤ z.re → z.re ≤ 8 →
      ‖Complex.digamma z‖ ≤ Real.log (2 + |v/2|) + 3 := by
    intro z hzim hz1 hz2
    rw [← hzim]
    refine digamma_strip_le z hz1 hz2 ?_
    rw [hzim]
    have h2 : |v/2| = |v| / 2 := by rw [abs_div]; norm_num
    rw [h2]
    linarith [abs_nonneg v]
  rcases χ.even_or_odd with hE | hO
  · have hhalf : s/2 = (1/2 : ℂ) * s := by ring
    have him : (s/2).im = v/2 := by rw [hhalf, Complex.mul_im]; simp [hsim]; ring
    have hre : (s/2).re = x/2 := by rw [hhalf, Complex.mul_re]; simp [hsre]; ring
    have hγ : Complex.Gamma (s/2) ≠ 0 :=
      Gamma_ne_zero_of_im_ne_zero (by rw [him]; exact div_ne_zero hvne two_ne_zero)
    have hψ := hkey (s/2) him (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [logDeriv_gammaFactor_even hE s hγ]
    calc ‖-(1/2 : ℂ) * Complex.log (Real.pi : ℂ) + (1/2) * Complex.digamma (s/2)‖
        ≤ ‖-(1/2 : ℂ) * Complex.log (Real.pi : ℂ)‖ +
            ‖(1/2 : ℂ) * Complex.digamma (s/2)‖ := norm_add_le _ _
      _ = (1/2) * Real.log Real.pi + (1/2) * ‖Complex.digamma (s/2)‖ := by
            rw [norm_mul, norm_neg, norm_mul, norm_complex_log_pi]
            norm_num
      _ ≤ (1/2) * Real.log ((N:ℝ) * (|v| + 3)) +
            (1/2) * (Real.log (2 + |v/2|) + 3) := by
            have h1' := mul_le_mul_of_nonneg_left hLpi (by norm_num : (0:ℝ) ≤ 1/2)
            have h2' := mul_le_mul_of_nonneg_left hψ (by norm_num : (0:ℝ) ≤ 1/2)
            linarith
      _ ≤ 3 * Real.log ((N:ℝ) * (|v| + 3)) := by
            have := mul_le_mul_of_nonneg_left hlogT (by norm_num : (0:ℝ) ≤ 1/2)
            linarith
  · have hhalf : (s+1)/2 = (1/2 : ℂ) * (s+1) := by ring
    have him : ((s+1)/2).im = v/2 := by
      rw [hhalf, Complex.mul_im]; simp [Complex.add_im, hsim]; ring
    have hre : ((s+1)/2).re = (x+1)/2 := by
      rw [hhalf, Complex.mul_re]; simp [Complex.add_re, hsre]; ring
    have hγ : Complex.Gamma ((s+1)/2) ≠ 0 :=
      Gamma_ne_zero_of_im_ne_zero (by rw [him]; exact div_ne_zero hvne two_ne_zero)
    have hψ := hkey ((s+1)/2) him (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [logDeriv_gammaFactor_odd hO s hγ]
    calc ‖-(1/2 : ℂ) * Complex.log (Real.pi : ℂ) + (1/2) * Complex.digamma ((s+1)/2)‖
        ≤ ‖-(1/2 : ℂ) * Complex.log (Real.pi : ℂ)‖ +
            ‖(1/2 : ℂ) * Complex.digamma ((s+1)/2)‖ := norm_add_le _ _
      _ = (1/2) * Real.log Real.pi + (1/2) * ‖Complex.digamma ((s+1)/2)‖ := by
            rw [norm_mul, norm_neg, norm_mul, norm_complex_log_pi]
            norm_num
      _ ≤ (1/2) * Real.log ((N:ℝ) * (|v| + 3)) +
            (1/2) * (Real.log (2 + |v/2|) + 3) := by
            have h1' := mul_le_mul_of_nonneg_left hLpi (by norm_num : (0:ℝ) ≤ 1/2)
            have h2' := mul_le_mul_of_nonneg_left hψ (by norm_num : (0:ℝ) ≤ 1/2)
            linarith
      _ ≤ 3 * Real.log ((N:ℝ) * (|v| + 3)) := by
            have := mul_le_mul_of_nonneg_left hlogT (by norm_num : (0:ℝ) ≤ 1/2)
            linarith

/-- On a horizontal segment, `logDeriv (LFunction χ)` is the difference of
`logDeriv (completedLFunction χ)` and `logDeriv (gammaFactor χ)`. -/
private lemma logDeriv_LFunction_eq (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : s ≠ 0) (hΛ : completedLFunction χ s ≠ 0) (hγ : gammaFactor χ s ≠ 0)
    (hdΛ : DifferentiableAt ℂ (completedLFunction χ) s)
    (hdγ : DifferentiableAt ℂ (gammaFactor χ) s) :
    logDeriv (LFunction χ) s =
      logDeriv (completedLFunction χ) s - logDeriv (gammaFactor χ) s := by
  have hcongr : LFunction χ =ᶠ[𝓝 s]
      (fun t => completedLFunction χ t / gammaFactor χ t) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht
    exact LFunction_eq_completed_div_gammaFactor χ t (Or.inl ht)
  have h1 : logDeriv (LFunction χ) s =
      logDeriv (fun t => completedLFunction χ t / gammaFactor χ t) s :=
    (logDeriv_congr_nhds hcongr).eq_of_nhds
  rw [h1, logDeriv_div s hΛ hγ hdΛ hdγ]

/-- Continuity of `logDeriv f` away from the zeros of `f`, for `f` differentiable everywhere
(e.g. `LFunction χ` or `completedLFunction χ`). -/
private lemma contOn_logDeriv_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ContinuousOn (fun z : ℂ => logDeriv f z) {z : ℂ | f z ≠ 0} := by
  have hderv : ContinuousOn (deriv f) {z : ℂ | f z ≠ 0} := hf.deriv.continuous.continuousOn
  have hFc : ContinuousOn f {z : ℂ | f z ≠ 0} := hf.continuous.continuousOn
  have hdiv : ContinuousOn (fun z : ℂ => deriv f z / f z) {z : ℂ | f z ≠ 0} :=
    ContinuousOn.div hderv hFc (by intro z hz; exact hz)
  simpa [logDeriv] using hdiv

/-- `Gammaℝ = π^{-s/2} Γ(s/2)` is differentiable away from its zeros. -/
private lemma differentiableAt_GammaR_of_im {t : ℂ} (h : (t/2).im ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ t := by
  have hne : ∀ m : ℕ, t/2 ≠ -(m : ℂ) := by
    intro m hm
    exact h (by rw [hm]; simp)
  rw [show Complex.Gammaℝ = fun u : ℂ => (Real.pi : ℂ) ^ (-u/2) * Complex.Gamma (u/2) from
    funext fun u => Complex.Gammaℝ_def u]
  refine DifferentiableAt.mul ?_ ?_
  · exact (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => -u/2) t).const_cpow
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  · exact (Complex.differentiableAt_Gamma (t/2) hne).comp t (by fun_prop)

/-- Integral form of the passage from `Λ` to `L` on a horizontal segment: on
`{x + iT' : -1/2 ≤ x ≤ 2}` the logarithmic derivative of `LFunction χ` is bounded pointwise by
that of `completedLFunction χ` plus `3 log (N(T'+3))`, whence the integral of the former is at
most the integral of the latter plus `8 log (N(T'+3))`.

The only hypothesis on the zeros is that no zero of `Λ(χ,·)` lies within distance `δ > 0` of
the line `Im s = T'`; this is used to know that `Λ` (hence `L`) does not vanish on the segment. -/
private lemma integral_logDeriv_LFunction_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (v : ℝ) (hv : 2 ≤ |v|) (δ : ℝ) (hδ : 0 < δ)
    (hno : ∀ ρ : ℂ, completedLFunction χ ρ = 0 → δ ≤ |ρ.im - v|) :
    (∫ x : ℝ in (-1/2)..2, ‖logDeriv (LFunction χ) ((x : ℂ) + (v : ℂ) * Complex.I)‖) ≤
      (∫ x : ℝ in (-1/2)..2,
          ‖logDeriv (completedLFunction χ) ((x : ℂ) + (v : ℂ) * Complex.I)‖) +
        8 * Real.log (N * (|v| + 3)) := by
  set s : ℝ → ℂ := fun x => (x : ℂ) + (v : ℂ) * Complex.I with hs
  have hsim : ∀ x : ℝ, (s x).im = v := by intro x; simp [s]
  have hv0 : 0 < |v| := by linarith
  have hvne : v ≠ 0 := abs_pos.mp hv0
  have hs0 : ∀ x : ℝ, s x ≠ 0 := by
    intro x h
    have h0 : (s x).im = 0 := by rw [h]; simp
    rw [hsim x] at h0
    exact hvne h0
  have hL0 : 0 ≤ Real.log ((N : ℝ) * (|v| + 3)) := by
    apply Real.log_nonneg
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    nlinarith
  have hhalf_im : ∀ x : ℝ, ((s x) / 2).im = v/2 := by
    intro x
    rw [show (s x)/2 = (1/2 : ℂ) * s x from by ring, Complex.mul_im]
    simp [hsim x]
    ring
  have hhalf_im' : ∀ x : ℝ, ((s x + 1) / 2).im = v/2 := by
    intro x
    rw [show (s x + 1)/2 = (1/2 : ℂ) * (s x + 1) from by ring, Complex.mul_im]
    simp [Complex.add_im, hsim x]
    ring
  have hΛnz : ∀ x : ℝ, completedLFunction χ (s x) ≠ 0 := by
    intro x hzero
    have h1 := hno (s x) hzero
    rw [hsim x] at h1
    have h2 : |v - v| = 0 := by simp
    rw [h2] at h1
    linarith
  have hγnz : ∀ x : ℝ, gammaFactor χ (s x) ≠ 0 := by
    intro x
    have hpi : ((Real.pi : ℂ) ^ (-(s x)/2)) ≠ 0 :=
      (Complex.cpow_ne_zero_iff).mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    have hpi' : ((Real.pi : ℂ) ^ (-(s x+1)/2)) ≠ 0 :=
      (Complex.cpow_ne_zero_iff).mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    rcases χ.even_or_odd with hE | hO
    · rw [show gammaFactor χ = Complex.Gammaℝ from funext fun t => Even.gammaFactor_def hE t,
        Complex.Gammaℝ_def]
      exact mul_ne_zero hpi (Gamma_ne_zero_of_im_ne_zero (by rw [hhalf_im x]; exact div_ne_zero hvne two_ne_zero))
    · rw [show gammaFactor χ = fun t => Complex.Gammaℝ (t+1) from
          funext fun t => Odd.gammaFactor_def hO t]
      change Complex.Gammaℝ (s x + 1) ≠ 0
      rw [Complex.Gammaℝ_def]
      exact mul_ne_zero hpi' (Gamma_ne_zero_of_im_ne_zero (by rw [hhalf_im' x]; exact div_ne_zero hvne two_ne_zero))
  have hdγ : ∀ x : ℝ, DifferentiableAt ℂ (gammaFactor χ) (s x) := by
    intro x
    rcases χ.even_or_odd with hE | hO
    · rw [show gammaFactor χ = Complex.Gammaℝ from funext fun t => Even.gammaFactor_def hE t]
      exact differentiableAt_GammaR_of_im (by rw [hhalf_im x]; exact div_ne_zero hvne two_ne_zero)
    · rw [show gammaFactor χ = fun t => Complex.Gammaℝ (t+1) from
        funext fun t => Odd.gammaFactor_def hO t]
      change DifferentiableAt ℂ (fun t : ℂ => Complex.Gammaℝ (t+1)) (s x)
      exact (differentiableAt_GammaR_of_im (t := s x + 1)
        (by rw [hhalf_im' x]; exact div_ne_zero hvne two_ne_zero)).comp (x := s x)
        (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => t + 1) (s x))
  have hdΛ : ∀ x : ℝ, DifferentiableAt ℂ (completedLFunction χ) (s x) :=
    fun x => differentiable_completedLFunction hχ (s x)
  have hLnz : ∀ x : ℝ, LFunction χ (s x) ≠ 0 := by
    intro x
    rw [LFunction_eq_completed_div_gammaFactor χ (s x) (Or.inl (hs0 x))]
    exact div_ne_zero (hΛnz x) (hγnz x)
  have hcontL : ContinuousOn (fun x : ℝ => logDeriv (LFunction χ) (s x)) (Set.Icc (-1/2) 2) :=
    (contOn_logDeriv_of_differentiable (differentiable_LFunction hχ)).comp
      (by fun_prop : Continuous s).continuousOn (fun x _ => hLnz x)
  have hcontΛ : ContinuousOn (fun x : ℝ => logDeriv (completedLFunction χ) (s x))
      (Set.Icc (-1/2) 2) :=
    (contOn_logDeriv_of_differentiable (differentiable_completedLFunction hχ)).comp
      (by fun_prop : Continuous s).continuousOn (fun x _ => hΛnz x)
  have hintL : IntervalIntegrable (fun x : ℝ => ‖logDeriv (LFunction χ) (s x)‖)
      volume (-1/2) 2 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (-1/2 : ℝ) ≤ 2)] using hcontL.norm
  have hintΛ : IntervalIntegrable (fun x : ℝ => ‖logDeriv (completedLFunction χ) (s x)‖)
      volume (-1/2) 2 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (-1/2 : ℝ) ≤ 2)] using hcontΛ.norm
  have hpt : ∀ x ∈ Set.Icc (-1/2 : ℝ) 2, ‖logDeriv (LFunction χ) (s x)‖ ≤
      ‖logDeriv (completedLFunction χ) (s x)‖ + 3 * Real.log (N * (|v| + 3)) := by
    intro x hx
    have h1 := logDeriv_LFunction_eq χ (s x) (hs0 x) (hΛnz x) (hγnz x) (hdΛ x) (hdγ x)
    have h2 : ‖logDeriv (gammaFactor χ) (s x)‖ ≤ 3 * Real.log (N * (|v| + 3)) :=
      norm_logDeriv_gammaFactor_le χ v hv x (by linarith [hx.1]) hx.2
    calc ‖logDeriv (LFunction χ) (s x)‖
        = ‖logDeriv (completedLFunction χ) (s x) - logDeriv (gammaFactor χ) (s x)‖ := by rw [h1]
      _ ≤ ‖logDeriv (completedLFunction χ) (s x)‖ + ‖logDeriv (gammaFactor χ) (s x)‖ :=
            norm_sub_le _ _
      _ ≤ ‖logDeriv (completedLFunction χ) (s x)‖ + 3 * Real.log (N * (|v| + 3)) := by
            linarith
  have hconst : IntervalIntegrable
      (fun x : ℝ => ‖logDeriv (completedLFunction χ) (s x)‖ + 3 * Real.log (N * (|v| + 3)))
      volume (-1/2) 2 := hintΛ.add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on (a := (-1/2 : ℝ)) (b := 2)
    (by norm_num) hintL hconst hpt
  rw [intervalIntegral.integral_add hintΛ intervalIntegrable_const] at hmono
  have hc : (∫ x : ℝ in (-1/2)..2, (3 * Real.log (N * (|v| + 3))))
      = (2 - (-1/2)) * (3 * Real.log (N * (|v| + 3))) := by
    rw [intervalIntegral.integral_const]
    simp
  rw [hc] at hmono
  have h8 : (2 - (-1/2)) * (3 * Real.log (N * (|v| + 3))) ≤ 8 * Real.log (N * (|v| + 3)) := by
    nlinarith [hL0]
  linarith


/-- `log (N (T'+3)) ≥ 1` for `T' ≥ 2` (needed to absorb lower-order terms). -/
private lemma hsb_logN_ge_one (T' : ℝ) (hT : 2 ≤ T') :
    (1 : ℝ) ≤ Real.log ((N : ℝ) * (T' + 3)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h5 : (5 : ℝ) ≤ (N : ℝ) * (T' + 3) := by
    have hT3 : (5 : ℝ) ≤ T' + 3 := by linarith
    calc (5 : ℝ) = 1 * 5 := by ring
      _ ≤ (N : ℝ) * (T' + 3) := mul_le_mul hN1 hT3 (by norm_num) (by linarith)
  have he : Real.exp 1 ≤ (N : ℝ) * (T' + 3) :=
    (le_of_lt Real.exp_one_lt_three).trans ((by norm_num : (3 : ℝ) ≤ 5).trans h5)
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((N : ℝ) * (T' + 3)) := Real.log_le_log (Real.exp_pos 1) he

end Helpers

theorem horizontalSegment_logDeriv_bound_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T' : ℝ, 2 ≤ T' → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im - T'|) →
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im + T'|) →
      ((∫ x : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.LFunction χ)
            ((x : ℂ) + (T' : ℂ) * Complex.I)‖) ≤
          C * Real.log (N * (T' + 3)) * (Real.log (N * (T' + 3)) + Real.log (1 / δ))) ∧
      ((∫ x : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.LFunction χ)
            ((x : ℂ) - (T' : ℂ) * Complex.I)‖) ≤
          C * Real.log (N * (T' + 3)) * (Real.log (N * (T' + 3)) + Real.log (1 / δ))) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := completedLogDeriv_horizontal_segment_bound χ hχ hχprim
  obtain ⟨C₁, hC₁pos, hC₁⟩ := completedLogDeriv_horizontal_segment_bound_neg χ hχ hχprim
  refine ⟨max (C₀ + 8) (C₁ + 8), by positivity, ?_⟩
  intro T' hT δ hδ hδ1 H1 H2
  have hT0 : (0:ℝ) ≤ T' := by linarith
  have hu0 : 0 < (N : ℝ) * (T' + 3) := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have h : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
      linarith
    exact mul_pos hNpos (by linarith)
  have hL1 : (1 : ℝ) ≤ Real.log ((N : ℝ) * (T' + 3)) := hsb_logN_ge_one T' hT
  have hlog0 : (0 : ℝ) ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    rw [one_div]
    exact (one_le_inv₀ hδ).mpr hδ1
  have hmax : max 0 (Real.log (1 / δ)) = Real.log (1 / δ) := max_eq_right hlog0
  have hX0 : (0:ℝ) ≤ Real.log ((N : ℝ) * (T' + 3)) *
      (Real.log ((N : ℝ) * (T' + 3)) + Real.log (1 / δ)) :=
    mul_nonneg (by linarith) (by linarith)
  have hfunL : (fun x : ℝ => ‖logDeriv (LFunction χ) ((x : ℂ) - (T' : ℂ) * Complex.I)‖)
      = fun x : ℝ => ‖logDeriv (LFunction χ) ((x : ℂ) + ((-T' : ℝ) : ℂ) * Complex.I)‖ := by
    funext x
    rw [show (x : ℂ) - (T' : ℂ) * Complex.I = (x : ℂ) + ((-T' : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
  have hfunA : (fun x : ℝ => ‖logDeriv (completedLFunction χ) ((x : ℂ) - (T' : ℂ) * Complex.I)‖)
      = fun x : ℝ =>
          ‖logDeriv (completedLFunction χ) ((x : ℂ) + ((-T' : ℝ) : ℂ) * Complex.I)‖ := by
    funext x
    rw [show (x : ℂ) - (T' : ℂ) * Complex.I = (x : ℂ) + ((-T' : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
  constructor
  · have hcore := hC₀ T' hT δ hδ H1
    rw [hmax, mul_add] at hcore
    have htrans := integral_logDeriv_LFunction_le χ hχ T'
      (by rw [abs_of_nonneg hT0]; exact hT) δ hδ H1
    rw [abs_of_nonneg hT0] at htrans
    have hJ : (∫ x : ℝ in (-1/2)..2,
          ‖logDeriv (LFunction χ) ((x : ℂ) + (T' : ℂ) * Complex.I)‖)
        ≤ (C₀ + 8) * Real.log ((N : ℝ) * (T' + 3)) *
            (Real.log ((N : ℝ) * (T' + 3)) + Real.log (1 / δ)) := by
      nlinarith [hcore, htrans, hL1, hlog0, hC₀pos]
    have hCax : C₀ + 8 ≤ max (C₀ + 8) (C₁ + 8) := le_max_left _ _
    nlinarith [hJ, hCax, hL1, hlog0]
  · have hvneg : (2:ℝ) ≤ |(-T')| := by rw [abs_neg, abs_of_nonneg hT0]; exact hT
    have hno' : ∀ ρ : ℂ, completedLFunction χ ρ = 0 → δ ≤ |ρ.im - (-T')| := by
      intro ρ hρ
      have h := H2 ρ hρ
      have hgoal : |ρ.im - (-T')| = |ρ.im + T'| := by rw [sub_neg_eq_add]
      rw [hgoal]
      exact h
    have hcore := hC₁ T' hT δ hδ H2
    rw [hmax, mul_add] at hcore
    rw [hfunA] at hcore
    have htrans := integral_logDeriv_LFunction_le χ hχ (-T') hvneg δ hδ hno'
    rw [abs_neg, abs_of_nonneg hT0] at htrans
    have hJ : (∫ x : ℝ in (-1/2)..2,
          ‖logDeriv (LFunction χ) ((x : ℂ) + ((-T' : ℝ) : ℂ) * Complex.I)‖)
        ≤ (C₁ + 8) * Real.log ((N : ℝ) * (T' + 3)) *
            (Real.log ((N : ℝ) * (T' + 3)) + Real.log (1 / δ)) := by
      nlinarith [hcore, htrans, hL1, hlog0, hC₁pos]
    rw [hfunL]
    have hCax : C₁ + 8 ≤ max (C₀ + 8) (C₁ + 8) := le_max_right _ _
    nlinarith [hJ, hCax, hL1, hlog0]


end Commons.NumberTheory.DirichletCharacter
