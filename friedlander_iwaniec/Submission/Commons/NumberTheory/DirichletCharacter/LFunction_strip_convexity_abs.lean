import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_abs_sq_half
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_vertical_poly_lower
import Submission.Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
import Submission.Commons.NumberTheory.DirichletCharacter.Even_inv
import Submission.Commons.NumberTheory.DirichletCharacter.Odd_inv
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_eq
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_upper_explicit
open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Commons.NumberTheory.DirichletCharacter
private lemma Gamma_star (w : ℂ) : Complex.Gamma (star w) = star (Complex.Gamma w) := by
  simpa using Complex.Gamma_conj w
private lemma norm_Gamma_star (w : ℂ) : ‖Complex.Gamma (star w)‖ = ‖Complex.Gamma w‖ := by
  rw [Gamma_star, norm_star]

private lemma gamma_abs_sq_half' (v : ℝ) :
    ‖Complex.Gamma ((1/2:ℂ) + ((v:ℝ):ℂ)*I)‖^2 = Real.pi / Real.cosh (Real.pi * v) := by
  have h := Commons.Analysis.SpecialFunctions.Gamma.gamma_abs_sq_half v
  rwa [mul_comm I _] at h

private lemma cosh_pi_abs (v : ℝ) : Real.cosh (Real.pi * v) = Real.cosh (Real.pi * |v|) := by
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
  · rw [abs_of_nonpos hv, mul_neg, Real.cosh_neg]

private lemma four_add_sq_ge (t : ℝ) : 2 + |t| ≤ 4 + t^2 := by
  nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 1/2)]

private lemma clog_bounds {s : ℂ} (hre0 : 0 ≤ s.re) (hre1 : s.re ≤ 1) :
    Real.log (2 + |s.im|) / 2 ≤ ‖Complex.log (s + 2)‖ ∧
    ‖Complex.log (s + 2)‖ ≤ Real.log (2 + |s.im|) + 5 := by
  set w : ℂ := s + 2 with hw
  have hwre : w.re = s.re + 2 := by rw [hw]; simp
  have hwim : w.im = s.im := by rw [hw]; simp
  have hnorm_sq : ‖w‖^2 = w.re^2 + w.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnorm_ge2 : 2 ≤ ‖w‖ := by
    have : 4 ≤ ‖w‖^2 := by rw [hnorm_sq, hwre, hwim]; nlinarith [hre0, sq_nonneg s.im]
    nlinarith [norm_nonneg w]
  have hlogre : (Complex.log w).re = Real.log ‖w‖ := Complex.log_re w
  have hlogpos : 0 ≤ Real.log ‖w‖ := Real.log_nonneg (by linarith)
  have hlow : Real.log (2 + |s.im|) / 2 ≤ ‖Complex.log w‖ := by
    have h1 : Real.log (2 + |s.im|) ≤ Real.log (‖w‖^2) := by
      apply Real.log_le_log (by positivity)
      rw [hnorm_sq, hwre, hwim]
      nlinarith [hre0, four_add_sq_ge s.im]
    rw [Real.log_pow] at h1
    push_cast at h1
    have h2 : (Complex.log w).re ≤ ‖Complex.log w‖ :=
      (le_abs_self _).trans (abs_re_le_norm _)
    rw [hlogre] at h2
    linarith
  have hup : ‖Complex.log w‖ ≤ Real.log (2 + |s.im|) + 5 := by
    have h1 : ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    have h2 : |(Complex.log w).re| = Real.log ‖w‖ := by rw [hlogre, abs_of_nonneg hlogpos]
    have h3 : |(Complex.log w).im| ≤ Real.pi := by rw [Complex.log_im]; exact Complex.abs_arg_le_pi w
    have h4 : Real.log ‖w‖ ≤ 1 + Real.log (2 + |s.im|) := by
      have h5 : ‖w‖ ≤ 2 * (2 + |s.im|) := by
        have h6 : ‖w‖^2 ≤ (2 * (2 + |s.im|))^2 := by
          rw [hnorm_sq, hwre, hwim]
          nlinarith [hre0, hre1, sq_abs s.im, abs_nonneg s.im, sq_nonneg s.im]
        nlinarith [norm_nonneg w, abs_nonneg s.im]
      have h6 := Real.log_le_log (by linarith [norm_nonneg w] : (0:ℝ) < ‖w‖) h5
      have h7 : Real.log (2 * (2 + |s.im|)) = Real.log 2 + Real.log (2 + |s.im|) :=
        Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by linarith [abs_nonneg s.im] : (2:ℝ) + |s.im| ≠ 0)
      have h8 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith [h6, h7, h8]
    calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| := h1
      _ ≤ Real.log ‖w‖ + Real.pi := by rw [h2]; linarith [h3]
      _ ≤ 1 + Real.log (2 + |s.im|) + Real.pi := by linarith
      _ ≤ Real.log (2 + |s.im|) + 5 := by linarith [Real.pi_lt_four]
  exact ⟨by rwa [hw] at hlow, by rwa [hw] at hup⟩

private lemma sinh_le_mul_cosh (y : ℝ) (hy : 0 ≤ y) : Real.sinh y ≤ y * Real.cosh y := by
  have hmono : MonotoneOn (fun y => y * Real.cosh y - Real.sinh y) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    · intro y hy
      exact (((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub
        (Real.hasDerivAt_sinh y)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hd : deriv (fun y => y * Real.cosh y - Real.sinh y) y = y * Real.sinh y := by
        have h : deriv (fun y => y * Real.cosh y - Real.sinh y) y =
            Real.cosh y + y * Real.sinh y - Real.cosh y := by
          simpa using (((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub
            (Real.hasDerivAt_sinh y)).deriv
        rw [h]; ring
      rw [hd]
      exact mul_nonneg hy.le (Real.sinh_nonneg_iff.mpr hy.le)
  have h0 : (0:ℝ) ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_refl 0)
  have hy' : y ∈ Set.Ici 0 := Set.mem_Ici.mpr hy
  have := hmono h0 hy' hy
  simp only [mul_zero, Real.cosh_zero, Real.sinh_zero, sub_zero] at this
  linarith [this]

private lemma tanh_le_self (x : ℝ) (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos x)]
  exact sinh_le_mul_cosh x hx

private lemma tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

private lemma Gamma_ratio_decay (s : ℂ) (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ ≤
      Real.exp ((1/2 - s.re/2) * (Real.log (2 + |s.im|) + 2)) := by
  set u₂ : ℝ := 1 - s.re/4 with hu₂
  set u₁ : ℝ := 1/2 + s.re/4 with hu₁
  set τ : ℝ := s.im/4 with hτ
  have hu1 : (1:ℝ)/2 ≤ u₁ := by rw [hu₁]; linarith
  have h12 : u₁ ≤ u₂ := by rw [hu₁, hu₂]; linarith
  have h2 : u₂ ≤ 8 := by rw [hu₂]; linarith
  have hu2m1 : u₂ - u₁ = 1/2 - s.re/2 := by rw [hu₂, hu₁]; ring
  have hnum : (1 - s/4) = star (((u₂ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I) := by
    rw [hu₂, hτ]; apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im] <;> ring
  have hden : (1/2 + s/4) = ((u₁ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I := by
    rw [hu₁, hτ]; apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im] <;> ring
  have hA : Complex.Gamma (((u₂ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.re hm; simp at this; linarith [hu1]
  have hB : Complex.Gamma (((u₁ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.re hm; simp at this; linarith [hu1]
  have hApos : 0 < ‖Complex.Gamma (((u₂ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I)‖ := norm_pos_iff.mpr hA
  have hBpos : 0 < ‖Complex.Gamma (((u₁ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I)‖ := norm_pos_iff.mpr hB
  have hinc := Commons.Analysis.SpecialFunctions.Gamma.log_norm_Gamma_sub_le u₁ u₂ τ hu1 h12 h2
  have hτabs : |τ| = |s.im|/4 := by rw [hτ, abs_div]; norm_num
  have hlog : Real.log (2 + |τ|) ≤ Real.log (2 + |s.im|) := by
    apply Real.log_le_log (by positivity); rw [hτabs]; linarith [abs_nonneg s.im]
  have hratio : ‖Complex.Gamma (((u₂ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I)‖ /
      ‖Complex.Gamma (((u₁ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * I)‖ ≤
      Real.exp ((u₂ - u₁) * (Real.log (2 + |s.im|) + 2)) := by
    have h := Real.exp_le_exp.mpr hinc
    rw [Real.exp_sub, Real.exp_log hApos, Real.exp_log hBpos] at h
    refine h.trans (Real.exp_le_exp.mpr ?_)
    have h0 : 0 ≤ u₂ - u₁ := by rw [hu2m1]; linarith
    nlinarith [hlog, h0]
  rw [hnum, hden, norm_div, norm_Gamma_star]
  refine hratio.trans (le_of_eq ?_)
  rw [hu2m1]


private lemma Gamma_one_norm_sq (v : ℝ) (hv : v ≠ 0) :
    ‖Complex.Gamma ((1:ℂ) + ((v:ℝ):ℂ)*I)‖^2 = Real.pi * |v| / Real.sinh (Real.pi * |v|) := by
  have hvne : ((v:ℝ):ℂ) ≠ 0 := by exact_mod_cast hv
  have hvn : (|v|:ℝ) ≠ 0 := abs_ne_zero.mpr hv
  have hsinhpos : 0 < Real.sinh (Real.pi * |v|) := by rw [Real.sinh_pos_iff]; positivity
  have hsinhne : Real.sinh (Real.pi * |v|) ≠ 0 := ne_of_gt hsinhpos
  set w : ℂ := (1:ℂ) + ((v:ℝ):ℂ)*I with hw
  have hwne : w ≠ 0 := by
    rw [hw]; intro h; apply hv; have := congrArg Complex.im h; simpa using this
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  have h1w : 1 - w = -(((v:ℝ):ℂ)*I) := by rw [hw]; ring
  rw [h1w] at hrefl
  have hnegne : -(((v:ℝ):ℂ)*I) ≠ 0 := by
    intro h; apply hvne; have := congrArg Complex.im h; simpa using this
  have hadd := Complex.Gamma_add_one (-(((v:ℝ):ℂ)*I)) hnegne
  have hEq1 : -(((v:ℝ):ℂ)*I) + 1 = 1 - ((v:ℝ):ℂ)*I := by ring
  rw [hEq1] at hadd
  have hGneg : Complex.Gamma (-(((v:ℝ):ℂ)*I)) =
      Complex.Gamma (1 - ((v:ℝ):ℂ)*I) / (-(((v:ℝ):ℂ)*I)) := by
    rw [hadd]; field_simp
  have hstarw : star w = 1 - ((v:ℝ):ℂ)*I := by
    rw [hw]; apply Complex.ext <;> simp
  have hsinw : Complex.sin ((Real.pi:ℂ) * w) = -(Complex.sinh ((Real.pi:ℂ)*((v:ℝ):ℂ)) * I) := by
    rw [hw]
    have harg : (Real.pi:ℂ) * ((1:ℂ) + ((v:ℝ):ℂ)*I) = (Real.pi:ℂ) + I*((Real.pi:ℂ)*((v:ℝ):ℂ)) := by ring
    rw [harg, Complex.sin_add, Complex.sin_pi, Complex.cos_pi, zero_mul, neg_one_mul, zero_add,
        ← Complex.sin_mul_I]
    ring
  have hnormsin : ‖Complex.sin ((Real.pi:ℂ) * w)‖ = Real.sinh (Real.pi * |v|) := by
    rw [hsinw, norm_neg, norm_mul, Complex.norm_I, mul_one]
    have hcast : Complex.sinh ((Real.pi:ℂ)*((v:ℝ):ℂ)) = ((Real.sinh (Real.pi*v):ℝ):ℂ) := by
      rw [← Complex.ofReal_mul, Complex.ofReal_sinh]
    rw [hcast]
    rw [show ‖Complex.ofReal (Real.sinh (Real.pi*v))‖ = |Real.sinh (Real.pi*v)| from RCLike.norm_ofReal _]
    rw [Real.abs_sinh, abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]
  have hnorm := congrArg norm hrefl
  rw [norm_mul, norm_div, Complex.norm_of_nonneg (le_of_lt Real.pi_pos)] at hnorm
  have hnegv : ‖(-(((v:ℝ):ℂ)*I))‖ = |v| := by
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one]
    exact RCLike.norm_ofReal v
  have hG1 : ‖Complex.Gamma (-(((v:ℝ):ℂ)*I))‖ = ‖Complex.Gamma w‖ / |v| := by
    rw [hGneg, norm_div, hnegv]
    have h1 : ‖Complex.Gamma (1 - ((v:ℝ):ℂ)*I)‖ = ‖Complex.Gamma w‖ := by
      have := norm_Gamma_star w
      rwa [hstarw] at this
    rw [h1]
  rw [hG1, hnormsin] at hnorm
  have hL : ‖Complex.Gamma w‖ * (‖Complex.Gamma w‖ / |v|) = ‖Complex.Gamma w‖^2 / |v| := by ring
  rw [hL] at hnorm
  rw [div_eq_iff hvn] at hnorm
  rw [hnorm, div_mul_eq_mul_div]

private lemma Gamma_ratio_zero_lower (v : ℝ) (hv : v ≠ 0) :
    Real.sqrt (max (1/Real.pi) |v|) ≤
      ‖Complex.Gamma (1 + (v:ℂ)*I) / Complex.Gamma (1/2 + (v:ℂ)*I)‖ := by
  have ha : 0 < |v| := abs_pos.mpr hv
  have htpos : 0 < Real.tanh (Real.pi * |v|) := tanh_pos_of_pos (by positivity)
  have hr : ‖Complex.Gamma (1 + (v:ℂ)*I) / Complex.Gamma (1/2 + (v:ℂ)*I)‖^2 =
      |v| / Real.tanh (Real.pi * |v|) := by
    rw [norm_div, div_pow, Gamma_one_norm_sq v hv, gamma_abs_sq_half']
    rw [Real.tanh_eq_sinh_div_cosh]
    have hc : (0:ℝ) < Real.cosh (Real.pi * v) := Real.cosh_pos _
    have hcn : Real.cosh (Real.pi*|v|) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    have hs : Real.sinh (Real.pi*|v|) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
    rw [cosh_pi_abs v]
    field_simp
  have hle : max (1/Real.pi) |v| ≤ |v| / Real.tanh (Real.pi * |v|) := by
    apply max_le
    · rw [le_div_iff₀ htpos]
      have h1 : Real.tanh (Real.pi*|v|) ≤ Real.pi*|v| := tanh_le_self _ (by positivity)
      have h2 : (1/Real.pi) * Real.tanh (Real.pi*|v|) ≤ (1/Real.pi)*(Real.pi*|v|) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : (1/Real.pi)*(Real.pi*|v|) = |v| := by field_simp
      linarith [h2, h3]
    · rw [le_div_iff₀ htpos]
      have h4 := Real.tanh_lt_one (Real.pi*|v|)
      nlinarith [h4, ha]
  rw [← Real.sqrt_sq (norm_nonneg _), hr]
  apply Real.sqrt_le_sqrt
  exact hle


/-! ### Bounds for `log (s+2) + log N` in the strip -/

private lemma log_re_lower {s : ℂ} (hre0 : 0 ≤ s.re) :
    Real.log (2 + |s.im|) / 2 ≤ (Complex.log (s + 2)).re := by
  have hsq : ‖s + 2‖^2 = (s+2).re^2 + (s+2).im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hre : (s+2).re = s.re + 2 := by simp
  have him : (s+2).im = s.im := by simp
  have hge : (2 + |s.im| : ℝ) ≤ ‖s + 2‖^2 := by
    rw [hsq, hre, him]
    have h1 : (4:ℝ) ≤ (s.re + 2)^2 := by nlinarith [hre0]
    have h2 : |s.im| ≤ s.im^2 + 1 := by nlinarith [abs_nonneg s.im, sq_abs s.im, sq_nonneg (|s.im| - 1/2)]
    linarith
  have hle : Real.sqrt (2 + |s.im|) ≤ ‖s + 2‖ := by
    calc Real.sqrt (2 + |s.im|) ≤ Real.sqrt (‖s + 2‖^2) := Real.sqrt_le_sqrt hge
      _ = ‖s + 2‖ := Real.sqrt_sq (norm_nonneg _)
  have hpos : 0 < Real.sqrt (2 + |s.im|) := Real.sqrt_pos.mpr (by linarith [abs_nonneg s.im])
  have hl := Real.log_le_log hpos hle
  rw [Real.log_sqrt (by linarith [abs_nonneg s.im])] at hl
  rwa [Complex.log_re]

private lemma clog_shift_lower {N : ℕ} [NeZero N] {s : ℂ} (hre0 : 0 ≤ s.re) :
    Real.log (2 + |s.im|) / 2 ≤ ‖Complex.log (s + 2) + (Real.log N : ℂ)‖ := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have h := log_re_lower hre0
  have hre : Real.log (2 + |s.im|) / 2 ≤ (Complex.log (s + 2) + (Real.log N : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re]; linarith
  exact hre.trans (Complex.re_le_norm _)

private lemma clog_shift_upper {N : ℕ} [NeZero N] {s : ℂ} (hre0 : 0 ≤ s.re) (hre1 : s.re ≤ 1) :
    ‖Complex.log (s + 2) + (Real.log N : ℂ)‖ ≤ Real.log ((N:ℝ) * (2 + |s.im|)) + 5 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have h := (clog_bounds hre0 hre1).2
  have hb : (0:ℝ) < 2 + |s.im| := by positivity
  have hlog : Real.log ((N:ℝ) * (2 + |s.im|)) = Real.log N + Real.log (2 + |s.im|) :=
    Real.log_mul (ne_of_gt hNpos) (ne_of_gt hb)
  calc ‖Complex.log (s + 2) + (Real.log N : ℂ)‖
      ≤ ‖Complex.log (s + 2)‖ + ‖(Real.log N : ℂ)‖ := norm_add_le _ _
    _ = ‖Complex.log (s + 2)‖ + Real.log N := by
        rw [show ‖((Real.log N : ℝ):ℂ)‖ = |Real.log N| from RCLike.norm_ofReal _,
          abs_of_nonneg (Real.log_nonneg hN1)]
    _ ≤ (Real.log (2 + |s.im|) + 5) + Real.log N := by linarith
    _ = Real.log ((N:ℝ) * (2 + |s.im|)) + 5 := by rw [hlog]; ring

private lemma clog_shift_lower_zero {N : ℕ} [NeZero N] (t : ℝ) :
    (Real.log (N:ℝ) + Real.log (2 + |t|)) / 2 ≤
      ‖Complex.log (((t:ℂ)*I) + 2) + (Real.log N : ℂ)‖ := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have h := log_re_lower (s := ((t:ℂ)*I)) (by simp)
  have hh : ((t:ℂ)*I).im = t := by simp
  rw [hh] at h
  have hre : (Real.log (N:ℝ) + Real.log (2 + |t|)) / 2 ≤
      (Complex.log (((t:ℂ)*I) + 2) + (Real.log N : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re]; linarith
  exact hre.trans (Complex.re_le_norm _)

private lemma clog_shift_lower_one {N : ℕ} [NeZero N] (t : ℝ) :
    (Real.log (N:ℝ) + Real.log (2 + |t|)) / 2 ≤
      ‖Complex.log ((1:ℂ) + (t:ℂ)*I + 2) + (Real.log N : ℂ)‖ := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have h := log_re_lower (s := ((1:ℂ) + (t:ℂ)*I)) (by simp)
  have hh : ((1:ℂ) + (t:ℂ)*I).im = t := by simp
  rw [hh] at h
  have hre : (Real.log (N:ℝ) + Real.log (2 + |t|)) / 2 ≤
      (Complex.log ((1:ℂ) + (t:ℂ)*I + 2) + (Real.log N : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re]; linarith
  exact hre.trans (Complex.re_le_norm _)

private noncomputable def Wf (N : ℕ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ ((1 - s) / 2) * (Complex.Gamma (1 - s / 4) / Complex.Gamma (1 / 2 + s / 4)) *
    (Complex.log (s + 2) + (Real.log N : ℂ))

private lemma Wf_norm_upper {N : ℕ} [NeZero N] (s : ℂ) (hre0 : 0 ≤ s.re) (hre1 : s.re ≤ 1) :
    ‖Wf N s‖ ≤ 5 * Real.exp 1 * ((N:ℝ) * (2 + |s.im|)) ^ ((1 - s.re)/2) *
      (Real.log ((N:ℝ) * (2 + |s.im|)) + 2) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hcpow : ‖(N:ℂ) ^ ((1-s)/2)‖ = (N:ℝ)^((1-s.re)/2) := by
    rw [← Complex.ofReal_natCast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    congr 1
    simp [Complex.sub_re]
  set b : ℝ := 2 + |s.im| with hb
  have hbpos : 0 < b := by rw [hb]; positivity
  have hb1 : 1 ≤ b := by rw [hb]; linarith [abs_nonneg s.im]
  set a : ℝ := 1/2 - s.re/2 with ha
  have hratio : ‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ ≤
      Real.exp (a * (Real.log b + 2)) := by
    rw [ha, hb]; exact Gamma_ratio_decay s hre0 hre1
  have hlogb : ‖Complex.log (s + 2) + (Real.log N : ℂ)‖ ≤ Real.log ((N:ℝ) * b) + 5 := by
    rw [hb]; exact clog_shift_upper hre0 hre1
  have hexp : Real.exp (a * (Real.log b + 2)) = b ^ a * Real.exp (2*a) := by
    rw [mul_add, Real.exp_add, Real.rpow_def_of_pos hbpos]; ring_nf
  have hexp2 : Real.exp (2*a) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr; rw [ha]; linarith
  have hab : a = (1 - s.re)/2 := by rw [ha]; ring
  have hL0 : 0 ≤ Real.log ((N:ℝ)*b) + 5 := by
    have h1 : (1:ℝ) ≤ (N:ℝ)*b := by nlinarith [hN1, hb1]
    have := Real.log_nonneg h1
    linarith
  have stepA : ‖Wf N s‖ = (N:ℝ)^((1-s.re)/2) *
      (‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ *
        ‖Complex.log (s + 2) + (Real.log N : ℂ)‖) := by
    rw [Wf, norm_mul, norm_mul, hcpow]; ring
  have stepB : (N:ℝ)^((1-s.re)/2) *
      (‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ *
        ‖Complex.log (s + 2) + (Real.log N : ℂ)‖)
      ≤ (N:ℝ)^((1-s.re)/2) * (Real.exp (a * (Real.log b + 2)) * (Real.log ((N:ℝ)*b) + 5)) := by
    gcongr
  have stepC : (N:ℝ)^((1-s.re)/2) * (Real.exp (a * (Real.log b + 2)) * (Real.log ((N:ℝ)*b) + 5))
      ≤ (N:ℝ)^((1-s.re)/2) * (b^a * Real.exp 1) * (Real.log ((N:ℝ)*b) + 5) := by
    rw [hexp]
    have h1 : Real.exp (2*a) ≤ Real.exp 1 := hexp2
    have h2 : 0 ≤ b^a := Real.rpow_nonneg hbpos.le a
    have h3 : 0 ≤ (N:ℝ)^((1-s.re)/2) := Real.rpow_nonneg hNpos.le _
    have he1 : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith [h1, h2, h3, he1, hL0,
      mul_le_mul_of_nonneg_left h1 (mul_nonneg h3 h2)]
  have stepD : (N:ℝ)^((1-s.re)/2) * (b^a * Real.exp 1) * (Real.log ((N:ℝ)*b) + 5)
      = Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log ((N:ℝ)*b) + 5) := by
    rw [Real.mul_rpow hNpos.le hbpos.le, hab]; ring
  have hkey : Real.log ((N:ℝ)*b) + 5 ≤ 5 * (Real.log ((N:ℝ)*b) + 2) := by
    have h1 : (1:ℝ) ≤ (N:ℝ)*b := by nlinarith [hN1, hb1]
    have h0 : 0 ≤ Real.log ((N:ℝ)*b) := Real.log_nonneg h1
    linarith
  have stepE : Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log ((N:ℝ)*b) + 5)
      ≤ 5 * Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log ((N:ℝ)*b) + 2) := by
    have hpow0 : 0 ≤ Real.exp 1 * ((N:ℝ)*b)^((1-s.re)/2) := by
      exact mul_nonneg (Real.exp_pos 1).le (Real.rpow_nonneg (by positivity) _)
    calc Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log ((N:ℝ)*b) + 5)
        ≤ Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (5 * (Real.log ((N:ℝ)*b) + 2)) :=
          mul_le_mul_of_nonneg_left hkey hpow0
      _ = 5 * Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log ((N:ℝ)*b) + 2) := by ring
  calc ‖Wf N s‖ = (N:ℝ)^((1-s.re)/2) *
        (‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ *
          ‖Complex.log (s + 2) + (Real.log N : ℂ)‖) := stepA
    _ ≤ (N:ℝ)^((1-s.re)/2) * (Real.exp (a * (Real.log b + 2)) * (Real.log ((N:ℝ)*b) + 5)) := stepB
    _ ≤ (N:ℝ)^((1-s.re)/2) * (b^a * Real.exp 1) * (Real.log ((N:ℝ)*b) + 5) := stepC
    _ = Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log ((N:ℝ)*b) + 5) := stepD
    _ ≤ 5 * Real.exp 1 * ((N:ℝ) * b)^((1-s.re)/2) * (Real.log ((N:ℝ)*b) + 2) := stepE
    _ = 5 * Real.exp 1 * ((N:ℝ) * (2 + |s.im|)) ^ ((1 - s.re)/2) *
          (Real.log ((N:ℝ) * (2 + |s.im|)) + 2) := by rw [hb]
private lemma Gamma_ne_zero_of_re_pos' {z : ℂ} (hz : 0 < z.re) : Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero; intro m hm
  have hre := congrArg Complex.re hm
  simp at hre
  have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  linarith


private lemma two_le_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    2 ≤ N := by
  rcases Nat.lt_or_ge N 2 with h | h
  · have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hN1 : N = 1 := by omega
    subst hN1
    exact absurd (Subsingleton.elim χ 1) hχ
  · exact h

private lemma Wf_differentiableAt {N : ℕ} [NeZero N] (s : ℂ) (hlo : -2 < s.re) (hhi : s.re < 4) :
    DifferentiableAt ℂ (Wf N) s := by
  have hNnz : (N:ℂ) ≠ 0 := by
    have h := NeZero.ne N; exact_mod_cast h
  unfold Wf
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
  · exact DifferentiableAt.const_cpow (f := fun s : ℂ => (1 - s)/2) (by fun_prop) (Or.inl hNnz)
  · refine DifferentiableAt.div ?_ ?_ ?_
    · have hcomp : DifferentiableAt ℂ (fun s : ℂ => 1 - s/4) s := by fun_prop
      refine (Complex.differentiableAt_Gamma (1 - s/4) ?_).comp s hcomp
      intro m hm
      have hre := congrArg Complex.re hm
      rw [Complex.sub_re, Complex.div_re] at hre
      simp at hre
      have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    · have hcomp : DifferentiableAt ℂ (fun s : ℂ => 1/2 + s/4) s := by fun_prop
      refine (Complex.differentiableAt_Gamma (1/2 + s/4) ?_).comp s hcomp
      intro m hm
      have hre := congrArg Complex.re hm
      rw [Complex.add_re, Complex.div_re] at hre
      simp at hre
      have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    · apply Gamma_ne_zero_of_re_pos'
      rw [Complex.add_re, Complex.div_re]; simp; linarith
  · have hmem : s + 2 ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      rw [Complex.add_re]; simp; linarith
    exact ((differentiableAt_log hmem).comp s
      (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => t + 2) s)).add
      (differentiableAt_const ((Real.log N : ℝ) : ℂ))

private lemma Wf_ne_zero_strip {N : ℕ} [NeZero N] (s : ℂ) (hlo : 0 ≤ s.re) (hhi : s.re ≤ 1) :
    Wf N s ≠ 0 := by
  have hNnz : (N:ℂ) ≠ 0 := by
    have h := NeZero.ne N; exact_mod_cast h
  have hcpow : (N:ℂ)^((1-s)/2) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; exact Or.inl hNnz
  have hG1 : Complex.Gamma (1 - s/4) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos'
    rw [Complex.sub_re, Complex.div_re]; simp; linarith
  have hG2 : Complex.Gamma (1/2 + s/4) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos'
    rw [Complex.add_re, Complex.div_re]; simp; linarith
  have hlog : Complex.log (s+2) + (Real.log N : ℂ) ≠ 0 := by
    intro h
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
    have hre := congrArg Complex.re h
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re] at hre
    simp at hre
    have h2 : 2 ≤ ‖s + 2‖ := by
      have h3 := Complex.re_le_norm (s + 2)
      rw [Complex.add_re] at h3; simp at h3; linarith
    have h1 : 0 < Real.log ‖s + 2‖ := Real.log_pos (by linarith)
    have h4 : 0 ≤ Real.log N := Real.log_nonneg hN1
    linarith
  rw [Wf]
  exact mul_ne_zero (mul_ne_zero hcpow (div_ne_zero hG1 hG2)) hlog

private lemma F_differentiableOn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (fun s : ℂ => LFunction χ s / Wf N s) (re ⁻¹' Set.Ioo 0 1) := by
  intro s hs
  rw [Set.mem_preimage, Set.mem_Ioo] at hs
  exact ((differentiable_LFunction hχ s).differentiableWithinAt).div
    ((Wf_differentiableAt s (by linarith [hs.1]) (by linarith [hs.2])).differentiableWithinAt)
    (Wf_ne_zero_strip s (le_of_lt hs.1) (le_of_lt hs.2))

private lemma F_continuousOn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ContinuousOn (fun s : ℂ => LFunction χ s / Wf N s) (re ⁻¹' Set.Icc 0 1) := by
  intro s hs
  rw [Set.mem_preimage, Set.mem_Icc] at hs
  exact (ContinuousAt.continuousWithinAt (((differentiable_LFunction hχ s).continuousAt).div
    ((Wf_differentiableAt s (by linarith [hs.1]) (by linarith [hs.2])).continuousAt)
    (Wf_ne_zero_strip s hs.1 hs.2)))

private lemma Gamma_mul_I_norm_sq (y : ℝ) (hy : y ≠ 0) :
    ‖Complex.Gamma (((y:ℝ):ℂ) * I)‖^2 = Real.pi / (|y| * Real.sinh (Real.pi * |y|)) := by
  have h1 := Gamma_one_norm_sq y hy
  have hadd : Complex.Gamma (1 + ((y:ℝ):ℂ)*I) =
      (((y:ℝ):ℂ)*I) * Complex.Gamma (((y:ℝ):ℂ)*I) := by
    have hne : (((y:ℝ):ℂ)*I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Complex.I_ne_zero, or_false]
      exact_mod_cast hy
    rw [show (1:ℂ) + ((y:ℝ):ℂ)*I = (((y:ℝ):ℂ)*I) + 1 from by ring]
    exact Complex.Gamma_add_one _ hne
  have hnorm : ‖Complex.Gamma (1 + ((y:ℝ):ℂ)*I)‖ = |y| * ‖Complex.Gamma (((y:ℝ):ℂ)*I)‖ := by
    rw [hadd, norm_mul, norm_mul, Complex.norm_I, mul_one,
        show ‖((y:ℝ):ℂ)‖ = |y| from RCLike.norm_ofReal _]
  rw [hnorm, mul_pow, sq_abs y] at h1
  have hypos : 0 < |y| := abs_pos.mpr hy
  have hsinhpos : 0 < Real.sinh (Real.pi * |y|) := Real.sinh_pos_iff.mpr (by positivity)
  have hsinhne : Real.sinh (Real.pi * |y|) ≠ 0 := ne_of_gt hsinhpos
  rw [eq_div_iff hsinhne] at h1
  rw [show y^2 = |y|^2 from (sq_abs y).symm] at h1
  rw [eq_div_iff (by positivity : |y| * Real.sinh (Real.pi*|y|) ≠ 0)]
  nlinarith [h1]

private lemma GammaR_ratio_one_sub_le {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gammaℝ (1 - (t:ℂ)*I) / Complex.Gammaℝ ((t:ℂ)*I)‖ ≤
      (2 + |t|)^((1:ℝ)/2) / Real.sqrt (2*Real.pi) := by
  have ht2 : t/2 ≠ 0 := by intro h; exact ht (by linarith [h])
  have hnum : ‖Complex.Gammaℝ (1 - (t:ℂ)*I)‖ =
      (Real.pi:ℝ)^(-(1/2:ℝ)) * ‖Complex.Gamma ((1/2:ℂ) - (((t/2):ℝ):ℂ)*I)‖ := by
    have h := Commons.Analysis.SpecialFunctions.Gamma.norm_gammaR_vertical_eq 1 (-t)
    have e1 : (((1:ℝ):ℂ) + I*((-t:ℝ):ℂ)) = (1 - (t:ℂ)*I) := by push_cast; ring
    have e2 : ((((1:ℝ)/2:ℝ):ℂ) + I*((((-t)/2:ℝ):ℂ))) = ((1/2:ℂ) - (((t/2):ℝ):ℂ)*I) := by
      push_cast; ring
    rw [e1, e2] at h
    exact h
  have hden : ‖Complex.Gammaℝ ((t:ℂ)*I)‖ = ‖Complex.Gamma ((((t/2):ℝ):ℂ)*I)‖ := by
    have h := Commons.Analysis.SpecialFunctions.Gamma.norm_gammaR_vertical_eq 0 t
    have e1 : (((0:ℝ):ℂ) + I*((t:ℝ):ℂ)) = ((t:ℂ)*I) := by push_cast; ring
    have e2 : ((((0:ℝ)/2:ℝ):ℂ) + I*(((t/2:ℝ):ℂ))) = ((((t/2):ℝ):ℂ)*I) := by push_cast; ring
    have he : (Real.pi:ℝ)^(-((0:ℝ)/2)) = 1 := by
      rw [show -((0:ℝ)/2) = 0 by norm_num, Real.rpow_zero]
    rw [e1, e2, he, one_mul] at h
    exact h
  have hnum2 : ‖Complex.Gamma ((1/2:ℂ) - (((t/2):ℝ):ℂ)*I)‖^2 =
      Real.pi / Real.cosh (Real.pi * (t/2)) := by
    have h := gamma_abs_sq_half' (-(t/2))
    rw [show Real.pi * (-(t/2)) = -(Real.pi*(t/2)) by ring, Real.cosh_neg] at h
    have harg : ((1/2:ℂ) + (((-(t/2)):ℝ):ℂ)*I) = (1/2:ℂ) - (((t/2):ℝ):ℂ)*I := by push_cast; ring
    rwa [harg] at h
  have hden2 : ‖Complex.Gamma ((((t/2):ℝ):ℂ)*I)‖^2 =
      Real.pi / (|t/2| * Real.sinh (Real.pi * |t/2|)) := Gamma_mul_I_norm_sq (t/2) ht2
  have hratio_sq : ‖Complex.Gammaℝ (1 - (t:ℂ)*I) / Complex.Gammaℝ ((t:ℂ)*I)‖^2 ≤
      (2 + |t|)/(2*Real.pi) := by
    rw [norm_div, hnum, hden, div_pow, mul_pow, hnum2, hden2]
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    have hcosh_eq : Real.cosh (Real.pi * (t/2)) = Real.cosh (Real.pi * |t/2|) := by
      rw [show Real.pi * |t/2| = |Real.pi * (t/2)| from by rw [abs_mul, abs_of_pos hpi]]
      exact (Real.cosh_abs _).symm
    rw [hcosh_eq]
    have hpi1 : ((Real.pi:ℝ)^(-(1/2:ℝ)))^2 = 1/Real.pi := by
      rw [sq, ← Real.rpow_add hpi]
      rw [show (-(1/2:ℝ)) + (-(1/2)) = -1 by ring, Real.rpow_neg_one, inv_eq_one_div]
    rw [hpi1]
    have hcoshp : 0 < Real.cosh (Real.pi*|t/2|) := Real.cosh_pos _
    have hsinhp : 0 < Real.sinh (Real.pi*|t/2|) := Real.sinh_pos_iff.mpr (by positivity)
    have hsinhle : Real.sinh (Real.pi*|t/2|) ≤ Real.cosh (Real.pi*|t/2|) := by
      rw [Real.sinh_eq, Real.cosh_eq]
      linarith [Real.exp_pos (-(Real.pi*|t/2|))]
    have habs2 : |t/2| = |t|/2 := by rw [abs_div]; norm_num
    have hsinhle' : Real.sinh (Real.pi*(|t|/2)) ≤ Real.cosh (Real.pi*(|t|/2)) := by
      rw [← habs2]; exact hsinhle
    have heq : (1/Real.pi) * (Real.pi/Real.cosh (Real.pi*|t/2|)) /
        (Real.pi/(|t/2| * Real.sinh (Real.pi*|t/2|)))
        = |t/2| * Real.sinh (Real.pi*|t/2|) / (Real.pi * Real.cosh (Real.pi*|t/2|)) := by
      field_simp
    rw [heq, habs2]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < Real.pi * Real.cosh (Real.pi*(|t|/2)))
      (by positivity : (0:ℝ) < 2*Real.pi)]
    have h1 : |t| / 2 * Real.sinh (Real.pi*(|t|/2)) * (2*Real.pi) ≤
        |t| / 2 * Real.cosh (Real.pi*(|t|/2)) * (2*Real.pi) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsinhle' (by positivity)
    have h2 : |t| / 2 * Real.cosh (Real.pi*(|t|/2)) * (2*Real.pi) ≤
        (2 + |t|) * (Real.pi * Real.cosh (Real.pi*(|t|/2))) :=
      by nlinarith [abs_nonneg t, Real.cosh_pos (Real.pi*(|t|/2)), Real.pi_pos]
    linarith [h1, h2]
  have hnonneg : 0 ≤ ‖Complex.Gammaℝ (1 - (t:ℂ)*I) / Complex.Gammaℝ ((t:ℂ)*I)‖ := norm_nonneg _
  calc ‖Complex.Gammaℝ (1 - (t:ℂ)*I) / Complex.Gammaℝ ((t:ℂ)*I)‖
      = Real.sqrt (‖Complex.Gammaℝ (1 - (t:ℂ)*I) / Complex.Gammaℝ ((t:ℂ)*I)‖^2) :=
        (Real.sqrt_sq hnonneg).symm
    _ ≤ Real.sqrt ((2 + |t|)/(2*Real.pi)) := Real.sqrt_le_sqrt hratio_sq
    _ = (2 + |t|)^((1:ℝ)/2) / Real.sqrt (2*Real.pi) := by
        rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 + |t|), Real.sqrt_eq_rpow]

private lemma Gamma_one_sub_mul_I_norm (u : ℝ) (hu : u ≠ 0) :
    ‖Complex.Gamma (1 - (u:ℂ)*I)‖ = |u| * ‖Complex.Gamma ((u:ℂ)*I)‖ := by
  have hconj : Complex.Gamma (1 - (u:ℂ)*I) = star (Complex.Gamma (1 + (u:ℂ)*I)) := by
    rw [← Gamma_star]
    congr 1
    apply Complex.ext <;> simp
  rw [hconj, norm_star]
  have hadd : Complex.Gamma (1 + (u:ℂ)*I) = ((u:ℂ)*I) * Complex.Gamma ((u:ℂ)*I) := by
    rw [show (1:ℂ) + (u:ℂ)*I = ((u:ℂ)*I) + 1 from by ring]
    exact Complex.Gamma_add_one _ (by
      simp only [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Complex.I_ne_zero, or_false]
      exact_mod_cast hu)
  rw [hadd, norm_mul, norm_mul, Complex.norm_I, mul_one,
      show ‖((u:ℝ):ℂ)‖ = |u| from RCLike.norm_ofReal _]

private lemma GammaR_ratio_two_sub_le {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gammaℝ (2 - (t:ℂ)*I) / Complex.Gammaℝ (1 + (t:ℂ)*I)‖ ≤
      (2 + |t|)^((1:ℝ)/2) / Real.sqrt (2*Real.pi) := by
  have ht2 : t/2 ≠ 0 := by intro h; exact ht (by linarith [h])
  have hnum : ‖Complex.Gammaℝ (2 - (t:ℂ)*I)‖ =
      (Real.pi:ℝ)^(-(1:ℝ)) * (|t/2| * ‖Complex.Gamma ((((t/2):ℝ):ℂ)*I)‖) := by
    have h := Commons.Analysis.SpecialFunctions.Gamma.norm_gammaR_vertical_eq 2 (-t)
    have e1 : (((2:ℝ):ℂ) + I*((-t:ℝ):ℂ)) = (2 - (t:ℂ)*I) := by push_cast; ring
    have e2 : ((((2:ℝ)/2:ℝ):ℂ) + I*((((-t)/2:ℝ):ℂ))) = (1 - (((t/2):ℝ):ℂ)*I) := by
      push_cast; ring
    rw [e1, e2] at h
    have he : (Real.pi:ℝ)^(-((2:ℝ)/2)) = (Real.pi:ℝ)^(-(1:ℝ)) := by norm_num
    rw [he] at h
    rw [h, Gamma_one_sub_mul_I_norm (t/2) ht2]
  have hden : ‖Complex.Gammaℝ (1 + (t:ℂ)*I)‖ =
      (Real.pi:ℝ)^(-(1/2:ℝ)) * ‖Complex.Gamma ((1/2:ℂ) + (((t/2):ℝ):ℂ)*I)‖ := by
    have h := Commons.Analysis.SpecialFunctions.Gamma.norm_gammaR_vertical_eq 1 t
    have e1 : (((1:ℝ):ℂ) + I*((t:ℝ):ℂ)) = (1 + (t:ℂ)*I) := by push_cast; ring
    have e2 : ((((1:ℝ)/2:ℝ):ℂ) + I*(((t/2:ℝ):ℂ))) = ((1/2:ℂ) + (((t/2):ℝ):ℂ)*I) := by
      push_cast; ring
    rw [e1, e2] at h
    exact h
  have hnum2 : ‖Complex.Gamma ((((t/2):ℝ):ℂ)*I)‖^2 =
      Real.pi / (|t/2| * Real.sinh (Real.pi * |t/2|)) := Gamma_mul_I_norm_sq (t/2) ht2
  have hden2 : ‖Complex.Gamma ((1/2:ℂ) + (((t/2):ℝ):ℂ)*I)‖^2 =
      Real.pi / Real.cosh (Real.pi * (t/2)) := by
    have h := gamma_abs_sq_half' (t/2)
    rw [show ((1/2:ℂ) + (((t/2):ℝ):ℂ)*I) = ((1/2:ℂ) + (((t/2):ℝ):ℂ)*I) from rfl] at h
    exact h
  have hratio_sq : ‖Complex.Gammaℝ (2 - (t:ℂ)*I) / Complex.Gammaℝ (1 + (t:ℂ)*I)‖^2 ≤
      (2 + |t|)/(2*Real.pi) := by
    rw [norm_div, hnum, hden, div_pow, mul_pow, mul_pow, mul_pow, hnum2, hden2]
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    have hcosh_eq : Real.cosh (Real.pi * (t/2)) = Real.cosh (Real.pi * |t/2|) := by
      rw [show Real.pi * |t/2| = |Real.pi * (t/2)| from by rw [abs_mul, abs_of_pos hpi]]
      exact (Real.cosh_abs _).symm
    rw [hcosh_eq]
    have hpi1 : ((Real.pi:ℝ)^(-(1:ℝ)))^2 = 1/Real.pi^2 := by
      rw [sq, ← Real.rpow_add hpi]
      rw [show (-(1:ℝ)) + (-(1:ℝ)) = -2 by ring, Real.rpow_neg (le_of_lt hpi), Real.rpow_two,
          inv_eq_one_div, sq]
    have hpi2 : ((Real.pi:ℝ)^(-(1/2:ℝ)))^2 = 1/Real.pi := by
      rw [sq, ← Real.rpow_add hpi]
      rw [show (-(1/2:ℝ)) + (-(1/2)) = -1 by ring, Real.rpow_neg_one, inv_eq_one_div]
    rw [hpi1, hpi2]
    have hcosp : 0 < Real.cosh (Real.pi*|t/2|) := Real.cosh_pos _
    have hsinhp : 0 < Real.sinh (Real.pi*|t/2|) := Real.sinh_pos_iff.mpr (by positivity)
    have htp : 0 < |t/2| := abs_pos.mpr ht2
    have habs2 : |t/2| = |t|/2 := by rw [abs_div]; norm_num
    have hle : |t| * Real.cosh (Real.pi*|t/2|) ≤ (2 + |t|) * Real.sinh (Real.pi*|t/2|) := by
      have hcosh_le : Real.cosh (Real.pi*|t/2|) ≤ Real.sinh (Real.pi*|t/2|) + 1 := by
        have hexp : Real.exp (-(Real.pi*|t/2|)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (t/2), Real.pi_pos])
        rw [Real.cosh_eq, Real.sinh_eq]
        linarith [hexp]
      have hsinh_ge : Real.pi * |t/2| ≤ Real.sinh (Real.pi*|t/2|) :=
        Real.self_le_sinh_iff.mpr (by positivity)
      have h2sinh : |t| ≤ 2 * Real.sinh (Real.pi*|t/2|) := by
        nlinarith [hsinh_ge, abs_nonneg t, Real.pi_gt_three]
      nlinarith [hcosh_le, h2sinh, hsinhp, abs_nonneg t]
    have heq : (1/Real.pi^2) * (|t/2|^2 * (Real.pi/(|t/2| * Real.sinh (Real.pi*|t/2|)))) /
        (1/Real.pi * (Real.pi/Real.cosh (Real.pi*|t/2|)))
        = |t/2| * Real.cosh (Real.pi*|t/2|) / (Real.pi * Real.sinh (Real.pi*|t/2|)) := by
      field_simp
    rw [heq, habs2]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < Real.pi * Real.sinh (Real.pi*(|t|/2)))
      (by positivity : (0:ℝ) < 2*Real.pi)]
    have hle' : |t| * Real.cosh (Real.pi*(|t|/2)) ≤ (2 + |t|) * Real.sinh (Real.pi*(|t|/2)) := by
      rw [← habs2]; exact hle
    nlinarith [hle', Real.sinh_pos_iff.mpr (by positivity : (0:ℝ) < Real.pi*(|t|/2)),
      Real.pi_pos, abs_nonneg t]
  have hnonneg : 0 ≤ ‖Complex.Gammaℝ (2 - (t:ℂ)*I) / Complex.Gammaℝ (1 + (t:ℂ)*I)‖ := norm_nonneg _
  calc ‖Complex.Gammaℝ (2 - (t:ℂ)*I) / Complex.Gammaℝ (1 + (t:ℂ)*I)‖
      = Real.sqrt (‖Complex.Gammaℝ (2 - (t:ℂ)*I) / Complex.Gammaℝ (1 + (t:ℂ)*I)‖^2) :=
        (Real.sqrt_sq hnonneg).symm
    _ ≤ Real.sqrt ((2 + |t|)/(2*Real.pi)) := Real.sqrt_le_sqrt hratio_sq
    _ = (2 + |t|)^((1:ℝ)/2) / Real.sqrt (2*Real.pi) := by
        rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 + |t|), Real.sqrt_eq_rpow]
private lemma gammaFactor_ne_zero_of_im_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s.im ≠ 0) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [DirichletCharacter.Even.gammaFactor_def h, Complex.Gammaℝ_def]
    refine mul_ne_zero ?_ ?_
    · rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (by exact_mod_cast (ne_of_gt Real.pi_pos) : (Real.pi : ℂ) ≠ 0)
    · apply Complex.Gamma_ne_zero; intro m hm
      apply hs
      have := congrArg (fun z => z * 2) hm
      simp at this
      have := congrArg Complex.im this
      simpa using this
  · rw [DirichletCharacter.Odd.gammaFactor_def h, Complex.Gammaℝ_def]
    refine mul_ne_zero ?_ ?_
    · rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (by exact_mod_cast (ne_of_gt Real.pi_pos) : (Real.pi : ℂ) ≠ 0)
    · apply Complex.Gamma_ne_zero; intro m hm
      apply hs
      have := congrArg (fun z => z * 2) hm
      simp at this
      have := congrArg Complex.im this
      simp at this; linarith

private lemma Gamma_ratio_zero_lower' (t : ℝ) (ht : t ≠ 0) :
    Real.sqrt (max (1/Real.pi) (|t|/4)) ≤
      ‖Complex.Gamma (1 + (t:ℂ)/4*I) / Complex.Gamma ((1/2:ℂ) + (t:ℂ)/4*I)‖ := by
  have h := Gamma_ratio_zero_lower (t/4) (by positivity)
  rw [show |t/4| = |t|/4 from by rw [abs_div]; norm_num] at h
  have e : (t:ℂ)/4 = (((t/4:ℝ)):ℂ) := by push_cast; ring
  rw [e]
  exact h

private lemma sqrt_max_le (t : ℝ) : (2+|t|)^((1:ℝ)/2) ≤ 4 * Real.sqrt (max (1/Real.pi) (|t|/4)) := by
  have h1 : (2+|t|)^((1:ℝ)/2) ≤ Real.sqrt 3 * Real.sqrt (max 1 |t|) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), ← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_sqrt
    rcases lt_or_ge |t| 1 with h | h
    · rw [max_eq_left (le_of_lt h)]; nlinarith
    · rw [max_eq_right h]; nlinarith [abs_nonneg t]
  have h2 : Real.sqrt (max 1 |t|) ≤ 2 * Real.sqrt (max (1/Real.pi) (|t|/4)) := by
    have hp4 : (1:ℝ) ≤ 4/Real.pi := by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
    rcases lt_or_ge |t| (4/Real.pi) with h | h
    · have hmax1 : max 1 |t| ≤ 4/Real.pi := by
        rcases lt_or_ge |t| 1 with h1 | h1
        · rw [max_eq_left (le_of_lt h1)]; exact hp4
        · rw [max_eq_right h1]; exact le_of_lt h
      have hm : max (1/Real.pi) (|t|/4) = 1/Real.pi := by
        apply max_eq_left
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) Real.pi_pos]
        have := (lt_div_iff₀ Real.pi_pos).mp h
        linarith
      rw [hm, show (2:ℝ)*Real.sqrt (1/Real.pi) = Real.sqrt (4*(1/Real.pi)) from by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
            show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
      apply Real.sqrt_le_sqrt
      rwa [mul_one_div]
    · have hm : max (1/Real.pi) (|t|/4) = |t|/4 := by
        apply max_eq_right
        rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (0:ℝ) < 4)]
        have := (div_le_iff₀ Real.pi_pos).mp h
        linarith
      rw [hm, show (2:ℝ)*Real.sqrt (|t|/4) = Real.sqrt (4*(|t|/4)) from by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
            show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)],
        show 4*(|t|/4) = |t| by ring,
        max_eq_right (by linarith [h, hp4] : (1:ℝ) ≤ |t|)]
  have h3 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc (2+|t|)^((1:ℝ)/2) ≤ Real.sqrt 3 * Real.sqrt (max 1 |t|) := h1
    _ ≤ 2 * (2 * Real.sqrt (max (1/Real.pi) (|t|/4))) := by
        apply mul_le_mul h3 h2 (Real.sqrt_nonneg _) (by norm_num)
    _ = 4 * Real.sqrt (max (1/Real.pi) (|t|/4)) := by ring


private lemma gammaFactor_ratio_zero_sharp {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (t : ℝ) (ht : t ≠ 0) :
    ‖(χ⁻¹).gammaFactor (1 - (t:ℂ)*I) / χ.gammaFactor ((t:ℂ)*I)‖ ≤
      (2 + |t|)^((1:ℝ)/2) / Real.sqrt (2*Real.pi) := by
  rcases χ.even_or_odd with hχe | hχo
  · rw [DirichletCharacter.Even.gammaFactor_def hχe,
        DirichletCharacter.Even.gammaFactor_def
          (Commons.NumberTheory.DirichletCharacter.Even_inv hχe)]
    exact GammaR_ratio_one_sub_le ht
  · rw [DirichletCharacter.Odd.gammaFactor_def hχo,
        DirichletCharacter.Odd.gammaFactor_def
          (Commons.NumberTheory.DirichletCharacter.Odd_inv hχo)]
    rw [show (1:ℂ) - (t:ℂ)*I + 1 = 2 - (t:ℂ)*I from by ring,
        show (t:ℂ)*I + 1 = 1 + (t:ℂ)*I from by ring]
    exact GammaR_ratio_two_sub_le ht

private lemma LFunction_norm_zero_le_sharp {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (t : ℝ) (ht : t ≠ 0) :
    ‖LFunction χ ((t:ℂ)*I)‖ ≤ (1/Real.sqrt (2*Real.pi)) * (N:ℝ)^((1:ℝ)/2) *
      (2+|t|)^((1:ℝ)/2) * (Real.log N + Real.log (2+|t|) + 6) := by
  set s : ℂ := (t:ℂ)*I with hs
  have hsim : s.im = t := by rw [hs]; simp
  have hsre : s.re = 0 := by rw [hs]; simp
  have hsim' : s.im ≠ 0 := by rw [hsim]; exact ht
  have hs0 : s ≠ 0 := by
    intro h; apply hsim'; rw [h]; simp
  have h1s : 1 - s ≠ 0 := by
    intro h; apply hsim'; have := congrArg Complex.im h; simpa using this
  have hγχ : χ.gammaFactor s ≠ 0 := gammaFactor_ne_zero_of_im_ne_zero χ hsim'
  have hγχi : (χ⁻¹).gammaFactor (1 - s) ≠ 0 :=
    gammaFactor_ne_zero_of_im_ne_zero (χ⁻¹)
      (by rw [Complex.sub_im, Complex.one_im, hsim]; simp [ht])
  have hχine : χ⁻¹ ≠ 1 := by
    intro h; apply hχ
    have := congrArg (fun ψ : DirichletCharacter ℂ N => ψ⁻¹) h
    simpa using this
  have hL1 : LFunction χ s = completedLFunction χ s / χ.gammaFactor s :=
    LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  have hL2 : LFunction (χ⁻¹) (1 - s) =
      completedLFunction (χ⁻¹) (1 - s) / (χ⁻¹).gammaFactor (1 - s) :=
    LFunction_eq_completed_div_gammaFactor (χ⁻¹) (1 - s) (Or.inl h1s)
  have hcomp : completedLFunction (χ⁻¹) (1 - s) =
      LFunction (χ⁻¹) (1 - s) * (χ⁻¹).gammaFactor (1 - s) := by
    rw [hL2]; exact (div_mul_cancel₀ _ hγχi).symm
  have hFE := completedLFunction_eq χ hχprim s
  have hmain : LFunction χ s = (N:ℂ)^((1:ℂ)/2 - s) * χ.rootNumber *
      (LFunction (χ⁻¹) (1 - s) * (χ⁻¹).gammaFactor (1 - s)) / χ.gammaFactor s := by
    rw [hL1, hFE, hcomp]
  have hNpow : ‖(N:ℂ)^((1:ℂ)/2 - s)‖ = (N:ℝ)^((1:ℝ)/2) := by
    rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))]
    congr 1
    rw [Complex.sub_re, Complex.div_re]; simp [hs]
  have hroot := rootNumber_norm_eq_one χ hχprim
  have hnorm_eq : ‖LFunction χ s‖ = (N:ℝ)^((1:ℝ)/2) * ‖χ.rootNumber‖ *
      ‖LFunction (χ⁻¹) (1 - s)‖ * ‖(χ⁻¹).gammaFactor (1 - s)‖ / ‖χ.gammaFactor s‖ := by
    rw [hmain]
    simp only [norm_div, norm_mul]
    rw [hNpow]
    ring_nf
  have hL2b : ‖LFunction (χ⁻¹) (1 - s)‖ ≤ Real.log N + Real.log (2+|t|) + 6 := by
    have h := norm_LFunction_le_re_ge_one (χ⁻¹) hχine (1 - s)
      (by rw [Complex.sub_re, Complex.one_re, hsre]; norm_num)
    rwa [show (1 - s).im = -t from by rw [Complex.sub_im, Complex.one_im, hsim]; ring,
      abs_neg] at h
  have hγb : ‖(χ⁻¹).gammaFactor (1 - s)‖ / ‖χ.gammaFactor s‖ ≤
      (2+|t|)^((1:ℝ)/2) / Real.sqrt (2*Real.pi) := by
    rw [← norm_div]
    have := gammaFactor_ratio_zero_sharp χ t ht
    rwa [show (1 - (t:ℂ)*I) = 1 - s from by rw [hs]] at this
  rw [hnorm_eq]
  simp only [hroot, mul_one, one_mul]
  have hγpos : 0 < ‖χ.gammaFactor s‖ := norm_pos_iff.mpr hγχ
  rw [div_le_iff₀ hγpos]
  have hLnn : 0 ≤ Real.log N + Real.log (2+|t|) + 6 := by
    have h1 := Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)) : (1:ℝ) ≤ (N:ℝ))
    have h2 := Real.log_nonneg (by linarith [abs_nonneg t] : (1:ℝ) ≤ 2+|t|)
    linarith
  have hγb' : ‖(χ⁻¹).gammaFactor (1 - s)‖ ≤
      (2+|t|)^((1:ℝ)/2) / Real.sqrt (2*Real.pi) * ‖χ.gammaFactor s‖ := by
    rw [← div_le_iff₀ hγpos]; exact hγb
  calc (N:ℝ)^((1:ℝ)/2) * ‖LFunction (χ⁻¹) (1 - s)‖ * ‖(χ⁻¹).gammaFactor (1 - s)‖
      = (N:ℝ)^((1:ℝ)/2) * (‖LFunction (χ⁻¹) (1 - s)‖ * ‖(χ⁻¹).gammaFactor (1 - s)‖) := by ring
    _ ≤ (N:ℝ)^((1:ℝ)/2) * ((Real.log N + Real.log (2+|t|) + 6) *
          ((2+|t|)^((1:ℝ)/2) / Real.sqrt (2*Real.pi) * ‖χ.gammaFactor s‖)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
        exact mul_le_mul hL2b hγb' (norm_nonneg _) hLnn
    _ = ((1/Real.sqrt (2*Real.pi)) * (N:ℝ)^((1:ℝ)/2) * (2+|t|)^((1:ℝ)/2) *
          (Real.log N + Real.log (2+|t|) + 6)) * ‖χ.gammaFactor s‖ := by ring

private lemma Gamma_half_norm : ‖Complex.Gamma (1/2:ℂ)‖ = Real.sqrt Real.pi := by
  have h := gamma_abs_sq_half' 0
  have h2 : ‖Complex.Gamma (1/2:ℂ)‖^2 = Real.pi := by simpa using h
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

private lemma GammaR_one_norm : ‖Complex.Gammaℝ 1‖ = 1 := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      show (-(1:ℂ)/2).re = -(1/2) from by norm_num [Complex.div_re, Complex.neg_re],
      Gamma_half_norm,
      show (Real.pi:ℝ)^(-(1/2:ℝ)) = (Real.sqrt Real.pi)⁻¹ from by
        rw [Real.rpow_neg (le_of_lt Real.pi_pos), Real.sqrt_eq_rpow]]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))

private lemma GammaR_two_norm : ‖Complex.Gammaℝ 2‖ = 1/Real.pi := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      show (-(2:ℂ)/2).re = -(1:ℝ) from by norm_num [Complex.div_re, Complex.neg_re],
      show Complex.Gamma ((2:ℂ)/2) = 1 from by
        rw [show (2:ℂ)/2 = 1 from by norm_num, Complex.Gamma_one], norm_one, mul_one,
      show (Real.pi:ℝ)^(-(1:ℝ)) = 1/Real.pi from by rw [Real.rpow_neg_one, inv_eq_one_div]]

private lemma gammaFactor_one_norm_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ‖χ.gammaFactor 1‖ ≤ 1 := by
  rcases χ.even_or_odd with he | ho
  · rw [DirichletCharacter.Even.gammaFactor_def he, GammaR_one_norm]
  · rw [DirichletCharacter.Odd.gammaFactor_def ho]
    rw [show (1:ℂ) + 1 = 2 from by norm_num, GammaR_two_norm]
    rw [div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]

private lemma Wf_lower_zero {N : ℕ} [NeZero N] (t : ℝ) (ht : t ≠ 0) :
    (1/8) * (N:ℝ)^((1:ℝ)/2) * (2+|t|)^((1:ℝ)/2) * (Real.log N + Real.log (2+|t|)) ≤
      ‖Wf N ((t:ℂ)*I)‖ := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hnum : ‖(N:ℂ)^((1-(t:ℂ)*I)/2)‖ = (N:ℝ)^((1:ℝ)/2) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    congr 1
    rw [Complex.div_re, Complex.sub_re]; simp
  have hratio_eq : ‖Complex.Gamma (1 - ((t:ℂ)*I)/4) / Complex.Gamma (1/2 + ((t:ℂ)*I)/4)‖ =
      ‖Complex.Gamma (1 + (t:ℂ)/4*I) / Complex.Gamma (1/2 + (t:ℂ)/4*I)‖ := by
    have e1 : 1 - ((t:ℂ)*I)/4 = star (1 + (t:ℂ)/4*I) := by apply Complex.ext <;> simp
    have e2 : (1/2:ℂ) + ((t:ℂ)*I)/4 = (1/2:ℂ) + (t:ℂ)/4*I := by ring
    rw [e1, e2]; simp only [norm_div, Gamma_star, norm_star]
  have hG : (2+|t|)^((1:ℝ)/2)/4 ≤
      ‖Complex.Gamma (1 - ((t:ℂ)*I)/4) / Complex.Gamma (1/2 + ((t:ℂ)*I)/4)‖ := by
    rw [hratio_eq]
    have h1 := sqrt_max_le t
    have h2 := Gamma_ratio_zero_lower' t ht
    linarith
  have hh : (Real.log N + Real.log (2+|t|))/2 ≤
      ‖Complex.log ((t:ℂ)*I + 2) + (Real.log N : ℂ)‖ := clog_shift_lower_zero t
  have hWf : ‖Wf N ((t:ℂ)*I)‖ = (N:ℝ)^((1:ℝ)/2) *
      (‖Complex.Gamma (1 - ((t:ℂ)*I)/4) / Complex.Gamma (1/2 + ((t:ℂ)*I)/4)‖ *
        ‖Complex.log ((t:ℂ)*I + 2) + (Real.log N : ℂ)‖) := by
    rw [Wf, norm_mul, norm_mul, hnum]; ring
  have htop : 0 ≤ (Real.log N + Real.log (2+|t|))/2 := by
    apply div_nonneg _ (by norm_num)
    exact add_nonneg (Real.log_nonneg hN1) (Real.log_nonneg (by linarith [abs_nonneg t]))
  calc (1/8) * (N:ℝ)^((1:ℝ)/2) * (2+|t|)^((1:ℝ)/2) * (Real.log N + Real.log (2+|t|))
      = (N:ℝ)^((1:ℝ)/2) * ((2+|t|)^((1:ℝ)/2)/4 * ((Real.log N + Real.log (2+|t|))/2)) := by ring_nf
    _ ≤ (N:ℝ)^((1:ℝ)/2) *
          (‖Complex.Gamma (1 - ((t:ℂ)*I)/4) / Complex.Gamma (1/2 + ((t:ℂ)*I)/4)‖ *
            ‖Complex.log ((t:ℂ)*I + 2) + (Real.log N : ℂ)‖) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hNpos.le _)
        exact mul_le_mul hG hh htop (norm_nonneg _)
    _ = ‖Wf N ((t:ℂ)*I)‖ := hWf.symm

private lemma Wf_lower_one {N : ℕ} [NeZero N] (t : ℝ) :
    (Real.log N + Real.log (2+|t|))/2 ≤ ‖Wf N ((1:ℂ) + (t:ℂ)*I)‖ := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set s : ℂ := (1:ℂ) + (t:ℂ)*I with hs
  have hsre : s.re = 1 := by rw [hs]; simp
  have hnum : ‖(N:ℂ)^((1-s)/2)‖ = 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    congr 1
    rw [Complex.div_re, Complex.sub_re, hsre]; simp
  have hratio : ‖Complex.Gamma (1 - s/4) / Complex.Gamma (1/2 + s/4)‖ = 1 := by
    have e1 : 1 - s/4 = star (1/2 + s/4) := by
      rw [hs]; apply Complex.ext <;> simp <;> ring
    rw [e1, norm_div, Gamma_star, norm_star]
    rw [div_self]
    apply norm_ne_zero_iff.mpr
    apply Complex.Gamma_ne_zero; intro m hm
    have hre : ((1/2:ℂ) + s/4).re = 3/4 := by rw [hs]; simp; ring
    have := congrArg Complex.re hm
    rw [hre] at this
    simp at this
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hh : (Real.log N + Real.log (2+|t|))/2 ≤ ‖Complex.log (s + 2) + (Real.log N : ℂ)‖ := by
    rw [hs]; exact clog_shift_lower_one t
  have hWf : ‖Wf N s‖ = 1 * (1 * ‖Complex.log (s+2) + (Real.log N : ℂ)‖) := by
    rw [Wf, norm_mul, norm_mul, hnum, hratio]
    ring
  rw [hWf, one_mul, one_mul]
  exact hh
private lemma Wf_norm_lower_global {N : ℕ} [NeZero N] (z : ℂ) (hlo : 0 ≤ z.re) (hhi : z.re ≤ 1) :
    (1/2) * Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) * Real.log (2+|z.im|) ≤ ‖Wf N z‖ := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hzpos : 0 < 2 + |z.im| := by linarith [abs_nonneg z.im]
  have hnum : 1 ≤ ‖(N:ℂ)^((1-z)/2)‖ := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.one_le_rpow hN1
    rw [Complex.div_re, Complex.sub_re]; simp; linarith
  set u₂ : ℝ := 1 - z.re/4 with hu₂
  set u₁ : ℝ := 1/2 + z.re/4 with hu₁
  set τ : ℝ := z.im/4 with hτ
  have hu1 : (1:ℝ)/2 ≤ u₁ := by rw [hu₁]; linarith
  have h12 : u₁ ≤ u₂ := by rw [hu₁, hu₂]; linarith
  have h2 : u₂ ≤ 8 := by rw [hu₂]; linarith
  have hnum2 : (1 - z/4) = star (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I) := by
    rw [hu₂, hτ]; apply Complex.ext <;> simp
  have hden2 : (1/2 + z/4) = ((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I := by
    rw [hu₁, hτ]; apply Complex.ext <;> simp
  have hA : Complex.Gamma (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I) ≠ 0 := by
    apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.re hm; simp at this; linarith [hu1]
  have hB : Complex.Gamma (((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I) ≠ 0 := by
    apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.re hm; simp at this; linarith [hu1]
  have hApos : 0 < ‖Complex.Gamma (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ := norm_pos_iff.mpr hA
  have hBpos : 0 < ‖Complex.Gamma (((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ := norm_pos_iff.mpr hB
  have hinc := Commons.Analysis.SpecialFunctions.Gamma.abs_log_norm_Gamma_sub_le u₁ u₂ τ hu1 h12 h2
  have hτle : |τ| ≤ |z.im| := by rw [hτ, abs_div]; linarith [abs_nonneg z.im]
  have hratio' : Real.exp (-((u₂-u₁)*(Real.log (2+|τ|)+2))) ≤
      ‖Complex.Gamma (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ / ‖Complex.Gamma (((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ := by
    rw [abs_le] at hinc
    obtain ⟨hlo2, _⟩ := hinc
    have hexp : Real.exp (Real.log ‖Complex.Gamma (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ -
        Real.log ‖Complex.Gamma (((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖) =
        ‖Complex.Gamma (((u₂:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ / ‖Complex.Gamma (((u₁:ℝ):ℂ) + ((τ:ℝ):ℂ)*I)‖ := by
      rw [Real.exp_sub, Real.exp_log hApos, Real.exp_log hBpos]
    rw [← hexp]
    exact Real.exp_le_exp.mpr hlo2
  have hu21 : u₂ - u₁ = 1/2 - z.re/2 := by rw [hu₂, hu₁]; ring
  have hC : (u₂-u₁)*(Real.log (2+|τ|)+2) ≤ 1 + (1/2)*Real.log (2+|z.im|) := by
    have hlog2 : Real.log (2+|τ|) ≤ Real.log (2+|z.im|) :=
      Real.log_le_log (by linarith [abs_nonneg τ]) (by linarith [hτle])
    have hle : (u₂-u₁) ≤ 1/2 := by rw [hu21]; linarith
    have h0 : 0 ≤ u₂-u₁ := by rw [hu21]; linarith
    have h3 : 0 ≤ Real.log (2+|τ|) + 2 := by linarith [Real.log_nonneg (by linarith [abs_nonneg τ] : (1:ℝ) ≤ 2+|τ|)]
    nlinarith [hle, hlog2, h0, h3]
  have hgoal : Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) =
      Real.exp (-(1 + (1/2)*Real.log (2+|z.im|))) := by
    rw [Real.rpow_def_of_pos hzpos, ← Real.exp_add]
    congr 1; ring
  have hratio : Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) ≤
      ‖Complex.Gamma (1 - z/4) / Complex.Gamma (1/2 + z/4)‖ := by
    rw [hgoal, hnum2, hden2, norm_div, norm_Gamma_star]
    exact (Real.exp_le_exp.mpr (by rw [neg_le_neg_iff]; exact hC)).trans hratio'
  have hlog : Real.log (2+|z.im|)/2 ≤ ‖Complex.log (z+2) + (Real.log N : ℂ)‖ := clog_shift_lower hlo
  have hWf : ‖Wf N z‖ = ‖(N:ℂ)^((1-z)/2)‖ *
      (‖Complex.Gamma (1 - z/4) / Complex.Gamma (1/2 + z/4)‖ *
        ‖Complex.log (z+2) + (Real.log N : ℂ)‖) := by
    rw [Wf, norm_mul, norm_mul]; ring
  rw [hWf]
  have hel : 0 < Real.exp (-1) := Real.exp_pos _
  have hlg : 0 ≤ Real.log (2+|z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hpp : 0 < (2+|z.im|)^((-(1:ℝ)/2)) := Real.rpow_pos_of_pos hzpos _
  calc (1/2) * Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) * Real.log (2+|z.im|)
      ≤ 1 * ((Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2))) * ‖Complex.log (z+2) + (Real.log N : ℂ)‖) := by
        nlinarith [hlog, hel, hlg, hpp, mul_pos hel hpp]
    _ ≤ ‖(N:ℂ)^((1-z)/2)‖ * (‖Complex.Gamma (1 - z/4) / Complex.Gamma (1/2 + z/4)‖ *
          ‖Complex.log (z+2) + (Real.log N : ℂ)‖) := by
        gcongr

private lemma sqrt_pair_le (t : ℝ) : (2+|t|)^((1:ℝ)/2) ≤ 2 * Real.sqrt (max 1 |t|) := by
  rw [← Real.sqrt_eq_rpow]
  rcases lt_or_ge |t| 1 with h | h
  · rw [max_eq_left (le_of_lt h), Real.sqrt_one, mul_one]
    have hs : Real.sqrt (2+|t|) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at hs
  · rw [max_eq_right h]
    calc Real.sqrt (2+|t|) ≤ Real.sqrt (4*|t|) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt |t| := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
              show Real.sqrt 4 = 2 by
                rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]

private lemma F_bound_strip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ |z.im| →
      ‖LFunction χ z / Wf N z‖ ≤ Cg * (2 + |z.im|)^3 := by
  obtain ⟨D, hDpos, hD⟩ := LFunction_strip_upper_explicit (N := N) χ hχ hχprim
  refine ⟨64 * (D + 1) * ((N:ℝ) + 1)^2, by positivity, ?_⟩
  intro z hlo hhi hbig
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hDz : ‖LFunction χ z‖ ≤ D * ((N:ℝ) + |z.im| + 1)^2 := by
    have h := hD z.re z.im hlo (by linarith [hhi])
    rwa [show (z.re:ℂ) + I*(z.im:ℂ) = z from by apply Complex.ext <;> simp] at h
  have hW := Wf_norm_lower_global (N := N) z hlo hhi
  have hzpos : 0 < 2 + |z.im| := by linarith [abs_nonneg z.im]
  have hWpos : 0 < (1/2) * Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) * Real.log (2+|z.im|) := by
    have h3 : 0 < Real.log (2+|z.im|) := Real.log_pos (by linarith [abs_nonneg z.im])
    positivity
  have hlog1 : 1 ≤ Real.log (2+|z.im|) := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log (2+|z.im|) :=
      Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three, abs_nonneg z.im])
    rwa [Real.log_exp] at h1
  have he1 : (1:ℝ)/4 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (by norm_num : (0:ℝ) < 4) (Real.exp_pos 1)).mpr
      (by linarith [Real.exp_one_lt_three])
  have hb : 0 < (2+|z.im|)^((-(1:ℝ)/2)) := Real.rpow_pos_of_pos hzpos _
  have hrp : (2+|z.im|)^3 * (2+|z.im|)^((-(1:ℝ)/2)) = (2+|z.im|)^((5:ℝ)/2) := by
    rw [← Real.rpow_natCast (2+|z.im|) 3, ← Real.rpow_add hzpos]
    congr 1
    push_cast
    ring
  have h2z : (2+|z.im|)^((2:ℝ)) ≤ (2+|z.im|)^((5:ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (by norm_num)
  have hNle2 : ((N:ℝ)+|z.im|+1)^2 ≤ ((N:ℝ)+1)^2 * (2+|z.im|)^((2:ℝ)) := by
    have h1 : (N:ℝ)+|z.im|+1 ≤ ((N:ℝ)+1)*(2+|z.im|) := by nlinarith [hN1, abs_nonneg z.im]
    have h3 : (2+|z.im|)^2 = (2+|z.im|)^((2:ℝ)) := (Real.rpow_natCast _ 2).symm
    rw [← h3]
    nlinarith [h1, hN1, abs_nonneg z.im]
  rw [norm_div]
  refine (div_le_div_of_nonneg_left (norm_nonneg _) hWpos hW).trans ?_
  rw [div_le_iff₀ hWpos]
  have h5pos : 0 < (2+|z.im|)^((5:ℝ)/2) := Real.rpow_pos_of_pos hzpos _
  have hchain : D * ((N:ℝ)+|z.im|+1)^2 ≤
      (64 * (D + 1) * ((N:ℝ) + 1)^2 * (2 + |z.im|)^3) *
        ((1/2) * Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) * Real.log (2+|z.im|)) := by
    rw [show (64 * (D + 1) * ((N:ℝ) + 1)^2 * (2 + |z.im|)^3) *
        ((1/2) * Real.exp (-1) * (2+|z.im|)^((-(1:ℝ)/2)) * Real.log (2+|z.im|))
        = 64 * (D+1) * ((N:ℝ)+1)^2 * ((1/2) * Real.exp (-1)) *
          ((2+|z.im|)^3 * (2+|z.im|)^((-(1:ℝ)/2))) * Real.log (2+|z.im|) by ring, hrp]
    have hNn : (0:ℝ) ≤ ((N:ℝ)+1)^2 := by positivity
    have h1 : D * ((N:ℝ)+|z.im|+1)^2 ≤ D * (((N:ℝ)+1)^2 * (2+|z.im|)^((2:ℝ))) :=
      mul_le_mul_of_nonneg_left hNle2 hDpos.le
    have h2 : D * (((N:ℝ)+1)^2 * (2+|z.im|)^((2:ℝ))) ≤ D * (((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2z hNn) hDpos.le
    have h3 : D * (((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2)) ≤
        64 * (D+1) * ((N:ℝ)+1)^2 * ((1/2) * Real.exp (-1)) *
          (2+|z.im|)^((5:ℝ)/2) * Real.log (2+|z.im|) := by
      have hD1 : D ≤ 64*(D+1) := by linarith
      have h5n : 0 ≤ (2+|z.im|)^((5:ℝ)/2) := le_of_lt h5pos
      have hmul : (1:ℝ)/4 ≤ Real.exp (-1) * Real.log (2+|z.im|) := by
        nlinarith [he1, hlog1, (Real.exp_pos (-1)).le]
      have hNn2 : 0 ≤ ((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2) := by positivity
      have hD8 : D ≤ 8*(D+1) := by linarith
      have hmul4 : (1:ℝ) ≤ 4 * (Real.exp (-1) * Real.log (2+|z.im|)) := by linarith [hmul]
      have hstep : 8*(D+1) ≤ 32*(D+1)*(Real.exp (-1) * Real.log (2+|z.im|)) := by
        rw [show 32*(D+1)*(Real.exp (-1)*Real.log (2+|z.im|))
            = 8*(D+1) * (4*(Real.exp (-1)*Real.log (2+|z.im|))) by ring]
        simpa using mul_le_mul_of_nonneg_left hmul4 (show (0:ℝ) ≤ 8*(D+1) by linarith)
      calc D * (((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2))
          ≤ 8*(D+1) * (((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2)) :=
            mul_le_mul_of_nonneg_right hD8 (by positivity)
        _ ≤ 32*(D+1)*(Real.exp (-1)*Real.log (2+|z.im|)) * (((N:ℝ)+1)^2 * (2+|z.im|)^((5:ℝ)/2)) :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
        _ = 64 * (D+1) * ((N:ℝ)+1)^2 * ((1/2) * Real.exp (-1)) * (2+|z.im|)^((5:ℝ)/2) * Real.log (2+|z.im|) := by ring
    exact h1.trans (h2.trans h3)

  linarith [hDz, hchain]



private lemma Wf_zero_norm {N : ℕ} [NeZero N] :
    ‖Wf N 0‖ = (N:ℝ)^((1:ℝ)/2) * (1/Real.sqrt Real.pi) * (Real.log N + Real.log 2) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hlog2 : Complex.log (2:ℂ) = ((Real.log 2 : ℝ):ℂ) := by
    have := Complex.ofReal_log (show (0:ℝ) ≤ 2 by norm_num)
    simpa using this.symm
  have hnum : ‖(N:ℂ)^((1:ℂ)/2)‖ = (N:ℝ)^((1:ℝ)/2) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    congr 1; simp [Complex.div_re]
  have hWf0 : Wf N 0 = (N:ℂ)^((1:ℂ)/2) * (1 / Complex.Gamma (1/2:ℂ)) *
      (((Real.log 2 : ℝ):ℂ) + (Real.log N : ℂ)) := by
    unfold Wf
    rw [show ((1:ℂ) - 0)/2 = (1:ℂ)/2 from by ring,
        show (1:ℂ) - 0/4 = 1 from by ring,
        show (1/2:ℂ) + 0/4 = 1/2 from by ring,
        show (0:ℂ) + 2 = 2 from by ring, hlog2, Complex.Gamma_one, one_div]
  rw [hWf0, norm_mul, norm_mul, hnum, norm_div, Gamma_half_norm, norm_one]
  have hlogN2 : ‖((Real.log 2 : ℝ):ℂ) + (Real.log N : ℂ)‖ = Real.log 2 + Real.log N := by
    rw [← Complex.ofReal_add]
    rw [show ‖(((Real.log 2 + Real.log N : ℝ)):ℂ)‖ = |Real.log 2 + Real.log N| from
      RCLike.norm_ofReal _]
    rw [abs_of_nonneg]
    have h1 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    have h2 := Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)) : (1:ℝ) ≤ (N:ℝ))
    linarith
  rw [hlogN2]
  ring

private lemma LFunction_zero_norm_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ‖LFunction χ 0‖ ≤ (N:ℝ)^((1:ℝ)/2) * (Real.log N + Real.log 2 + 6) := by
  have hNne : N ≠ 1 := by
    intro h; subst h; exact hχ (Subsingleton.elim χ 1)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  rcases χ.even_or_odd with he | ho
  · have hg0 : χ.gammaFactor 0 = 0 := by
      rw [DirichletCharacter.Even.gammaFactor_def he]
      exact Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by norm_num⟩
    rw [LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hNne), hg0, div_zero, norm_zero]
    positivity
  · have hχine : χ⁻¹ ≠ 1 := by
      intro h; apply hχ
      have := congrArg (fun ψ : DirichletCharacter ℂ N => ψ⁻¹) h
      simpa using this
    have hg0 : χ.gammaFactor 0 = Complex.Gammaℝ 1 := by
      rw [DirichletCharacter.Odd.gammaFactor_def ho]; norm_num
    have hL0 : LFunction χ 0 = completedLFunction χ 0 / Complex.Gammaℝ 1 := by
      rw [LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hNne), hg0]
    rw [hL0, norm_div, GammaR_one_norm, div_one]
    have hγi : (χ⁻¹).gammaFactor 1 ≠ 0 := by
      rw [DirichletCharacter.Odd.gammaFactor_def
        (Commons.NumberTheory.DirichletCharacter.Odd_inv ho)]
      rw [show (1:ℂ) + 1 = 2 from by norm_num, Complex.Gammaℝ_def]
      apply mul_ne_zero
      · rw [Complex.cpow_ne_zero_iff]
        exact Or.inl (by exact_mod_cast (ne_of_gt Real.pi_pos) : (Real.pi:ℂ) ≠ 0)
      · rw [show (2:ℂ)/2 = 1 from by norm_num, Complex.Gamma_one]; exact one_ne_zero
    have hcompl : completedLFunction (χ⁻¹) 1 = LFunction (χ⁻¹) 1 * (χ⁻¹).gammaFactor 1 := by
      have h := LFunction_eq_completed_div_gammaFactor (χ⁻¹) 1 (Or.inl (by norm_num : (1:ℂ) ≠ 0))
      rw [h]; exact (div_mul_cancel₀ _ hγi).symm
    have hb : ‖LFunction (χ⁻¹) 1‖ ≤ Real.log N + Real.log 2 + 6 := by
      have h := norm_LFunction_le_re_ge_one (χ⁻¹) hχine 1 (by simp)
      simpa using h
    have hcomp_eq : completedLFunction χ 0 =
        (N:ℂ)^((1:ℂ)/2 - 0) * χ.rootNumber * completedLFunction χ⁻¹ (1 - 0) :=
      completedLFunction_eq χ hχprim 0
    have hcomp0 : completedLFunction χ⁻¹ (1 - 0) = LFunction (χ⁻¹) 1 * (χ⁻¹).gammaFactor 1 := by
      rw [show (1:ℂ) - 0 = 1 from by ring]; exact hcompl
    have hNpow : ‖(N:ℂ)^((1:ℂ)/2 - 0)‖ = (N:ℝ)^((1:ℝ)/2) := by
      rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))]
      congr 1
      rw [Complex.sub_re, Complex.div_re]; simp
    have hroot := rootNumber_norm_eq_one χ hχprim
    rw [hcomp_eq, norm_mul, norm_mul, hNpow, hroot, mul_one, hcomp0, norm_mul]
    have hγ1 : ‖(χ⁻¹).gammaFactor 1‖ ≤ 1 := gammaFactor_one_norm_le_one (χ⁻¹)
    have hLnn : 0 ≤ Real.log N + Real.log 2 + 6 := by
      have h1 := Real.log_nonneg hN1
      have h2 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
      linarith
    calc (N:ℝ)^((1:ℝ)/2) * (‖LFunction (χ⁻¹) 1‖ * ‖(χ⁻¹).gammaFactor 1‖)
        ≤ (N:ℝ)^((1:ℝ)/2) * ((Real.log N + Real.log 2 + 6) * 1) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
          exact mul_le_mul hb hγ1 (norm_nonneg _) hLnn
      _ = (N:ℝ)^((1:ℝ)/2) * (Real.log N + Real.log 2 + 6) := by ring
private lemma F_growth {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ B : ℝ, (fun z : ℂ => LFunction χ z / Wf N z) =O[
      Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo 0 1)]
      (fun z : ℂ => Real.exp (B * Real.exp (1 * |z.im|))) := by
  obtain ⟨Cg, hCgpos, hCg⟩ := F_bound_strip χ hχ hχprim
  refine ⟨40 + |Real.log Cg| + 1, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  rw [Filter.eventually_inf_principal, Filter.eventually_comap]
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with b hb
  intro z hzim hz
  have h1 : (1:ℝ) ≤ |z.im| := by
    have h := hb
    simp only [Function.comp_apply] at hzim
    rw [← hzim] at h
    exact h
  have hzre : 0 ≤ z.re ∧ z.re ≤ 1 := by
    simp only [Set.mem_preimage, Set.mem_Ioo] at hz
    exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hone : (1:ℝ) * |z.im| = |z.im| := one_mul _
  have hcube : (2 + |z.im|)^3 ≤ Real.exp (3 * |z.im| + 5) := by
    have hx0 : (0:ℝ) ≤ |z.im| := by linarith
    have h3 : (2 + |z.im|)^3 ≤ (3 * |z.im|)^3 :=
      pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 2 + |z.im|) (by linarith) 3
    have hx3 : |z.im|^3 ≤ Real.exp (3 * |z.im|) := by
      have hle : |z.im| ≤ Real.exp |z.im| := by linarith [Real.add_one_le_exp |z.im|]
      have h := pow_le_pow_left₀ hx0 hle 3
      have e : Real.exp |z.im| ^ 3 = Real.exp (3 * |z.im|) := by
        rw [show Real.exp (3 * |z.im|) = Real.exp |z.im| ^ 3 from by
          rw [show (3:ℝ) * |z.im| = ((3:ℕ):ℝ) * |z.im| by norm_num, Real.exp_nat_mul]]
      exact h.trans (le_of_eq e)
    have hexp5 : (27:ℝ) ≤ Real.exp 5 := by
      have he1 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by
        rw [show (5:ℝ) = ((5:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
      rw [h2]
      have h3 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he1 5
      norm_num at h3
      linarith
    have h4 : (3 * |z.im|)^3 = 27 * |z.im|^3 := by ring
    have h5 : 27 * |z.im|^3 ≤ 27 * Real.exp (3 * |z.im|) :=
      mul_le_mul_of_nonneg_left hx3 (by norm_num)
    have h6 : 27 * Real.exp (3 * |z.im|) ≤ Real.exp 5 * Real.exp (3 * |z.im|) :=
      mul_le_mul_of_nonneg_right hexp5 (Real.exp_pos _).le
    have h7 : Real.exp 5 * Real.exp (3 * |z.im|) = Real.exp (3 * |z.im| + 5) := by
      rw [Real.exp_add]
      ring
    linarith [h3, h4, h5, h6, h7]
  have hBbound : 3 * |z.im| + 5 + Real.log Cg ≤
      (40 + |Real.log Cg| + 1) * Real.exp |z.im| := by
    have hx0 : (0:ℝ) ≤ |z.im| := by linarith
    have hex : 1 ≤ Real.exp |z.im| := Real.one_le_exp hx0
    have hB0 : 0 ≤ |Real.log Cg| + 1 := by positivity
    have hlogabs : Real.log Cg ≤ |Real.log Cg| := le_abs_self _
    have hsplit : (40 + |Real.log Cg| + 1) * Real.exp |z.im| =
        40 * Real.exp |z.im| + (|Real.log Cg| + 1) * Real.exp |z.im| := by ring
    have hA : 40 * (|z.im| + 1) ≤ 40 * Real.exp |z.im| :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp |z.im|) (by norm_num)
    have hC : (|Real.log Cg| + 1) ≤ (|Real.log Cg| + 1) * Real.exp |z.im| := by
      nlinarith [hB0, hex]
    linarith [hsplit, hA, hC, hlogabs, hx0]
  have hexp_ge : Real.exp (3 * |z.im| + 5) * Cg ≤
      Real.exp ((40 + |Real.log Cg| + 1) * Real.exp |z.im|) := by
    have h : Real.exp (3 * |z.im| + 5 + Real.log Cg) = Real.exp (3 * |z.im| + 5) * Cg := by
      rw [Real.exp_add, Real.exp_log hCgpos]
    rw [← h]
    exact Real.exp_le_exp.mpr hBbound
  have hmain : Cg * (2 + |z.im|)^3 ≤
      Real.exp ((40 + |Real.log Cg| + 1) * Real.exp (1 * |z.im|)) := by
    rw [hone]
    calc Cg * (2 + |z.im|)^3 ≤ Cg * Real.exp (3 * |z.im| + 5) :=
          mul_le_mul_of_nonneg_left hcube hCgpos.le
      _ = Real.exp (3 * |z.im| + 5) * Cg := by ring
      _ ≤ Real.exp ((40 + |Real.log Cg| + 1) * Real.exp |z.im|) := hexp_ge
  calc ‖LFunction χ z / Wf N z‖ ≤ Cg * (2 + |z.im|)^3 := hCg z hzre.1 hzre.2 h1
    _ ≤ Real.exp ((40 + |Real.log Cg| + 1) * Real.exp (1 * |z.im|)) := hmain
    _ = 1 * ‖Real.exp ((40 + |Real.log Cg| + 1) * Real.exp (1 * |z.im|))‖ := by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        simp


private lemma F_bound_boundary {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    (∀ z : ℂ, z.re = 0 → ‖LFunction χ z / Wf N z‖ ≤ 29) ∧
      (∀ z : ℂ, z.re = 1 → ‖LFunction χ z / Wf N z‖ ≤ 29) := by
  have hN2' : (2:ℝ) ≤ N := by
    have := two_le_of_ne_one χ hχ
    exact_mod_cast this
  have hNpos : (0:ℝ) < N := by linarith
  have h7sqrt : (7:ℝ) ≤ 29 * (1/Real.sqrt Real.pi) := by
    rw [mul_one_div]
    have hs : Real.sqrt Real.pi ≤ 2 := by
      rw [show (2:ℝ) = Real.sqrt 4 from by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (le_of_lt Real.pi_lt_four)
    rw [le_div_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)]
    nlinarith [hs, Real.sqrt_nonneg Real.pi]
  have hbase : ∀ w : ℝ, 0 ≤ w → 1 ≤ Real.log N + Real.log (2 + w) := by
    intro w hw
    have h4 : 1 ≤ Real.log ((N:ℝ) * (2 + w)) := by
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log ((N:ℝ)*(2+w)) := Real.log_le_log (Real.exp_pos 1)
              (by nlinarith [hN2', Real.exp_one_lt_three, hw])
    rwa [Real.log_mul (ne_of_gt hNpos) (ne_of_gt (by linarith))] at h4
  constructor
  · intro z hz
    have hzeq : z = ((z.im:ℝ):ℂ)*I := by apply Complex.ext <;> simp [hz]
    rcases eq_or_ne z.im 0 with h0 | h0
    · rw [hzeq, h0, Complex.ofReal_zero, zero_mul, norm_div, Wf_zero_norm (N:=N)]
      have hs1 : 1 ≤ Real.log N + Real.log 2 := by
        have := hbase 0 le_rfl; simpa using this
      have hsp : 0 < Real.log N + Real.log 2 := by linarith
      rw [div_le_iff₀ (mul_pos (mul_pos (Real.rpow_pos_of_pos hNpos _) (by positivity)) hsp)]
      have hN12 : 0 ≤ (N:ℝ)^((1:ℝ)/2) := Real.rpow_nonneg (by positivity) _
      calc ‖LFunction χ 0‖ ≤ (N:ℝ)^((1:ℝ)/2) * (Real.log N + Real.log 2 + 6) :=
            LFunction_zero_norm_le χ hχ hχprim
        _ ≤ (N:ℝ)^((1:ℝ)/2) * (7 * (Real.log N + Real.log 2)) :=
              mul_le_mul_of_nonneg_left (by linarith) hN12
        _ ≤ (N:ℝ)^((1:ℝ)/2) * ((29 * (1/Real.sqrt Real.pi)) * (Real.log N + Real.log 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h7sqrt hsp.le) hN12
        _ = 29 * ((N:ℝ)^((1:ℝ)/2) * (1/Real.sqrt Real.pi) * (Real.log N + Real.log 2)) := by ring
    · have hL := LFunction_norm_zero_le_sharp χ hχ hχprim z.im h0
      have hW := Wf_lower_zero (N:=N) z.im h0
      have hs1 : 1 ≤ Real.log N + Real.log (2+|z.im|) := hbase |z.im| (abs_nonneg _)
      have hsp : 0 < Real.log N + Real.log (2+|z.im|) := by linarith
      have hWpos : 0 < ‖Wf N (((z.im:ℝ):ℂ)*I)‖ :=
        lt_of_lt_of_le (mul_pos (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hNpos _))
          (Real.rpow_pos_of_pos (by positivity) _)) hsp) hW
      rw [hzeq, norm_div, div_le_iff₀ hWpos]
      have h7 : Real.log N + Real.log (2+|z.im|) + 6 ≤
          7 * (Real.log N + Real.log (2+|z.im|)) := by linarith
      have hsqrt2 : (2:ℝ) ≤ Real.sqrt (2*Real.pi) := by
        have h : (2:ℝ)^2 ≤ 2*Real.pi := by nlinarith [Real.pi_gt_three]
        calc (2:ℝ) = Real.sqrt (2^2) := (Real.sqrt_sq (by norm_num)).symm
          _ ≤ Real.sqrt (2*Real.pi) := Real.sqrt_le_sqrt h
      have h56 : (56:ℝ) ≤ 29 * Real.sqrt (2*Real.pi) := by nlinarith [hsqrt2]
      have hkey : (1/Real.sqrt (2*Real.pi)) * (Real.log N + Real.log (2+|z.im|) + 6) ≤
          29 * ((1/8) * (Real.log N + Real.log (2+|z.im|))) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have h2 : (56:ℝ) * (Real.log N + Real.log (2+|z.im|)) ≤
            29 * Real.sqrt (2*Real.pi) * (Real.log N + Real.log (2+|z.im|)) :=
          mul_le_mul_of_nonneg_right h56 (le_of_lt hsp)
        nlinarith [h7, h2]
      calc ‖LFunction χ (((z.im:ℝ):ℂ)*I)‖
          ≤ (1/Real.sqrt (2*Real.pi)) * (N:ℝ)^((1:ℝ)/2) * (2+|z.im|)^((1:ℝ)/2) *
              (Real.log N + Real.log (2+|z.im|) + 6) := hL
        _ = ((N:ℝ)^((1:ℝ)/2) * (2+|z.im|)^((1:ℝ)/2)) *
              ((1/Real.sqrt (2*Real.pi)) * (Real.log N + Real.log (2+|z.im|) + 6)) := by ring
        _ ≤ ((N:ℝ)^((1:ℝ)/2) * (2+|z.im|)^((1:ℝ)/2)) *
              (29 * ((1/8) * (Real.log N + Real.log (2+|z.im|)))) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = 29 * ((1/8) * (N:ℝ)^((1:ℝ)/2) * (2+|z.im|)^((1:ℝ)/2) *
              (Real.log N + Real.log (2+|z.im|))) := by ring
        _ ≤ 29 * ‖Wf N (((z.im:ℝ):ℂ)*I)‖ := mul_le_mul_of_nonneg_left hW (by norm_num)
  · intro z hz
    have hzeq : z = (1:ℂ) + ((z.im:ℝ):ℂ)*I := by apply Complex.ext <;> simp [hz]
    have hL := norm_LFunction_le_re_ge_one χ hχ ((1:ℂ) + ((z.im:ℝ):ℂ)*I) (by simp)
    have hW := Wf_lower_one (N:=N) z.im
    have hs1 : 1 ≤ Real.log N + Real.log (2+|z.im|) := hbase |z.im| (abs_nonneg _)
    have hsp : 0 < Real.log N + Real.log (2+|z.im|) := by linarith
    have hWpos : 0 < ‖Wf N ((1:ℂ) + ((z.im:ℝ):ℂ)*I)‖ :=
      lt_of_lt_of_le (by linarith) hW
    rw [hzeq, norm_div, div_le_iff₀ hWpos]
    have hbound : ‖LFunction χ ((1:ℂ) + ((z.im:ℝ):ℂ)*I)‖ ≤
        Real.log N + Real.log (2+|z.im|) + 6 := by
      have h := hL
      rw [show ((1:ℂ) + ((z.im:ℝ):ℂ)*I).im = z.im from by simp] at h
      simpa using h
    have hkey : Real.log N + Real.log (2+|z.im|) + 6 ≤
        29 * ((Real.log N + Real.log (2+|z.im|))/2) := by nlinarith [hs1]
    calc ‖LFunction χ ((1:ℂ) + ((z.im:ℝ):ℂ)*I)‖ ≤ Real.log N + Real.log (2+|z.im|) + 6 := hbound
      _ ≤ 29 * ((Real.log N + Real.log (2+|z.im|))/2) := hkey
      _ ≤ 29 * ‖Wf N ((1:ℂ) + ((z.im:ℝ):ℂ)*I)‖ := mul_le_mul_of_nonneg_left hW (by norm_num)

theorem LFunction_strip_convexity_abs {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {σ T : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    Real.log ‖DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
      ((1 - σ) / 2) * (Real.log (N : ℝ) + Real.log (2 + |T|)) +
        Real.log (Real.log ((N : ℝ) * (2 + |T|)) + 2) + 6 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  obtain ⟨hb0, hb1⟩ := F_bound_boundary χ hχ hχprim
  obtain ⟨B, hB⟩ := F_growth χ hχ hχprim
  set z : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hz
  have hzre : z.re = σ := by rw [hz]; simp
  have hzim : |z.im| = |T| := by rw [hz]; simp
  have hclos : closure (Complex.re ⁻¹' Set.Ioo (0:ℝ) 1) ⊆ Complex.re ⁻¹' Set.Icc (0:ℝ) 1 := by
    apply closure_minimal _ (isClosed_Icc.preimage continuous_re)
    intro w hw
    simp only [Set.mem_preimage, Set.mem_Icc] at hw ⊢
    exact ⟨le_of_lt hw.1, le_of_lt hw.2⟩
  have hdco : DiffContOnCl ℂ (fun s : ℂ => LFunction χ s / Wf N s)
      (Complex.re ⁻¹' Set.Ioo (0:ℝ) 1) :=
    ⟨F_differentiableOn χ hχ, (F_continuousOn χ hχ).mono hclos⟩
  have hWfne : Wf N z ≠ 0 := Wf_ne_zero_strip z (by rw [hzre]; exact hσ0) (by rw [hzre]; exact hσ1)
  have hnormpos : 0 < ‖Wf N z‖ := norm_pos_iff.mpr hWfne
  have hPL : ‖LFunction χ z / Wf N z‖ ≤ 29 :=
    PhragmenLindelof.vertical_strip (a := 0) (b := 1) (C := 29)
      (f := fun s : ℂ => LFunction χ s / Wf N s) (z := z) hdco
      ⟨1, by rw [sub_zero, div_one]; linarith [Real.pi_gt_three], B, hB⟩ hb0 hb1
      (by rw [hzre]; exact hσ0) (by rw [hzre]; exact hσ1)
  have hLle : ‖LFunction χ z‖ ≤ 29 * ‖Wf N z‖ := by
    rw [norm_div] at hPL
    exact (div_le_iff₀ hnormpos).mp hPL
  have hW := Wf_norm_upper (N := N) z (by rw [hzre]; exact hσ0) (by rw [hzre]; exact hσ1)
  have hbound : ‖LFunction χ z‖ ≤
      (29 * (5*Real.exp 1)) * (((N:ℝ)*(2+|z.im|))^((1-z.re)/2) *
        (Real.log ((N:ℝ)*(2+|z.im|)) + 2)) := by
    calc ‖LFunction χ z‖ ≤ 29 * ‖Wf N z‖ := hLle
      _ ≤ 29 * (5 * Real.exp 1 * ((N:ℝ)*(2+|z.im|))^((1-z.re)/2) *
            (Real.log ((N:ℝ)*(2+|z.im|)) + 2)) := mul_le_mul_of_nonneg_left hW (by norm_num)
      _ = (29 * (5*Real.exp 1)) * (((N:ℝ)*(2+|z.im|))^((1-z.re)/2) *
            (Real.log ((N:ℝ)*(2+|z.im|)) + 2)) := by ring
  rw [hzim, hzre] at hbound
  have harg1 : (1:ℝ) ≤ (N:ℝ)*(2+|T|) := by nlinarith [abs_nonneg T, hN1]
  have hlog : Real.log (29 * (5*Real.exp 1)) ≤ 6 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have he5 : (145:ℝ) ≤ Real.exp 1 ^ 5 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283)
        (le_of_lt Real.exp_one_gt_d9) 5
      norm_num at h ⊢
      linarith
    have he6 : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [show (6:ℝ) = ((6:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [he6]
    nlinarith [he5, Real.exp_pos 1]
  set E : ℝ := ((N:ℝ)*(2+|T|))^((1-σ)/2) * (Real.log ((N:ℝ)*(2+|T|)) + 2) with hE
  have hEpos : 0 < E := by
    rw [hE]
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (by have := Real.log_nonneg harg1; linarith)
  have hE1 : 1 ≤ E := by
    rw [hE]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow harg1 (by linarith))
      (by have := Real.log_nonneg harg1; linarith)
  have hlogbound : Real.log ‖LFunction χ z‖ ≤ Real.log (29 * (5*Real.exp 1)) + Real.log E := by
    have h1 : Real.log ‖LFunction χ z‖ ≤ Real.log ((29 * (5*Real.exp 1)) * E) := by
      rcases eq_or_lt_of_le (norm_nonneg (LFunction χ z)) with h0 | hpos
      · rw [← h0, Real.log_zero]
        apply Real.log_nonneg
        have h2 : (1:ℝ) ≤ (29 * (5*Real.exp 1)) := by nlinarith [Real.exp_one_gt_two]
        nlinarith [hE1, h2]
      · exact Real.log_le_log hpos (by rw [hE]; exact hbound)
    rw [Real.log_mul (ne_of_gt (mul_pos (by norm_num) (mul_pos (by norm_num) (Real.exp_pos 1)))) (ne_of_gt hEpos)] at h1
    exact h1
  have hlogE : Real.log E = ((1-σ)/2) * (Real.log N + Real.log (2+|T|)) +
      Real.log (Real.log ((N:ℝ)*(2+|T|)) + 2) := by
    calc Real.log E = Real.log (((N:ℝ)*(2+|T|))^((1-σ)/2) *
          (Real.log ((N:ℝ)*(2+|T|)) + 2)) := by rw [hE]
      _ = Real.log (((N:ℝ)*(2+|T|))^((1-σ)/2)) +
          Real.log (Real.log ((N:ℝ)*(2+|T|)) + 2) := by
            rw [Real.log_mul (by positivity)
              (ne_of_gt (by have := Real.log_nonneg harg1; linarith))]
      _ = ((1-σ)/2) * Real.log ((N:ℝ)*(2+|T|)) +
          Real.log (Real.log ((N:ℝ)*(2+|T|)) + 2) := by
            rw [Real.log_rpow (by nlinarith [abs_nonneg T, le_of_lt hNpos])]
      _ = ((1-σ)/2) * (Real.log N + Real.log (2+|T|)) +
          Real.log (Real.log ((N:ℝ)*(2+|T|)) + 2) := by
            rw [Real.log_mul (ne_of_gt hNpos) (by positivity)]
  calc Real.log ‖LFunction χ z‖ ≤ Real.log (29 * (5*Real.exp 1)) + Real.log E := hlogbound
    _ ≤ 6 + (((1-σ)/2) * (Real.log N + Real.log (2+|T|)) +
          Real.log (Real.log ((N:ℝ)*(2+|T|)) + 2)) := by rw [hlogE]; linarith [hlog]
    _ = ((1 - σ) / 2) * (Real.log (N : ℝ) + Real.log (2 + |T|)) +
          Real.log (Real.log ((N : ℝ) * (2 + |T|)) + 2) + 6 := by ring
