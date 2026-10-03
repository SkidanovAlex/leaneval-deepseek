import Mathlib
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.LogDeriv
import Submission.Port.LogDerivCompat
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Trigonometric

open Complex Filter Metric Set
open scoped Real Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Zeta

/-!
# Bounding `logDeriv ζ₁` on the negative strip `−3/2 ≤ Re s ≤ −1/2`

For `s = σ + i t` with `−3/2 ≤ σ ≤ −1/2` and `|t| ≥ 2`, its reflection `1 − s` has
real part `1 − σ ∈ [3/2, 5/2]`, deep inside the half-plane of absolute convergence
`Re w > 1`.  The functional equation in logarithmic-derivative form
(`zeta_logDeriv_fe_expanded`)

    ζ'/ζ (s) = log(2π) − ψ(1−s) + (π/2)·tan(π(1−s)/2) − ζ'/ζ (1−s)

then bounds `ζ'/ζ (s)` by

* a constant `M` for the reflected term `ζ'/ζ (1−s)` (`logDeriv_zeta_const_bound`,
  from the absolutely convergent von-Mangoldt Dirichlet series `−ζ'/ζ = ∑ Λ(n) n^{-w}`
  valid for `Re w > 1`; here moreover `Re (1−s) ≥ 3/2`),
* the digamma bound `‖ψ(1−s)‖ ≤ 3 L³` (`digamma_mid_strip_le`), and
* the tangent bound `‖(π/2)·tan(π(1−s)/2)‖ ≤ 2π L³` (`tan_norm_le_of_abs_im_ge`, using
  `|Im (π(1−s)/2)| = (π/2)|t| ≥ π ≥ 1`),

with `L = log(|t|+3)+1 ≥ 1`.  Finally `logDeriv ζ₁ = ζ'/ζ + 1/(s−1)` with `1/‖s−1‖ ≤ 1`.

The Riemann hypothesis only enters through the nonvanishing of `ζ` on the strip (a zero
there would have real part `1/2`); the analytic bounds themselves are unconditional.
-/

/-- A constant bound for `‖ζ'/ζ‖` in the half-plane `Re ≥ 3/2`, coming from the absolutely
convergent von-Mangoldt Dirichlet series `−ζ'/ζ(w) = ∑ Λ(n) n^{-w}`. -/
theorem logDeriv_zeta_const_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ w : ℂ, (3 / 2 : ℝ) ≤ w.re →
      ‖deriv riemannZeta w / riemannZeta w‖ ≤ M := by
  set F : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with hFdef
  have hsum : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) /
      (n : ℝ) ^ ((3 : ℝ) / 2)) :=
    summable_vonMangoldt_div_rpow (by norm_num)
  refine ⟨(∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2)) + 1,
    by positivity, ?_⟩
  intro w hw
  have hw1 : (1 : ℝ) < w.re := by linarith
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := w) hw1
  have hsumm : Summable (LSeries.term F w) := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := w) hw1
    rw [LSeriesSummable] at h
    simpa [F] using h
  have hnormsum : Summable (fun n => ‖LSeries.term F w n‖) := summable_norm_iff.mpr hsumm
  have h1 : ‖deriv riemannZeta w / riemannZeta w‖ ≤ ∑' n, ‖LSeries.term F w n‖ := by
    rw [show deriv riemannZeta w / riemannZeta w = - LSeries F w by rw [hL]; ring]
    rw [norm_neg, LSeries]
    exact norm_tsum_le_tsum_norm hnormsum
  have h2 : (∑' n, ‖LSeries.term F w n‖) ≤
      ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2) := by
    apply Summable.tsum_le_tsum ?_ hnormsum hsum
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [if_neg hn]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hnormF : ‖F n‖ = (ArithmeticFunction.vonMangoldt n : ℝ) := by
        simp [F, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
      rw [hnormF]
      apply div_le_div_of_nonneg_left hΛ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hn1 hw
  linarith

/-- Under RH, `ζ` has no zero on the strip `−3/2 ≤ Re s ≤ −1/2`: a zero there is not a trivial
zero (`−2, −4, …` all have real part `≤ −2`), so the Riemann hypothesis forces real part `1/2`. -/
private lemma zeta_ne_zero_of_rh_neg_strip (h : RiemannHypothesis) {s : ℂ}
    (hlo : -(3 / 2 : ℝ) ≤ s.re) (hhi : s.re ≤ -(1 / 2 : ℝ)) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have hren : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by norm_num
    rw [hren] at hre
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    linarith
  have hhalf : s.re = 1 / 2 := h s hz htriv hs1
  linarith

/-- If `0 < re w` then `w` avoids the non-positive integers. -/
private lemma ne_neg_nat_of_re_pos {w : ℂ} (hw : (0 : ℝ) < w.re) : ∀ n : ℕ, w ≠ -(n : ℂ) := by
  intro n hn
  have hre := congrArg Complex.re hn
  have hren : (-(n : ℂ)).re = -((n : ℝ)) := by simp
  rw [hren] at hre
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
  have hnn : -((n : ℝ)) ≤ 0 := by linarith
  linarith

/-- The cosine factor `cos (π(1−s)/2)` of the functional equation is nonzero whenever
`im s ≠ 0`, because it vanishes only at real points `s = −2k`. -/
private lemma cos_pi_one_sub_two_ne_zero_of_im_ne_zero {s : ℂ} (ht : s.im ≠ 0) :
    Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
  intro hz
  rcases Complex.cos_eq_zero_iff.mp hz with ⟨k, hk⟩
  have hz_im0 : (↑Real.pi * (1 - s) / 2).im = 0 := by
    rw [hk]
    simp
  have hzi_ne : (↑Real.pi * (1 - s) / 2).im ≠ 0 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hne : (Real.pi / 2) ≠ 0 := div_ne_zero hpi (by norm_num)
    have : -(Real.pi / 2) * s.im ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hne) ht
    simpa [Complex.mul_im] using this
  exact hzi_ne hz_im0

/-- `ζ₁ = (s−1)·ζ` in logarithmic-derivative form (for `s ≠ 1` with `ζ s ≠ 0`). -/
private lemma zeta1_logDeriv_eq (s : ℂ) (hs1 : s ≠ 1) (hζs : riemannZeta s ≠ 0) :
    logDeriv riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ := by
  have hEq : riemannZeta₁ =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [eventually_ne_nhds hs1] with z hzne
    have hz := riemannZeta_eq_inv_sub_mul hzne
    calc
      riemannZeta₁ z = (z - 1) * ((z - 1)⁻¹ * riemannZeta₁ z) := by
        rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hzne)]
        simp
      _ = (z - 1) * riemannZeta z := by rw [hz]
  have hcong := logDeriv_congr_nhds hEq
  have hval : logDeriv riemannZeta₁ s = logDeriv (fun z => (z - 1) * riemannZeta z) s :=
    hcong.self_of_nhds
  rw [hval]
  have hmul := Submission.Port.logDeriv_mul_fun (x := s) (f := fun z => z - 1) (g := riemannZeta)
      (sub_ne_zero.mpr hs1) hζs (by fun_prop) (differentiableAt_riemannZeta hs1)
  rw [hmul]
  have hld_id : logDeriv (fun z : ℂ => z - 1) s = (s - 1)⁻¹ := by
    rw [logDeriv_apply]
    have hd : deriv (fun z : ℂ => z - 1) s = 1 := by
      simpa using ((hasDerivAt_id s).sub_const (1 : ℂ)).deriv
    rw [hd]
    simp
  rw [hld_id, logDeriv_apply]
  ring

/-- `‖logDeriv ζ₁ s‖ ≤ ‖ζ'/ζ (s)‖ + 1/‖s−1‖` for `s ≠ 1` with `ζ s ≠ 0`. -/
private lemma norm_zeta1_logDeriv_le (s : ℂ) (hs1 : s ≠ 1) (hζs : riemannZeta s ≠ 0) :
    ‖logDeriv riemannZeta₁ s‖ ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := by
  rw [zeta1_logDeriv_eq s hs1 hζs]
  exact norm_add_le _ _

/-- The logarithmic factor `L(t) := log (|t| + 3) + 1`. -/
private def L (t : ℝ) : ℝ := Real.log (|t| + 3) + 1

private lemma L_ge_one (t : ℝ) (ht : (2 : ℝ) ≤ |t|) : (1 : ℝ) ≤ L t := by
  dsimp [L]
  have h : 0 ≤ Real.log (|t| + 3) := by
    apply Real.log_nonneg
    linarith [abs_nonneg t]
  linarith

private lemma L_pow3_ge_one (t : ℝ) (ht : (2 : ℝ) ≤ |t|) : (1 : ℝ) ≤ (L t) ^ 3 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (L_ge_one t ht) 3
  simpa using h

/-- Norm of the constant `log(2π)` equals `log (2π)`. -/
private lemma norm_log_two_pi : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ = Real.log (2 * Real.pi) := by
  have h0le : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hclog : Complex.log ((2 * Real.pi : ℝ) : ℂ) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) :=
    (Complex.ofReal_log h0le).symm
  rw [hclog]
  have hnon : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.two_le_pi]
  exact Complex.norm_of_nonneg hnon

/-- `log (2π) · L(t)³` absorbs the constant `log(2π)`. -/
private lemma log_two_pi_mul_L3_le (t : ℝ) (ht : (2 : ℝ) ≤ |t|) :
    Real.log (2 * Real.pi) ≤ Real.log (2 * Real.pi) * (L t) ^ 3 := by
  have hnon : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.two_le_pi]
  calc
    Real.log (2 * Real.pi) = Real.log (2 * Real.pi) * 1 := by ring
    _ ≤ Real.log (2 * Real.pi) * (L t) ^ 3 := by
      exact mul_le_mul_of_nonneg_left (L_pow3_ge_one t ht) hnon

/-- Digamma bound on the reflected point `1 − s = (1−σ) − i t`: `‖ψ‖ ≤ log(2 + |t|) + 2`. -/
private lemma digamma_bound {σ t : ℝ} (hlo : -(3 / 2 : ℝ) ≤ σ) (hhi : σ ≤ -(1 / 2 : ℝ)) :
    ‖Complex.digamma (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤ Real.log (2 + |t|) + 2 := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hx1 : (1 / 2 : ℝ) ≤ 1 - σ := by linarith
  have hx2 : 1 - σ ≤ 8 := by linarith
  have hmid := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le (1 - σ) (-t) hx1 hx2
  have harg : ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I = 1 - s := by
    dsimp [s]
    apply Complex.ext <;> simp <;> ring
  rw [← harg]
  simpa using hmid

/-- Polynomial-in-`log` digamma bound: `‖ψ (1−s)‖ ≤ 3 L(t)³`. -/
private lemma digamma_poly_bound {σ t : ℝ} (hlo : -(3 / 2 : ℝ) ≤ σ) (hhi : σ ≤ -(1 / 2 : ℝ))
    (ht : (2 : ℝ) ≤ |t|) :
    ‖Complex.digamma (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤ 3 * (L t) ^ 3 := by
  change ‖Complex.digamma (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
    3 * (Real.log (|t| + 3) + 1) ^ 3
  have hb := digamma_bound (σ := σ) (t := t) hlo hhi
  have hlelog : Real.log (2 + |t|) ≤ Real.log (|t| + 3) := by
    apply Real.log_le_log
    · positivity
    · linarith [abs_nonneg t]
  have hX1 : (1 : ℝ) ≤ Real.log (|t| + 3) + 1 := by
    have h : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hX : Real.log (|t| + 3) + 1 ≤ (Real.log (|t| + 3) + 1) ^ 3 := by
    have hp := pow_le_pow_right₀ hX1 (by norm_num : (1 : ℕ) ≤ 3)
    simpa using hp
  calc
    ‖Complex.digamma (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤ Real.log (2 + |t|) + 2 := hb
    _ ≤ Real.log (|t| + 3) + 2 := by linarith
    _ ≤ 3 * (Real.log (|t| + 3) + 1) := by
      have h : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
      linarith
    _ ≤ 3 * (Real.log (|t| + 3) + 1) ^ 3 := by
      exact mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 3)

/-- Imaginary part of the tangent argument `π (1−s)/2`. -/
private lemma tan_arg_im {σ t : ℝ} (s : ℂ) (hsim : s.im = t) :
    (↑Real.pi * (1 - s) / 2).im = -(Real.pi / 2) * t := by
  calc
    (↑Real.pi * (1 - s) / 2).im = -(Real.pi / 2) * s.im := by
      simp [Complex.mul_im]
      ring
    _ = -(Real.pi / 2) * t := by rw [hsim]

/-- `|Im (π(1−s)/2)| = (π/2)·|t|`, and in particular is `≥ 1` for `|t| ≥ 2`. -/
private lemma tan_arg_abs (σ t : ℝ) (ht : (2 : ℝ) ≤ |t|) :
    (1 : ℝ) ≤ |(↑Real.pi * (1 - ((σ : ℂ) + Complex.I * (t : ℂ))) / 2).im| := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsim : s.im = t := by simp [s]
  have hE : |(↑Real.pi * (1 - s) / 2).im| = (Real.pi / 2) * |t| := by
    rw [tan_arg_im (σ := σ) (t := t) s hsim]
    have hpi : 0 < Real.pi / 2 := by positivity
    rw [abs_mul, abs_neg]
    rw [abs_of_pos hpi]
  rw [hE]
  nlinarith [Real.two_le_pi, ht]

/-- `1/‖s−1‖ ≤ 1` on the strip `|t| ≥ 2`. -/
private lemma inv_sub_one_le_one (σ t : ℝ) (ht : (2 : ℝ) ≤ |t|) :
    ‖((σ : ℂ) + Complex.I * (t : ℂ) - 1)⁻¹‖ ≤ 1 := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsim : s.im = t := by simp [s]
  have hs1n : (1 : ℝ) ≤ ‖s - 1‖ := by
    calc
      (1 : ℝ) ≤ |t| / 2 := by linarith
      _ ≤ |t| := by
        have ht0 : 0 ≤ |t| := abs_nonneg t
        linarith
      _ = |(s - 1).im| := by simp [hsim]
      _ ≤ ‖s - 1‖ := abs_im_le_norm (s - 1)
  have hpos : 0 < ‖s - 1‖ := by linarith
  rw [norm_inv]
  exact (inv_le_one₀ hpos).mpr hs1n

/-- The assembled constant is positive. -/
private lemma negstrip_const_pos {M : ℝ} (hM : 0 < M) :
    0 < M + Real.log (2 * Real.pi) + 2 * Real.pi + 4 := by
  have hlog : 0 < Real.log (2 * Real.pi) := Real.log_pos (by nlinarith [Real.two_le_pi])
  linarith [Real.pi_pos]

end Commons.NumberTheory.Zeta
