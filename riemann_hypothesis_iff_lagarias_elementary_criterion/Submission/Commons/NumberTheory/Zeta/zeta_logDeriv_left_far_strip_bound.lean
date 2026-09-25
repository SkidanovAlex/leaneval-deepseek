import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_fe_expanded
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_strip_bound_rh
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_left_strip_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.tan_norm_le_of_abs_im_ge

open Complex Filter Metric Set
open scoped Real Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Zeta

/-!
# The logarithmic derivative of `ζ₁` on the far left strip `−1/2 ≤ Re s ≤ 1/8`

Under the Riemann hypothesis all nontrivial zeros of ζ lie on the critical line `Re s = 1/2`.
On the strip `−1/2 ≤ σ ≤ 1/8` the points `s = σ + i t` with `|t| ≥ 2` are neither zeros of `ζ`
(by the functional equation, a zero would force `ζ(1−s) = 0` with `Re (1−s) ≥ 7/8 > 1/2`,
contradicting RH) nor equal to `1`.  We use the functional equation in logarithmic-derivative
form (`zeta_logDeriv_fe_expanded`),

    ζ'/ζ (s) = log(2π) − ψ(1−s) + (π/2)·tan(π(1−s)/2) − ζ'/ζ (1−s),

bound the reflected term `ζ'/ζ (1−s)` (whose real part lies in `[7/8,3/2]`) by the right-strip
bound `zeta_logDeriv_strip_bound_rh`, bound the gamma/digamma term by `digamma_mid_strip_le`,
and bound the tangent term by `tan_norm_le_of_abs_im_ge` (since
`|Im (π(1−s)/2)| = (π/2)|t| ≥ π ≥ 1`).  Then `logDeriv ζ₁ = logDeriv ζ + 1/(s−1)`
(`zeta1_logDeriv_eq`) lifts the bound to `ζ₁`, the entire function of the statement.
-/

/-- Under RH no zero with real part in `(0, 1/2)`. -/
private lemma zeta_ne_zero_of_rh_lt_half (h : RiemannHypothesis) {s : ℂ}
    (hs0 : (0 : ℝ) < s.re) (hs2 : s.re < (1 / 2 : ℝ)) : riemannZeta s ≠ 0 := by
  intro hz
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    rw [hn] at hs0
    have hre : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
      norm_num
    rw [hre] at hs0
    have hn0 : (0 : ℝ) ≤ n + 1 := by positivity
    nlinarith
  have hs1 : s ≠ 1 := by
    intro h1
    have hs_re : s.re = (1 : ℂ).re := by rw [h1]
    rw [hs_re] at hs2
    norm_num at hs2
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
`im s ≠ 0`, because it vanishes only at real points `s = -2k`. -/
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
    have : -(Real.pi / 2) * s.im ≠ 0 := by
      exact mul_ne_zero (neg_ne_zero.mpr hne) ht
    simpa [Complex.mul_im] using this
  exact hzi_ne hz_im0

/-- `1 - s ≠ 1` is equivalent to `s ≠ 0`. -/
private lemma one_sub_ne_one_iff (s : ℂ) : (1 : ℂ) - s ≠ 1 ↔ s ≠ 0 := by
  constructor
  · intro h hs0
    apply h
    rw [hs0]
    simp
  · intro hs0 h
    apply hs0
    have h2 : (1 : ℂ) - s - 1 = 0 := by rw [h]; simp
    have hs' : -s = 0 := by simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h2
    exact neg_eq_zero.mp hs'

/-- The functional equation `ζ(s) = 2 (2π)^(-(1-s)) Γ(1-s) cos(π(1-s)/2) ζ(1-s)`
at a single point (a specialisation of `riemannZeta_one_sub`). -/
private lemma zeta_fe_point {s : ℂ} (hΓ : ∀ n : ℕ, 1 - s ≠ -↑n) (hs0 : s ≠ 0) :
    riemannZeta s = 2 * (((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - s))) * Gamma (1 - s) *
      cos (↑Real.pi * (1 - s) / 2) * riemannZeta (1 - s) := by
  have hF := riemannZeta_one_sub (s := (1 : ℂ) - s) hΓ ((one_sub_ne_one_iff s).mpr hs0)
  have harg : (1 : ℂ) - ((1 : ℂ) - s) = s := by ring
  rw [harg] at hF
  simpa using hF

/-- Under RH `ζ` has no zeros on the far left strip `Re s ≤ 1/8` away from the real axis:
a non-real zero `s` would force `ζ(1-s) = 0` with `Re (1-s) ≥ 7/8 > 1/2` by the functional
equation, contradicting the Riemann hypothesis. -/
private lemma zeta_ne_zero_of_le_eighth (h : RiemannHypothesis) {s : ℂ}
    (hre : s.re ≤ (1 / 8 : ℝ)) (him : s.im ≠ 0) : riemannZeta s ≠ 0 := by
  intro hz
  have hs0 : s ≠ 0 := by
    intro h0
    exact him (by rw [h0]; simp)
  have hre_w0 : (0 : ℝ) < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hΓ : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := ne_neg_nat_of_re_pos hre_w0
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 :=
    cos_pi_one_sub_two_ne_zero_of_im_ne_zero him
  have hF := zeta_fe_point (s := s) hΓ hs0
  have hprod : 2 * (((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - s))) * Gamma (1 - s) *
      cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) ?_
    · exact Complex.cpow_ne_zero_iff.mpr
        (Or.inl (by exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))))
    · exact Complex.Gamma_ne_zero hΓ
    · exact hcos
  have hζw_zero : riemannZeta (1 - s) = 0 := by
    have h0 : 2 * (((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - s))) * Gamma (1 - s) *
        cos (↑Real.pi * (1 - s) / 2) * riemannZeta (1 - s) = 0 := by
      rw [← hF]; exact hz
    exact (mul_eq_zero.mp h0).resolve_left hprod
  have hre_w : (1 / 2 : ℝ) < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  exact zeta_ne_zero_of_rh_gt_half h hre_w hζw_zero

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
  have hmul := logDeriv_mul (x := s) (f := fun z => z - 1) (g := riemannZeta)
      (sub_ne_zero.mpr hs1) hζs (by fun_prop) (differentiableAt_riemannZeta hs1)
  simp only [Pi.mul_def] at hmul
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

private lemma L_le_pow3 (t : ℝ) (ht : (2 : ℝ) ≤ |t|) : L t ≤ (L t) ^ 3 := by
  have h := pow_le_pow_right₀ (L_ge_one t ht) (by norm_num : (1 : ℕ) ≤ 3)
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
private lemma digamma_bound {σ t : ℝ} (hlo : -(1 / 2 : ℝ) ≤ σ) (hhi : σ ≤ (1 / 8 : ℝ)) :
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
private lemma digamma_poly_bound {σ t : ℝ} (hlo : -(1 / 2 : ℝ) ≤ σ) (hhi : σ ≤ (1 / 8 : ℝ))
    (ht : (2 : ℝ) ≤ |t|) :
    ‖Complex.digamma (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤ 3 * (L t) ^ 3 := by
  change ‖Complex.digamma (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
    3 * (Real.log (|t| + 3) + 1) ^ 3
  have hb := digamma_bound (σ := σ) (t := t) hlo hhi
  have hlelog : Real.log (2 + |t|) ≤ Real.log (|t| + 3) := by
    apply Real.log_le_log
    · positivity
    · linarith [abs_nonneg t]
  have hlg : 0 ≤ Real.log (|t| + 3) := by
    apply Real.log_nonneg
    linarith [abs_nonneg t]
  have hX1 : (1 : ℝ) ≤ Real.log (|t| + 3) + 1 := by nlinarith
  have hX : Real.log (|t| + 3) + 1 ≤ (Real.log (|t| + 3) + 1) ^ 3 := by
    have hp := pow_le_pow_right₀ hX1 (by norm_num : (1 : ℕ) ≤ 3)
    simpa using hp
  calc
    ‖Complex.digamma (1 - ((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤ Real.log (2 + |t|) + 2 := hb
    _ ≤ Real.log (|t| + 3) + 2 := by linarith
    _ ≤ 3 * (Real.log (|t| + 3) + 1) := by nlinarith
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

/-- Polynomial-in-`log` bound for the tangent term `(π/2)·tan u` with `|Im u| ≥ 1`:
`≤ 2π · L(t)³`. -/
private lemma tan_term_poly_bound (u : ℂ) (hu : (1 : ℝ) ≤ |u.im|) {t : ℝ}
    (ht : (2 : ℝ) ≤ |t|) :
    ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan u‖ ≤ 2 * Real.pi * (L t) ^ 3 := by
  have htan : ‖Complex.tan u‖ ≤ 4 :=
    Commons.Analysis.SpecialFunctions.Trigonometric.tan_norm_le_of_abs_im_ge u hu
  calc
    ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan u‖
        = ‖((Real.pi / 2 : ℝ) : ℂ)‖ * ‖Complex.tan u‖ := by
            rw [norm_mul]
    _ = (Real.pi / 2) * ‖Complex.tan u‖ := by
            congr 1
            exact Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    _ ≤ (Real.pi / 2) * 4 := by
            exact mul_le_mul_of_nonneg_left htan (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    _ = 2 * Real.pi := by ring
    _ ≤ 2 * Real.pi * (L t) ^ 3 := by
            simpa using mul_le_mul_of_nonneg_left (L_pow3_ge_one t ht)
              (by positivity : (0 : ℝ) ≤ 2 * Real.pi)

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

/-- The assembled constant `Crh · 729 + log(2π) + 2π + 4` is positive. -/
private lemma zeta_left_main_const_pos {Crh : ℝ} (hCrh : 0 < Crh) :
    0 < Crh * 729 + Real.log (2 * Real.pi) + 2 * Real.pi + 4 := by
  have hlog : 0 < Real.log (2 * Real.pi) := by
    apply Real.log_pos
    nlinarith [Real.two_le_pi]
  nlinarith [hCrh, hlog, Real.pi_pos]

/-- Final bookkeeping: `(… + 3)·L³ + 1 ≤ (… + 4)·L³`, using `1 ≤ L³`. -/
private lemma zeta_left_final_arith {Crh : ℝ} (hCrh : 0 ≤ Crh) {t : ℝ} (ht : (2 : ℝ) ≤ |t|) :
    (Crh * 729 + Real.log (2 * Real.pi) + 3 + 2 * Real.pi) * (L t) ^ 3 + 1 ≤
      (Crh * 729 + Real.log (2 * Real.pi) + 2 * Real.pi + 4) * (L t) ^ 3 := by
  have hL3 : (1 : ℝ) ≤ (L t) ^ 3 := L_pow3_ge_one t ht
  nlinarith

/-- The requested bound for the logarithmic derivative of the entire function `ζ₁`
on the far left strip `−1/2 ≤ σ ≤ 1/8`, `|t| ≥ 2`, assuming the Riemann hypothesis. -/
theorem zeta_logDeriv_left_far_strip_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, -(1/2 : ℝ) ≤ σ → σ ≤ (1/8 : ℝ) → 2 ≤ |t| →
      ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        C * (Real.log (|t| + 3) + 1) ^ 3 := by
  rcases zeta_logDeriv_strip_bound_rh with ⟨Crh, hCrh0, hCrhSpec⟩
  let C : ℝ := Crh * 729 + Real.log (2 * Real.pi) + 2 * Real.pi + 4
  have hCpos : 0 < C := by
    dsimp [C]
    exact zeta_left_main_const_pos hCrh0
  refine ⟨C, hCpos, ?_⟩
  intro σ t hσlo hσhi ht
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  let Lv : ℝ := L t
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have ht_ne : t ≠ 0 := by
    intro ht0
    rw [ht0] at ht
    norm_num at ht
  have hs0 : s ≠ 0 := by
    intro hs0'
    have h : s.im = 0 := by rw [hs0']; simp
    rw [hsim] at h
    exact ht_ne h
  have hs1 : s ≠ 1 := by
    intro hs1'
    have h : s.re = (1 : ℂ).re := congrArg Complex.re hs1'
    rw [hsre] at h
    norm_num at h
    linarith
  have hζs : riemannZeta s ≠ 0 := by
    apply zeta_ne_zero_of_le_eighth h
    · rw [hsre]; exact hσhi
    · rw [hsim]; exact ht_ne
  have hre_w : (1 / 2 : ℝ) < (1 - s).re := by
    have hsub : (1 - s).re = 1 - σ := by
      rw [Complex.sub_re, hsre]
      norm_num
    rw [hsub]
    linarith
  have hζw : riemannZeta (1 - s) ≠ 0 := zeta_ne_zero_of_rh_gt_half h hre_w
  have hre_w0 : (0 : ℝ) < (1 - s).re := by
    have hsub : (1 - s).re = 1 - σ := by
      rw [Complex.sub_re, hsre]
      norm_num
    rw [hsub]
    linarith
  have hΓ : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := ne_neg_nat_of_re_pos hre_w0
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    apply cos_pi_one_sub_two_ne_zero_of_im_ne_zero
    rw [hsim]
    exact ht_ne
  have hFE := zeta_logDeriv_fe_expanded hζs hζw hs0 hs1 hΓ hcos
  -- decompose the right hand side
  have hFE' : deriv riemannZeta s / riemannZeta s =
      Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2) -
          deriv riemannZeta (1 - s) / riemannZeta (1 - s) := by
    simpa using hFE
  have hL1 : (1 : ℝ) ≤ Lv := by
    dsimp [Lv]
    exact L_ge_one t ht
  have hL3 : (1 : ℝ) ≤ Lv ^ 3 := by
    dsimp [Lv]
    exact L_pow3_ge_one t ht
  -- bound the constant term
  have hbnd_log : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ ≤ Real.log (2 * Real.pi) * Lv ^ 3 := by
    rw [norm_log_two_pi]
    dsimp [Lv]
    exact log_two_pi_mul_L3_le t ht
  -- bound the digamma term (reflected)
  have hbnd_dg : ‖Complex.digamma (1 - s)‖ ≤ 3 * Lv ^ 3 := by
    have h := digamma_poly_bound (σ := σ) (t := t) hσlo hσhi ht
    simpa [s, Lv] using h
  -- bound the tangent term
  have hbnd_T : ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤
      2 * Real.pi * Lv ^ 3 := by
    have hu : (1 : ℝ) ≤ |(↑Real.pi * (1 - s) / 2).im| := by
      simpa [s] using (tan_arg_abs σ t ht)
    have h := tan_term_poly_bound (↑Real.pi * (1 - s) / 2) hu ht
    simpa [Lv] using h
  -- bound the reflected ζ'/ζ via the right strip lemma (δ = 1/8)
  have hRdist : (1 / 4 : ℝ) ≤ ‖((1 - σ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ) - 1‖ := by
    have harg : ((1 - σ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ) = 1 - s := by
      dsimp [s]
      apply Complex.ext <;> simp <;> ring
    rw [harg]
    have hsnorm : (2 : ℝ) ≤ ‖s‖ := by
      calc
        (2 : ℝ) ≤ |t| := ht
        _ = |s.im| := by rw [hsim]
        _ ≤ ‖s‖ := abs_im_le_norm s
    have hb : ‖s‖ ≥ (1 / 4 : ℝ) := by linarith
    have hsub : (1 - s - 1) = -s := by ring
    rw [hsub, norm_neg]
    exact hb
  have hRbound := hCrhSpec h (1 / 8) (1 - σ) (-t) (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (1 / 8 : ℝ) ≤ 1) (by linarith : (1 / 2 + 1 / 8 : ℝ) ≤ 1 - σ)
    (by linarith : 1 - σ ≤ 2) hRdist
  have harg_R : ((1 - σ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ) = 1 - s := by
    dsimp [s]
    apply Complex.ext <;> simp <;> ring
  have hRbound' : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤
      Crh * (1 + 1 / (1 / 8)) ^ 3 * (Real.log (|(-t)| + 3) + 1) ^ 3 := by
    rw [harg_R] at hRbound
    exact hRbound
  have hbnd_R : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ Crh * 729 * Lv ^ 3 := by
    have hnum : (1 + 1 / (1 / 8) : ℝ) ^ 3 = 9 ^ 3 := by norm_num
    have h729 : (9 : ℝ) ^ 3 = 729 := by norm_num
    calc
      ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖
          ≤ Crh * (1 + 1 / (1 / 8)) ^ 3 * (Real.log (|(-t)| + 3) + 1) ^ 3 := hRbound'
      _ = Crh * 729 * Lv ^ 3 := by
              rw [hnum, h729]
              have hre : Real.log (|(-t)| + 3) + 1 = Lv := by
                dsimp [Lv, L]
                simp
              rw [hre]
  -- assemble the ζ'/ζ bound
  have hnorm_main : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      (Crh * 729 + Real.log (2 * Real.pi) + 3 + 2 * Real.pi) * Lv ^ 3 := by
    calc
      ‖deriv riemannZeta s / riemannZeta s‖
          = ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
              ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2) -
                deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := by
              rw [hFE']
      _ ≤ ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 - s)‖ +
          ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
            ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := by
              have h1 : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
                  ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2) -
                    deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤
                  ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 - s)‖ +
                  ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
                    ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := by
                    have hs1 : ‖(Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
                        ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)) -
                          deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤
                        ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
                          ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ +
                            ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := by
                          simpa [sub_eq_add_neg] using
                            (norm_add_le (Complex.log ((2 * Real.pi : ℝ) : ℂ) -
                              Complex.digamma (1 - s) +
                                ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2))
                              (-(deriv riemannZeta (1 - s) / riemannZeta (1 - s))))
                    have hs2 : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
                          ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ ≤
                        ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s)‖ +
                          ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2)‖ := by
                          exact norm_add_le (Complex.log ((2 * Real.pi : ℝ) : ℂ) -
                            Complex.digamma (1 - s))
                            (((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2))
                    have hs3 : ‖Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s)‖ ≤
                        ‖Complex.log ((2 * Real.pi : ℝ) : ℂ)‖ + ‖Complex.digamma (1 - s)‖ := by
                          simpa [sub_eq_add_neg] using
                            (norm_add_le (Complex.log ((2 * Real.pi : ℝ) : ℂ))
                              (-Complex.digamma (1 - s)))
                    linarith
              exact h1
      _ ≤ Real.log (2 * Real.pi) * Lv ^ 3 + 3 * Lv ^ 3 + 2 * Real.pi * Lv ^ 3 +
            Crh * 729 * Lv ^ 3 := by
              exact add_le_add (add_le_add (add_le_add hbnd_log hbnd_dg) hbnd_T) hbnd_R
      _ = (Crh * 729 + Real.log (2 * Real.pi) + 3 + 2 * Real.pi) * Lv ^ 3 := by ring
  -- lift to ζ₁
  have hζ1main : ‖logDeriv riemannZeta₁ s‖ ≤ C * Lv ^ 3 := by
    have hle1 := norm_zeta1_logDeriv_le s hs1 hζs
    have hinv : ‖(s - 1)⁻¹‖ ≤ 1 := by
      simpa [s] using (inv_sub_one_le_one σ t ht)
    have hpre : ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ ≤
        (Crh * 729 + Real.log (2 * Real.pi) + 3 + 2 * Real.pi) * Lv ^ 3 + 1 := by
      exact add_le_add hnorm_main hinv
    calc
      ‖logDeriv riemannZeta₁ s‖ ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := hle1
      _ ≤ (Crh * 729 + Real.log (2 * Real.pi) + 3 + 2 * Real.pi) * Lv ^ 3 + 1 := hpre
      _ ≤ C * Lv ^ 3 := by
        dsimp [C, Lv]
        nlinarith only [L_pow3_ge_one t ht]
  have hgoal : ‖logDeriv riemannZeta₁ (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
      C * (Real.log (|t| + 3) + 1) ^ 3 := by
    change ‖logDeriv riemannZeta₁ s‖ ≤ C * (Real.log (|t| + 3) + 1) ^ 3
    change ‖logDeriv riemannZeta₁ s‖ ≤ C * Lv ^ 3
    exact hζ1main
  exact hgoal

end Commons.NumberTheory.Zeta
