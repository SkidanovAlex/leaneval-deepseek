import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_re_neg_half_bound
import Submission.Commons.Analysis.Integral.integral_inv_sqrt_quarter_add_sq_le

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! ## Auxiliary facts about the left edge `Re s = -1/2` -/

/-- The value of `Gammaℝ` at `-1/2 + it` is never zero. -/
private lemma GammaR_leftEdge_ne_zero (t : ℝ) :
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

/-- The gamma factor of a Dirichlet character does not vanish at `-1/2 + it`. -/
private lemma gammaFactor_leftEdge_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (t : ℝ) :
    gammaFactor χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [hE.gammaFactor_def]
    exact GammaR_leftEdge_ne_zero t
  · rw [hO.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, Complex.one_re]
    norm_num

/-- `N = 1` forces `χ = 1`. -/
private lemma eq_one_of_eq_one {N : ℕ} (χ : DirichletCharacter ℂ N) (h : N = 1) : χ = 1 := by
  subst h
  exact Subsingleton.elim χ 1

/-- **Non-vanishing of `L(χ, ·)` on the vertical line `Re s = -1/2`.** -/
lemma LFunction_ne_zero_of_re_eq_neg_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (t : ℝ) :
    DirichletCharacter.LFunction χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  have hN1 : N ≠ 1 := fun h => hχ (eq_one_of_eq_one χ h)
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = -(1 / 2 : ℝ) := by
    rw [hs]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one]
    norm_num
  intro hL
  have hγ : gammaFactor χ s ≠ 0 := by
    rw [hs]
    exact gammaFactor_leftEdge_ne_zero χ t
  have hdiv : DirichletCharacter.LFunction χ s =
      DirichletCharacter.completedLFunction χ s / gammaFactor χ s :=
    DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1)
  have hΛ : DirichletCharacter.completedLFunction χ s = 0 := by
    have h : DirichletCharacter.completedLFunction χ s / gammaFactor χ s = 0 := by
      rw [← hdiv]; exact hL
    have := congrArg (fun z : ℂ => z * gammaFactor χ s) h
    rw [div_mul_cancel₀ _ hγ, zero_mul] at this
    exact this
  have hstrip := zerosInStrip χ hχ hχprim s hΛ
  rw [hsre] at hstrip
  linarith [hstrip.1]

/-! ## The integrand is continuous -/

private lemma norm_leftEdge (t : ℝ) :
    ‖(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = Real.sqrt (1 / 4 + t ^ 2) := by
  have hns : Complex.normSq (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 1 / 4 + t ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      add_zero]
    ring
  rw [← hns, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

lemma continuous_logDeriv_LFunction_of_re_eq_neg_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    Continuous (fun t : ℝ => logDeriv (DirichletCharacter.LFunction χ)
      (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  have hd : Differentiable ℂ (DirichletCharacter.LFunction χ) := differentiable_LFunction hχ
  have hline : Continuous (fun t : ℝ => (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    fun_prop
  have hnum : Continuous (fun t : ℝ =>
      deriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    hd.deriv.continuous.comp hline
  have hden : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    hd.continuous.comp hline
  have hne : ∀ t : ℝ,
      DirichletCharacter.LFunction χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    fun t => LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim t
  have hq : Continuous (fun t : ℝ =>
      deriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    convert hnum.div hden hne using 1
  simpa only [logDeriv_apply] using hq

private lemma continuous_leftEdge_integrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    Continuous (fun t : ℝ => ‖logDeriv (DirichletCharacter.LFunction χ)
        (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
      ‖(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) := by
  have hnum := (continuous_logDeriv_LFunction_of_re_eq_neg_half χ hχ hχprim).norm
  have hden : Continuous (fun t : ℝ => ‖(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) := by
    fun_prop
  have hne : ∀ t : ℝ, ‖(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≠ 0 := by
    intro t h
    have h0 : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := norm_eq_zero.mp h
    have hre : ((((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re = -(1 / 2 : ℝ) := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one]
      norm_num
    rw [h0] at hre
    simp at hre
  convert hnum.div hden hne using 1

/-! ## The main bound -/

/-- **Bound for the logarithmic derivative of `L(·,χ)` on the vertical line `Re s = -1/2`.**

For a primitive non-trivial character `χ mod N` there is `C > 0` with, for all `T ≥ 2`,
`∫_{-T}^{T} ‖(L'/L)(-1/2 + it)‖ / ‖-1/2 + it‖ dt ≤ C (log (N (T+3)))²`.

Proof sketch: use the functional equation for the completed L-function to relate
`logDeriv Λ(χ)(s)` at `Re s = -1/2` to `logDeriv Λ(χ⁻¹)(1-s)` at `Re = 3/2`; bound the
latter by the absolutely convergent Dirichlet series plus the gamma-factor log-derivative
(elementary digamma bounds in `Re ≥ 1/2`, with the shift `ψ(z+1) = ψ(z) + 1/z` to reach
negative real parts); the weight `1/‖s‖` turns the resulting `log (2+|t|)` bound into
`log²`. -/
theorem leftEdge_logDeriv_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (∫ t : ℝ in -T..T, ‖logDeriv (DirichletCharacter.LFunction χ)
          (((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
        ‖(((-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) ≤
        C * (Real.log (N * (T + 3))) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := logDeriv_LFunction_re_neg_half_bound χ hχ hχprim
  refine ⟨18 * C₀, by positivity, ?_⟩
  intro T hT
  have hTpos : 0 < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set K : ℝ := Real.log ((N : ℝ) * (T + 3)) with hK
  have hK1 : 1 ≤ K := by
    rw [hK, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have h3 : (3 : ℝ) ≤ T + 3 := by linarith
    calc Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
      _ ≤ (N : ℝ) * (T + 3) := by nlinarith [hN1, h3]
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  suffices hmain : (∫ t : ℝ in -T..T, ‖logDeriv (DirichletCharacter.LFunction χ)
        (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
      ‖(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) ≤ (18 * C₀) * K ^ 2 by
    simpa only [hK] using hmain
  -- pointwise bound for the integrand
  have hpoint : ∀ t : ℝ, t ∈ Set.Icc (-T) T →
      ‖logDeriv (DirichletCharacter.LFunction χ)
          (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
        ‖(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (3 * C₀ * K) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹ := by
    intro t ht
    have htabs : |t| ≤ T := by
      rw [abs_le]; exact ⟨ht.1, ht.2⟩
    have hb : ‖logDeriv (DirichletCharacter.LFunction χ)
        (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C₀ * (Real.log (N : ℝ) + Real.log (2 + |t|) + 1) := by
      have h := hC₀ t
      have hpt : ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
          (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by norm_num
      rwa [hpt] at h
    have hA : Real.log (N : ℝ) + Real.log (2 + |t|) + 1 ≤ 3 * K := by
      have h1 : Real.log (N : ℝ) ≤ K := by
        rw [hK]
        apply Real.log_le_log (by positivity)
        nlinarith [hN1, hTpos]
      have h2 : Real.log (2 + |t|) ≤ K := by
        rw [hK]
        apply Real.log_le_log (by linarith [abs_nonneg t])
        have h3 : (2 : ℝ) + |t| ≤ T + 3 := by linarith
        have h4 : T + 3 ≤ (N : ℝ) * (T + 3) := by nlinarith [hN1, hTpos]
        linarith
      linarith
    rw [div_eq_mul_inv, norm_leftEdge t]
    calc ‖logDeriv (DirichletCharacter.LFunction χ)
            (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * (Real.sqrt (1 / 4 + t ^ 2))⁻¹
        ≤ (C₀ * (Real.log (N : ℝ) + Real.log (2 + |t|) + 1)) *
            (Real.sqrt (1 / 4 + t ^ 2))⁻¹ :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ ≤ (C₀ * (3 * K)) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (le_of_lt hC₀pos))
            (by positivity)
      _ = (3 * C₀ * K) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹ := by ring
  -- integrability of the two sides
  have hFint : IntervalIntegrable (fun t : ℝ => ‖logDeriv (DirichletCharacter.LFunction χ)
      (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
      ‖(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) MeasureTheory.volume (-T) T :=
    (continuous_leftEdge_integrand χ hχ hχprim).intervalIntegrable _ _
  have hGcont : Continuous (fun t : ℝ => (3 * C₀ * K) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹) := by
    apply Continuous.const_mul
    apply Continuous.inv₀
    · exact Real.continuous_sqrt.comp (by fun_prop)
    · intro t
      exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hGint : IntervalIntegrable
      (fun t : ℝ => (3 * C₀ * K) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹) MeasureTheory.volume (-T) T :=
    hGcont.intervalIntegrable _ _
  have hstep1 : (∫ t : ℝ in -T..T, ‖logDeriv (DirichletCharacter.LFunction χ)
        (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
      ‖(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      ∫ t : ℝ in -T..T, (3 * C₀ * K) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹ :=
    intervalIntegral.integral_mono_on (by linarith) hFint hGint hpoint
  have hweight := Commons.Analysis.Integral.integral_inv_sqrt_quarter_add_sq_le T hT1
  have hstep2 : (∫ t : ℝ in -T..T, (3 * C₀ * K) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹) =
      (3 * C₀ * K) * (∫ t : ℝ in -T..T, (Real.sqrt (1 / 4 + t ^ 2))⁻¹) :=
    intervalIntegral.integral_const_mul _ _
  have hstep3 : (∫ t : ℝ in -T..T, (3 * C₀ * K) * (Real.sqrt (1 / 4 + t ^ 2))⁻¹) ≤
      (3 * C₀ * K) * (4 + 2 * Real.log T) := by
    rw [hstep2]
    exact mul_le_mul_of_nonneg_left hweight (by positivity)
  have hstep4 : (3 * C₀ * K) * (4 + 2 * Real.log T) ≤ (18 * C₀) * K ^ 2 := by
    have hlogT : Real.log T ≤ K := by
      rw [hK]
      apply Real.log_le_log hTpos
      nlinarith [hN1, hTpos]
    have h4 : 4 + 2 * Real.log T ≤ 6 * K := by linarith
    have hmul := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 3 * C₀ * K)
    have heq : (3 * C₀ * K) * (6 * K) = (18 * C₀) * K ^ 2 := by ring
    linarith [hmul, heq]
  linarith [hstep1, hstep3, hstep4]

end Commons.NumberTheory.DirichletCharacter
