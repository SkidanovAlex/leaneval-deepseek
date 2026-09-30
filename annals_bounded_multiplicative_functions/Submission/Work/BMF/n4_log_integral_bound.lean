import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The principal term of the `[P,2P]` prime-character sum

For `P ≥ 4` and every real `t`,
`‖∫_P^{2P} v^{it} / log v dv‖ ≤ 8 · π₀(P)/(1+|t|)`, where `π₀(P) = P/log P`.

The proof is one integration by parts.  With `u(v) = v^{1+it}/(1+it)` (an antiderivative of
`v^{it}`) and `w(v) = 1/log v` one gets

`∫_P^{2P} v^{it}/log v dv = [u w]_P^{2P} - ∫_P^{2P} u w'`,

where `w'(v) = -1/(v (log v)²)`.  The boundary term is `O(π₀(P)/|1+it|)` and the remainder
integral has pointwise norm `|v^{1+it}/(1+it)| /(v (log v)²) = 1/(|1+it| (log v)²)`, hence is
`O(P/(log P)²/|1+it|)`.  Since `1/|1+it| ≤ 2/(1+|t|)` and both `P/log P` and `P/(log P)²` are
`≤ π₀(P)` for `P ≥ 4`, the claim follows with the explicit constant `8`.

The elementary facts used throughout are `‖v^{1+it}‖ = v`, `‖v^{it}‖ = 1` for `v > 0`
(`Complex.norm_cpow_eq_rpow_re_of_pos`) and the linear lower bound `(1+|t|)/2 ≤ ‖1 + it‖`.
-/

open Real Complex
open MeasureTheory intervalIntegral

namespace Work.BMF

/-- `‖v ^ (I t + 1)‖ = v` for positive real `v`. -/
lemma n4_norm_cpow_I_add_one (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖(x:ℂ)^(Complex.I*(t:ℂ)+1)‖ = x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have h : (Complex.I*(t:ℂ)+1).re = 1 := by simp
  rw [h, Real.rpow_one]

/-- `‖v ^ (I t)‖ = 1` for positive real `v`. -/
lemma n4_norm_cpow_I (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖(x:ℂ)^(Complex.I*(t:ℂ))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have h : (Complex.I*(t:ℂ)).re = 0 := by simp
  rw [h, Real.rpow_zero]

/-- The linear lower bound `(1 + |t|)/2 ≤ ‖1 + I t‖`. -/
lemma n4_half_one_add_abs_le_norm (t : ℝ) :
    (1 + |t|)/2 ≤ ‖Complex.I*(t:ℂ)+1‖ := by
  have h1 : (1:ℝ) ≤ ‖Complex.I*(t:ℂ)+1‖ := by
    have h := Complex.abs_re_le_norm (Complex.I*(t:ℂ)+1)
    have hre : (Complex.I*(t:ℂ)+1).re = 1 := by simp
    rw [hre] at h
    simpa using h
  have h2 : |t| ≤ ‖Complex.I*(t:ℂ)+1‖ := by
    have h := Complex.abs_im_le_norm (Complex.I*(t:ℂ)+1)
    have him : (Complex.I*(t:ℂ)+1).im = t := by simp
    rw [him] at h
    simpa using h
  rcases le_total (|t|) 1 with h | h
  · linarith
  · linarith

/-- `1 + I t ≠ 0`. -/
lemma n4_one_add_I_mul_ne_zero (t : ℝ) : Complex.I*(t:ℂ)+1 ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  simp at h1

/-- The inverse norm bound `1/‖1 + I t‖ ≤ 2/(1+|t|)`. -/
lemma n4_inv_norm_one_add_I_mul_le (t : ℝ) : 1/‖Complex.I*(t:ℂ)+1‖ ≤ 2/(1+|t|) := by
  have h2 : 0 < (1+|t|)/2 := by positivity
  calc 1 / ‖Complex.I*(t:ℂ)+1‖ ≤ 1/((1+|t|)/2) :=
        one_div_le_one_div_of_le h2 (n4_half_one_add_abs_le_norm t)
    _ = 2/(1+|t|) := by field_simp

/-- Endpoint bound for one term of the integration by parts: for real `x ≥ 2` and any real `t`,
`‖x ^ (1 + I t) / ((1 + I t) log x)‖ ≤ 2/(1+|t|) · x/log x`. -/
lemma n4_boundary_bound (t : ℝ) {x : ℝ} (hx : 2 ≤ x) :
    ‖(x:ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)/(Real.log x : ℂ)‖
      ≤ 2/(1+|t|) * (x / Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hxn : 0 ≤ x / Real.log x := div_nonneg hx0.le hlog.le
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog,
    n4_norm_cpow_I_add_one t hx0]
  calc x / ‖Complex.I*(t:ℂ)+1‖ / Real.log x
      = (x / Real.log x) * (1/‖Complex.I*(t:ℂ)+1‖) := by field_simp
    _ ≤ (x / Real.log x) * (2/(1+|t|)) :=
        mul_le_mul_of_nonneg_left (n4_inv_norm_one_add_I_mul_le t) hxn
    _ = 2/(1+|t|) * (x/Real.log x) := by ring

/-- Pointwise norm of the remainder integrand of the integration by parts. -/
lemma n4_norm_remainder_integrand (t : ℝ) {v : ℝ} (hv : 2 ≤ v) :
    ‖((v:ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)) * (-(1/((v:ℂ)*(Real.log v:ℂ)^2)))‖
      = 1/(‖Complex.I*(t:ℂ)+1‖ * (Real.log v)^2) := by
  have hv0 : 0 < v := by linarith
  have hlog : 0 < Real.log v := Real.log_pos (by linarith)
  simp only [norm_mul, norm_div, norm_neg, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hv0, abs_of_pos hlog, n4_norm_cpow_I_add_one t hv0]
  field_simp

/-- Bound for the remainder term of the integration by parts: for real `P ≥ 2` and any real `t`,
`‖∫_P^{2P} v^{1+It}/((1+It)) · (-1/(v (log v)²)) dv‖ ≤ 2/(1+|t|) · P/(log P)²`. -/
lemma n4_remainder_bound (t : ℝ) {P : ℝ} (hP : 2 ≤ P) :
    ‖∫ v in P..(2*P),
        ((v:ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)) * (-(1/((v:ℂ)*(Real.log v:ℂ)^2)))‖
      ≤ 2/(1+|t|) * (P/(Real.log P)^2) := by
  have hP0 : 0 < P := by linarith
  have hPle : P ≤ 2*P := by linarith
  have hlog : 0 < Real.log P := Real.log_pos (by linarith)
  have hcnorm : 0 < ‖Complex.I*(t:ℂ)+1‖ := norm_pos_iff.mpr (n4_one_add_I_mul_ne_zero t)
  have hbound : ∀ v ∈ Set.uIoc P (2*P),
      ‖((v:ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)) * (-(1/((v:ℂ)*(Real.log v:ℂ)^2)))‖
        ≤ 1/(‖Complex.I*(t:ℂ)+1‖ * (Real.log P)^2) := by
    intro v hv
    rw [Set.uIoc_of_le hPle] at hv
    have hvP : P < v := hv.1
    have hv2 : 2 ≤ v := by linarith
    rw [n4_norm_remainder_integrand t hv2]
    apply one_div_le_one_div_of_le
    · exact mul_pos hcnorm (pow_pos hlog 2)
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlog.le (Real.log_le_log hP0 (le_of_lt hvP)) 2) hcnorm.le
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hlen : |2*P - P| = P := by rw [show 2*P - P = P by ring, abs_of_pos hP0]
  rw [hlen] at hmain
  refine hmain.trans ?_
  have hPL : 0 ≤ P/(Real.log P)^2 := div_nonneg hP0.le (by positivity)
  calc 1/(‖Complex.I*(t:ℂ)+1‖ * (Real.log P)^2) * P
      = (P/(Real.log P)^2) * (1/‖Complex.I*(t:ℂ)+1‖) := by field_simp
    _ ≤ (P/(Real.log P)^2) * (2/(1+|t|)) :=
        mul_le_mul_of_nonneg_left (n4_inv_norm_one_add_I_mul_le t) hPL
    _ = 2/(1+|t|) * (P/(Real.log P)^2) := by ring

/-- **Integration by parts**: for `P ≥ 2` and real `t`,
`∫_P^{2P} v^{It}/log v dv = [v^{1+It}/((1+It) log v)]_P^{2P} - ∫_P^{2P} v^{1+It}/(1+It)·(-1/(v (log v)²))`. -/
lemma n4_log_integral_ibp (t : ℝ) {P : ℝ} (hP : 2 ≤ P) :
    ∫ x in P..(2*P), (x:ℂ)^(Complex.I*(t:ℂ)) / (Real.log x : ℂ)
      = ((2*P : ℝ) : ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)/(Real.log (2*P) : ℂ)
        - (P:ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)/(Real.log P : ℂ)
        - ∫ x in P..(2*P), ((x:ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)) * (-(1/((x:ℂ)*(Real.log x:ℂ)^2))) := by
  have hr : Complex.I*(t:ℂ) ≠ -1 := by
    intro h
    have h1 := congrArg Complex.re h
    simp at h1
  set u : ℝ → ℂ := fun x => (x:ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1) with hu_def
  set u' : ℝ → ℂ := fun x => (x:ℂ)^(Complex.I*(t:ℂ)) with hu'_def
  set w : ℝ → ℂ := fun x => ((Real.log x : ℂ))⁻¹ with hw_def
  set w' : ℝ → ℂ := fun x => -(1/((x:ℂ)*(Real.log x:ℂ)^2)) with hw'_def
  have hPle : P ≤ 2*P := by linarith
  have hmems : ∀ x ∈ Set.uIcc P (2*P), 2 ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hPle] at hx
    linarith [hx.1]
  have hu : ∀ x ∈ Set.uIcc P (2*P), HasDerivAt u (u' x) x := by
    intro x hx
    have hx2 : 2 ≤ x := hmems x hx
    have hx0 : x ≠ 0 := by linarith
    rw [hu_def, hu'_def]
    exact hasDerivAt_ofReal_cpow_const' hx0 hr
  have hw : ∀ x ∈ Set.uIcc P (2*P), HasDerivAt w (w' x) x := by
    intro x hx
    have hx2 : 2 ≤ x := hmems x hx
    have hx1 : 1 < x := by linarith
    have hx0 : x ≠ 0 := by linarith
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    rw [hw_def, hw'_def]
    have h1 : HasDerivAt (fun y : ℝ => ((Real.log y : ℂ))) ((x:ℂ)⁻¹) x := by
      have h := (Real.hasDerivAt_log hx0).ofReal_comp
      convert h using 1
      push_cast
      ring
    have h2 := h1.inv (by simpa using hlog)
    convert h2 using 1
    field_simp
  have hiu' : IntervalIntegrable u' volume P (2*P) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx2 : 2 ≤ x := hmems x hx
    rw [hu'_def]
    exact (Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (by linarith : x ≠ 0))).continuousWithinAt
  have hiw' : IntervalIntegrable w' volume P (2*P) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx2 : 2 ≤ x := hmems x hx
    have hx1 : 1 < x := by linarith
    rw [hw'_def]
    have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast (by linarith : x ≠ 0)
    have hlog : (Real.log x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Real.log_pos hx1)
    have hxcw : ContinuousWithinAt (fun x : ℝ => (x:ℂ)) (Set.uIcc P (2*P)) x :=
      Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt continuousWithinAt_id
    have hlcw : ContinuousWithinAt (fun x : ℝ => ((Real.log x : ℂ))) (Set.uIcc P (2*P)) x :=
      Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        ((Real.continuousAt_log (by linarith : x ≠ 0)).continuousWithinAt)
    exact ContinuousWithinAt.neg ((continuousWithinAt_const (x := x)).div
      (hxcw.mul (hlcw.pow 2)) (by simp [hx0, hlog]))
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hw hiu' hiw'
  have hgoal : ∫ x in P..(2*P), (x:ℂ)^(Complex.I*(t:ℂ)) / (Real.log x : ℂ)
      = ∫ x in P..(2*P), u' x * w x := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [hu'_def, hw_def, div_eq_mul_inv]
  rw [hgoal]
  have key2 : ∫ x in P..(2*P), u' x * w x
      = u (2*P) * w (2*P) - u P * w P - ∫ x in P..(2*P), u x * w' x := by
    rw [key]; ring
  rw [key2]
  simp only [hu_def, hw_def, hw'_def]
  push_cast
  ring_nf

/-- **The principal term of the `[P,2P]` prime-character sum.**  For `P ≥ 2` and every real `t`,
`‖∫_P^{2P} v^{it} / log v dv‖ ≤ C π₀(P)/(1+|t|)`, where `π₀(P) = P/log P`
(`Work.BMF.pi0` is defined in `Submission.Work.BMF.Defs`).

The proof is two integrations by parts: the antiderivative of `v^{it}` is `v^{1+it}/(1+it)`, so
the integral is `[v^{1+it}/((1+it) log v)]_P^{2P}` plus a term `∫ v^{it}/(log v)² dv` which is
`O(π₀(P))`; for `|t| ≤ 1` one instead uses the trivial bound `∫_P^{2P} dv/log v ≤ C π₀(P)`. -/
theorem n4_log_integral_bound : ∃ C P₀ : ℝ, 0 < C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → ∀ t : ℝ,
    ‖∫ v in P..(2 * P), (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℂ))‖
      ≤ C * pi0 P / (1 + |t|) := by
  refine ⟨8, 4, by norm_num, by norm_num, ?_⟩
  intro P hP t
  have hP0 : 0 < P := by linarith
  have hP2 : 2 ≤ P := by linarith
  have hPle : P ≤ 2*P := by linarith
  have hlog : 0 < Real.log P := Real.log_pos (by linarith)
  have hlog1 : 1 ≤ Real.log P := by
    have h4 : Real.log 4 ≤ Real.log P := Real.log_le_log (by norm_num) hP
    have h41 : (1:ℝ) < Real.log 4 := by
      have h : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
        push_cast
        ring
      have h2 := Real.log_two_gt_d9
      nlinarith
    linarith
  have hlog2P : Real.log P ≤ Real.log (2*P) := Real.log_le_log hP0 (by linarith)
  have hb1 := n4_boundary_bound t (x := 2*P) (by linarith : 2 ≤ 2*P)
  have hb2 := n4_boundary_bound t (x := P) hP2
  have hrem := n4_remainder_bound t hP2
  -- triangle inequality applied to the integration-by-parts identity
  have htri : ‖∫ v in P..(2*P), (v:ℂ)^(Complex.I*(t:ℂ))/(Real.log v : ℂ)‖
      ≤ ‖((2*P : ℝ) : ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)/(Real.log (2*P) : ℂ)‖
        + ‖(P : ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)/(Real.log P : ℂ)‖
        + ‖∫ v in P..(2*P),
            ((v:ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)) * (-(1/((v:ℂ)*(Real.log v:ℂ)^2)))‖ := by
    rw [n4_log_integral_ibp t hP2]
    have h1 := norm_sub_le
      ((((2*P : ℝ) : ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)/(Real.log (2*P) : ℂ)
        - (P : ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)/(Real.log P : ℂ)))
      (∫ v in P..(2*P),
        ((v:ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)) * (-(1/((v:ℂ)*(Real.log v:ℂ)^2))))
    have h2 := norm_sub_le
      (((2*P : ℝ) : ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)/(Real.log (2*P) : ℂ))
      ((P : ℂ)^(Complex.I*(t:ℂ)+1)/(Complex.I*(t:ℂ)+1)/(Real.log P : ℂ))
    linarith
  have hkey : ‖∫ v in P..(2*P), (v:ℂ)^(Complex.I*(t:ℂ))/(Real.log v : ℂ)‖
      ≤ 2/(1+|t|) * ((2*P)/Real.log (2*P)) + 2/(1+|t|) * (P/Real.log P)
        + 2/(1+|t|) * (P/(Real.log P)^2) := by
    linarith [htri, hb1, hb2, hrem]
  have hsum : (2*P)/Real.log (2*P) + P/Real.log P + P/(Real.log P)^2 ≤ 4*(P/Real.log P) := by
    have hA : (2*P)/Real.log (2*P) ≤ 2*(P/Real.log P) := by
      have hone : 1/Real.log (2*P) ≤ 1/Real.log P := one_div_le_one_div_of_le hlog hlog2P
      calc (2*P)/Real.log (2*P) = (2*P) * (1/Real.log (2*P)) := by rw [div_eq_mul_one_div]
        _ ≤ (2*P) * (1/Real.log P) := mul_le_mul_of_nonneg_left hone (by linarith)
        _ = 2*(P/Real.log P) := by ring
    have hB : P/(Real.log P)^2 ≤ P/Real.log P := by
      have hu : 0 ≤ P/Real.log P := div_nonneg hP0.le hlog.le
      have h1L : 1/Real.log P ≤ 1 := by
        simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hlog1
      calc P/(Real.log P)^2 = (P/Real.log P)*(1/Real.log P) := by field_simp
        _ ≤ (P/Real.log P)*1 := mul_le_mul_of_nonneg_left h1L hu
        _ = P/Real.log P := by ring
    linarith
  calc ‖∫ v in P..(2*P), (v:ℂ)^(Complex.I*(t:ℂ))/(Real.log v : ℂ)‖
      ≤ 2/(1+|t|) * ((2*P)/Real.log (2*P)) + 2/(1+|t|) * (P/Real.log P)
        + 2/(1+|t|) * (P/(Real.log P)^2) := hkey
    _ = 2/(1+|t|) * ((2*P)/Real.log (2*P) + P/Real.log P + P/(Real.log P)^2) := by ring
    _ ≤ 2/(1+|t|) * (4*(P/Real.log P)) := by
        apply mul_le_mul_of_nonneg_left hsum
        positivity
    _ = 8 * pi0 P / (1+|t|) := by rw [pi0]; ring

end Work.BMF
