import Mathlib
import Submission.Commons.NumberTheory.Mertens.mertens_lower

namespace Commons.NumberTheory.Mertens

open Real MeasureTheory

/-! # Difference of the first-Mertens remainders over `[x, X]`

`primeRecips_loglog_diff`: for `2 ≤ x ≤ X` and any real `B₁`,

```
(∑_{p≤X} 1/p − log log X) − (∑_{p≤x} 1/p − log log x)
  = ((logDiv X − log X − B₁)/log X − (logDiv x − log x − B₁)/log x)
    + ∫_x^X (logDiv t − log t − B₁)/(t (log t)²) dt
```

The proof is a direct consequence of the second Abel identity
`primeRecips_eq_logDiv_div_log_add_integral`, the splitting of the interval of
integration at `x`, and the two elementary integrals
`∫ t⁻¹/log t = log log X − log log x` and
`∫ t⁻¹/(log t)² = 1/log x − 1/log X`; the constant `B₁` cancels between the
boundary terms and the integral.
-/

/-- In `uIcc a b` with `2 ≤ a ≤ b`, every point is at least `2`. -/
private lemma uIcc_two_le_of_le {a b t : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (ht : t ∈ Set.uIcc a b) : 2 ≤ t := by
  rw [Set.uIcc_of_le hab] at ht
  exact le_trans ha ht.1

/-- `t⁻¹ / log t` is interval-integrable on `[a, b]` when `2 ≤ a ≤ b`. -/
private lemma intervalIntegrable_inv_div_log_ge {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  have hz2 : 2 ≤ z := uIcc_two_le_of_le ha hab hz
  have hz0 : z ≠ 0 := by linarith
  have hlog : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz2]
  fun_prop (disch := positivity)

/-- `t⁻¹ / (log t) ^ 2` is interval-integrable on `[a, b]` when `2 ≤ a ≤ b`. -/
private lemma intervalIntegrable_inv_div_log_sq_ge {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  have hz2 : 2 ≤ z := uIcc_two_le_of_le ha hab hz
  have hz0 : z ≠ 0 := by linarith
  have hlog : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz2]
  fun_prop (disch := positivity)

/-- Pointwise decomposition of the integrand (valid when `t ≠ 0 ≠ log t`):
`(logDiv − log − B)/(t log²t) = logDiv/(t log²t) − t⁻¹/log t − B·(t⁻¹/log²t)`. -/
private lemma integrand_split {t B : ℝ} (ht0 : t ≠ 0) (hlog : Real.log t ≠ 0) :
    (logDiv t - Real.log t - B) / (t * (Real.log t) ^ 2) =
      logDiv t / (t * (Real.log t) ^ 2) - t⁻¹ / Real.log t -
        B * (t⁻¹ / (Real.log t) ^ 2) := by
  field_simp [ht0, hlog]

/-- Difference of the two Abel-identity boundary terms on `[x, X]`. -/
private lemma bound_split {x X B₁ : ℝ} (hlogx : Real.log x ≠ 0) (hlogX : Real.log X ≠ 0) :
    ((logDiv X - Real.log X - B₁) / Real.log X -
        (logDiv x - Real.log x - B₁) / Real.log x) =
      logDiv X / Real.log X - logDiv x / Real.log x -
        B₁ / Real.log X + B₁ / Real.log x := by
  field_simp [hlogx, hlogX]
  ring

theorem primeRecips_loglog_diff {x X B₁ : ℝ} (h2x : 2 ≤ x) (hxX : x ≤ X) :
    (Commons.NumberTheory.Mertens.primeRecips X - Real.log (Real.log X)) -
        (Commons.NumberTheory.Mertens.primeRecips x - Real.log (Real.log x)) =
      ((Commons.NumberTheory.Mertens.logDiv X - Real.log X - B₁) / Real.log X -
        (Commons.NumberTheory.Mertens.logDiv x - Real.log x - B₁) / Real.log x) +
          (∫ t in x..X, (Commons.NumberTheory.Mertens.logDiv t - Real.log t - B₁) /
            (t * (Real.log t) ^ 2)) := by
  have h2X : 2 ≤ X := le_trans h2x hxX
  have hx1 : (1 : ℝ) < x := by linarith
  have hX1 : (1 : ℝ) < X := lt_of_lt_of_le hx1 hxX
  have hlogx_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  have hlogX_ne : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX1)
  -- integral certificates on [2,x] and [x,X]
  have hF_int_xX : IntervalIntegrable (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2)) volume x X :=
    intervalIntegrable_logDiv_div_id_log_sq_gen h2x hxX
  have hF_int_2x : IntervalIntegrable (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2)) volume 2 x :=
    intervalIntegrable_logDiv_div_id_log_sq_gen (by norm_num : (2 : ℝ) ≤ 2) h2x
  have hF_split : (∫ t in 2..X, logDiv t / (t * (Real.log t) ^ 2)) =
      (∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2)) +
        (∫ t in x..X, logDiv t / (t * (Real.log t) ^ 2)) :=
    (intervalIntegral.integral_add_adjacent_intervals hF_int_2x hF_int_xX).symm
  -- LHS reduces to the common expression
  have hLHS :
      (primeRecips X - Real.log (Real.log X)) -
          (primeRecips x - Real.log (Real.log x)) =
        logDiv X / Real.log X - logDiv x / Real.log x +
          (∫ t in x..X, logDiv t / (t * (Real.log t) ^ 2)) -
          (Real.log (Real.log X) - Real.log (Real.log x)) := by
    calc
      (primeRecips X - Real.log (Real.log X)) -
            (primeRecips x - Real.log (Real.log x))
          = ((logDiv X / Real.log X + (∫ t in 2..X, logDiv t / (t * (Real.log t) ^ 2))) -
                Real.log (Real.log X)) -
              ((logDiv x / Real.log x + (∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2))) -
                Real.log (Real.log x)) := by
              rw [primeRecips_eq_logDiv_div_log_add_integral h2X,
                  primeRecips_eq_logDiv_div_log_add_integral h2x]
          _ = ((logDiv X / Real.log X +
                  ((∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2)) +
                    (∫ t in x..X, logDiv t / (t * (Real.log t) ^ 2)))) - Real.log (Real.log X)) -
              ((logDiv x / Real.log x + (∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2))) -
                Real.log (Real.log x)) := by
              rw [hF_split]
          _ = logDiv X / Real.log X - logDiv x / Real.log x +
              (∫ t in x..X, logDiv t / (t * (Real.log t) ^ 2)) -
              (Real.log (Real.log X) - Real.log (Real.log x)) := by
              ring
  -- integral of the `t⁻¹ / log t` pieces, exactly
  have hU : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume x X :=
    intervalIntegrable_inv_div_log_ge h2x hxX
  have hV : IntervalIntegrable (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2) volume x X :=
    intervalIntegrable_inv_div_log_sq_ge h2x hxX
  have hBv : IntervalIntegrable (fun t : ℝ => B₁ * (t⁻¹ / (Real.log t) ^ 2)) volume x X :=
    hV.const_mul B₁
  have h_u : (∫ t in x..X, t⁻¹ / Real.log t) =
      Real.log (Real.log X) - Real.log (Real.log x) :=
    integral_inv_div_log hx1 hX1
  have h_v : (∫ t in x..X, t⁻¹ / (Real.log t) ^ 2) = 1 / Real.log x - 1 / Real.log X := by
    have hv := integral_inv_div_log_sq hx1 hX1
    rw [← one_div, ← one_div] at hv
    exact hv
  -- RHS reduces to the same common expression
  have hRHS :
      ((logDiv X - Real.log X - B₁) / Real.log X -
        (logDiv x - Real.log x - B₁) / Real.log x) +
          (∫ t in x..X, (logDiv t - Real.log t - B₁) / (t * (Real.log t) ^ 2))
        = logDiv X / Real.log X - logDiv x / Real.log x +
            (∫ t in x..X, logDiv t / (t * (Real.log t) ^ 2)) -
            (Real.log (Real.log X) - Real.log (Real.log x)) := by
    have hcong : (∫ t in x..X, (logDiv t - Real.log t - B₁) / (t * (Real.log t) ^ 2)) =
        ∫ t in x..X, (logDiv t / (t * (Real.log t) ^ 2) - t⁻¹ / Real.log t -
          B₁ * (t⁻¹ / (Real.log t) ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht2 : 2 ≤ t := uIcc_two_le_of_le h2x hxX ht
      have ht0 : t ≠ 0 := by linarith
      have hlogt : Real.log t ≠ 0 := by
        apply log_ne_zero_of_pos_of_ne_one <;> linarith [ht2]
      exact integrand_split (t := t) (B := B₁) ht0 hlogt
    have hint_lin :
        (∫ t in x..X, (logDiv t / (t * (Real.log t) ^ 2) - t⁻¹ / Real.log t -
            B₁ * (t⁻¹ / (Real.log t) ^ 2))) =
          (∫ t in x..X, logDiv t / (t * (Real.log t) ^ 2)) -
            (∫ t in x..X, t⁻¹ / Real.log t) -
            B₁ * (∫ t in x..X, t⁻¹ / (Real.log t) ^ 2) := by
      rw [intervalIntegral.integral_sub (hF_int_xX.sub hU) hBv,
          intervalIntegral.integral_sub hF_int_xX hU,
          intervalIntegral.integral_const_mul]
    calc
      ((logDiv X - Real.log X - B₁) / Real.log X -
            (logDiv x - Real.log x - B₁) / Real.log x) +
          (∫ t in x..X, (logDiv t - Real.log t - B₁) / (t * (Real.log t) ^ 2))
          = (logDiv X / Real.log X - logDiv x / Real.log x -
              B₁ / Real.log X + B₁ / Real.log x) +
              (∫ t in x..X, (logDiv t - Real.log t - B₁) / (t * (Real.log t) ^ 2)) := by
              rw [bound_split hlogx_ne hlogX_ne]
      _ = (logDiv X / Real.log X - logDiv x / Real.log x -
              B₁ / Real.log X + B₁ / Real.log x) +
              ((∫ t in x..X, logDiv t / (t * (Real.log t) ^ 2)) -
                (∫ t in x..X, t⁻¹ / Real.log t) -
                B₁ * (∫ t in x..X, t⁻¹ / (Real.log t) ^ 2)) := by
              rw [hcong, hint_lin]
      _ = (logDiv X / Real.log X - logDiv x / Real.log x -
              B₁ / Real.log X + B₁ / Real.log x) +
              ((∫ t in x..X, logDiv t / (t * (Real.log t) ^ 2)) -
                (Real.log (Real.log X) - Real.log (Real.log x)) -
                B₁ * (1 / Real.log x - 1 / Real.log X)) := by
              rw [h_u, h_v]
      _ = logDiv X / Real.log X - logDiv x / Real.log x +
            (∫ t in x..X, logDiv t / (t * (Real.log t) ^ 2)) -
            (Real.log (Real.log X) - Real.log (Real.log x)) := by
            ring
  exact hLHS.trans hRHS.symm

end Commons.NumberTheory.Mertens
