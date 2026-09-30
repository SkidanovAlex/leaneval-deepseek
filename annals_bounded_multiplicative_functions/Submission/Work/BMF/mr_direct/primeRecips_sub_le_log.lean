import Mathlib
import Submission.Work.BMF.mr_direct.mertens_lower_reimport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open scoped BigOperators

/-!
# A short-interval bound for the sum of prime reciprocals

We prove that for `2 ≤ x ≤ Y`,
`Σ_{x < p ≤ Y} 1/p = primeRecips Y − primeRecips x ≤ log 4 + log 4/log x + log 4·log(log Y/log x)`.

The proof uses the second Abel identity
`primeRecips x = logDiv x / log x + ∫_2^x logDiv t/(t log²t) dt`
together with the Chebyshev bound `logDiv t ≤ log 4·(1 + log t)`.
-/

/-- Elementary pointwise identity behind the evaluation of the integral. -/
private lemma one_add_log_div_eq {t : ℝ} (ht : 1 < t) :
    (1 + Real.log t) / (t * (Real.log t) ^ 2) = t⁻¹ / Real.log t + t⁻¹ / Real.log t ^ 2 := by
  have ht0 : t ≠ 0 := by linarith
  have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  field_simp
  ring

/-- Value of `∫_x^Y (1 + log t)/(t log²t) dt`. -/
private lemma integral_one_add_log_div_id_log_sq {x Y : ℝ} (hx : 1 < x) (hxY : x ≤ Y) :
    ∫ t in x..Y, (1 + Real.log t) / (t * (Real.log t) ^ 2) =
      Real.log (Real.log Y / Real.log x) + 1 / Real.log x - 1 / Real.log Y := by
  have hY : 1 < Y := lt_of_lt_of_le hx hxY
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlogY : Real.log Y ≠ 0 := ne_of_gt (Real.log_pos hY)
  have hcongr : ∫ t in x..Y, (1 + Real.log t) / (t * (Real.log t) ^ 2)
      = ∫ t in x..Y, (t⁻¹ / Real.log t + t⁻¹ / Real.log t ^ 2) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    simp only [Set.mem_uIcc] at ht
    refine one_add_log_div_eq ?_
    rcases ht with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
  have hint1 : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) MeasureTheory.volume x Y := by
    refine ContinuousOn.intervalIntegrable ?_
    intro z hz
    simp only [Set.mem_uIcc] at hz
    have hz0 : z ≠ 0 := by rcases hz with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
    have hlogz : Real.log z ≠ 0 := by
      rcases hz with ⟨h1, _⟩ | ⟨_, h2⟩ <;> exact ne_of_gt (Real.log_pos (by linarith))
    fun_prop (disch := positivity)
  have hint2 : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t ^ 2) MeasureTheory.volume x Y := by
    refine ContinuousOn.intervalIntegrable ?_
    intro z hz
    simp only [Set.mem_uIcc] at hz
    have hz0 : z ≠ 0 := by rcases hz with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
    have hlogz : Real.log z ≠ 0 := by
      rcases hz with ⟨h1, _⟩ | ⟨_, h2⟩ <;> exact ne_of_gt (Real.log_pos (by linarith))
    fun_prop (disch := positivity)
  rw [hcongr, intervalIntegral.integral_add hint1 hint2, integral_inv_div_log hx hY,
    integral_inv_div_log_sq hx hY, ← Real.log_div hlogY hlogx]
  ring

/-- Upper bound for the Abel integral term involving `logDiv`. -/
private lemma integral_logDiv_le {x Y : ℝ} (hx : 2 ≤ x) (hxY : x ≤ Y) :
    ∫ t in x..Y, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2) ≤
      Real.log 4 * (Real.log (Real.log Y / Real.log x) + 1 / Real.log x - 1 / Real.log Y) := by
  have hx1 : 1 < x := by linarith
  have hmono : ∫ t in x..Y, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2) ≤
      ∫ t in x..Y, Real.log 4 * ((1 + Real.log t) / (t * (Real.log t) ^ 2)) := by
    refine intervalIntegral.integral_mono_on hxY
      (Commons.NumberTheory.Mertens.intervalIntegrable_logDiv_div_id_log_sq_gen hx hxY)
      ((Commons.NumberTheory.Mertens.intervalIntegrable_one_add_log_div_id_log_sq_gen hx hxY).const_mul _)
      (fun t ht => ?_)
    have ht2 : 2 ≤ t := le_trans hx ht.1
    have ht1 : 1 < t := by linarith
    have hden : 0 < t * (Real.log t) ^ 2 := by
      have ht0 : 0 < t := by linarith
      have hlogt : 0 < Real.log t := Real.log_pos ht1
      positivity
    have hle := Commons.NumberTheory.Mertens.logDiv_le_log4_mul_one_add_log ht2
    calc Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2)
        ≤ Real.log 4 * (1 + Real.log t) / (t * (Real.log t) ^ 2) :=
          div_le_div_of_nonneg_right hle (le_of_lt hden)
      _ = Real.log 4 * ((1 + Real.log t) / (t * (Real.log t) ^ 2)) := by ring
  calc ∫ t in x..Y, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2)
      ≤ ∫ t in x..Y, Real.log 4 * ((1 + Real.log t) / (t * (Real.log t) ^ 2)) := hmono
    _ = Real.log 4 * ∫ t in x..Y, (1 + Real.log t) / (t * (Real.log t) ^ 2) :=
        intervalIntegral.integral_const_mul _ _
    _ = Real.log 4 * (Real.log (Real.log Y / Real.log x) + 1 / Real.log x - 1 / Real.log Y) := by
        rw [integral_one_add_log_div_id_log_sq hx1 hxY]

theorem primeRecips_sub_le_log {x Y : ℝ} (hx : 2 ≤ x) (hxY : x ≤ Y) :
    Commons.NumberTheory.Mertens.primeRecips Y - Commons.NumberTheory.Mertens.primeRecips x ≤
      Real.log 4 + Real.log 4 / Real.log x + Real.log 4 * Real.log (Real.log Y / Real.log x) := by
  have hY : 2 ≤ Y := le_trans hx hxY
  have hx1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogx_ne : Real.log x ≠ 0 := ne_of_gt hlogx
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith : 1 < Y)
  have hlogY_ne : Real.log Y ≠ 0 := ne_of_gt hlogY
  rw [Commons.NumberTheory.Mertens.primeRecips_eq_logDiv_div_log_add_integral hY,
    Commons.NumberTheory.Mertens.primeRecips_eq_logDiv_div_log_add_integral hx]
  have hsplit : (∫ t in 2..Y, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2))
      = (∫ t in 2..x, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2))
        + (∫ t in x..Y, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Commons.NumberTheory.Mertens.intervalIntegrable_logDiv_div_id_log_sq_gen (by norm_num : (2:ℝ) ≤ 2) hx)
      (Commons.NumberTheory.Mertens.intervalIntegrable_logDiv_div_id_log_sq_gen hx hxY)).symm
  have h1 : Commons.NumberTheory.Mertens.logDiv Y / Real.log Y ≤
      Real.log 4 / Real.log Y + Real.log 4 := by
    have hle := Commons.NumberTheory.Mertens.logDiv_le_log4_mul_one_add_log hY
    have heq : Real.log 4 * (1 + Real.log Y) / Real.log Y = Real.log 4 / Real.log Y + Real.log 4 := by
      field_simp
    calc Commons.NumberTheory.Mertens.logDiv Y / Real.log Y
        ≤ Real.log 4 * (1 + Real.log Y) / Real.log Y :=
          div_le_div_of_nonneg_right hle (le_of_lt hlogY)
      _ = Real.log 4 / Real.log Y + Real.log 4 := heq
  have h2 : -(Commons.NumberTheory.Mertens.logDiv x / Real.log x) ≤ 0 := by
    have hnn : 0 ≤ Commons.NumberTheory.Mertens.logDiv x := Commons.NumberTheory.Mertens.logDiv_nonneg x
    have : 0 ≤ Commons.NumberTheory.Mertens.logDiv x / Real.log x := div_nonneg hnn (le_of_lt hlogx)
    linarith
  have h3 := integral_logDiv_le hx hxY
  have hsum : Commons.NumberTheory.Mertens.logDiv Y / Real.log Y
        + -(Commons.NumberTheory.Mertens.logDiv x / Real.log x)
        + (∫ t in x..Y, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2)) ≤
      (Real.log 4 / Real.log Y + Real.log 4) + 0
        + Real.log 4 * (Real.log (Real.log Y / Real.log x) + 1 / Real.log x - 1 / Real.log Y) :=
    add_le_add (add_le_add h1 h2) h3
  calc (Commons.NumberTheory.Mertens.logDiv Y / Real.log Y
          + ∫ t in 2..Y, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2))
        - (Commons.NumberTheory.Mertens.logDiv x / Real.log x
          + ∫ t in 2..x, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2))
      = Commons.NumberTheory.Mertens.logDiv Y / Real.log Y
          + -(Commons.NumberTheory.Mertens.logDiv x / Real.log x)
          + (∫ t in x..Y, Commons.NumberTheory.Mertens.logDiv t / (t * (Real.log t) ^ 2)) := by
        rw [hsplit]; ring
    _ ≤ (Real.log 4 / Real.log Y + Real.log 4) + 0
        + Real.log 4 * (Real.log (Real.log Y / Real.log x) + 1 / Real.log x - 1 / Real.log Y) := hsum
    _ = Real.log 4 + Real.log 4 / Real.log x
        + Real.log 4 * Real.log (Real.log Y / Real.log x) := by
        field_simp
        ring

end Work.BMF.mr_direct
