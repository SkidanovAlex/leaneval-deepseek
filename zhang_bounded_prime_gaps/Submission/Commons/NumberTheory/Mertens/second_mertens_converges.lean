import Mathlib
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.first_mertens_bounded
import Submission.Commons.NumberTheory.Mertens.primeZeta_pole

open Finset Real Filter MeasureTheory
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

/-!
# Second Mertens theorem: `∑_{p ≤ x} 1/p − log log x` converges

We prove `second_mertens_converges`: there is a real constant `M` such that
`∑_{p ≤ x} 1/p − log log x → M` as `x → ∞`.

The proof is classical and elementary (Mertens):
* first Mertens theorem (`first_mertens_bounded`): `|logDiv x − log x|` is bounded;
* the Abel identity `primeRecips_eq_logDiv_div_log_add_integral` gives
  `∑ 1/p − log log x = (1 − log log 2) + (logDiv x − log x)/log x +
    ∫_2^x (logDiv t − log t)/(t (log t)²) dt`;
* the last two summands tend to limits (`E/log x → 0` by boundedness and the
  integral is a Cauchy net because `E` is bounded and `∫ t⁻¹/(log t)²` converges).
-/

/-- `logDiv x − log x` (bounded remainder in the first Mertens theorem). -/
private def smcE (x : ℝ) : ℝ :=
  logDiv x - Real.log x

/-- `log (log x)`. -/
private def smcLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log x)

/-- The correction integral `∫_2^x (logDiv t − log t)/(t (log t)²) dt`. -/
private def smcR (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, smcE t / (t * (Real.log t) ^ 2)

private lemma smcE_div_eq_sub (t : ℝ) :
    smcE t / (t * (Real.log t) ^ 2) =
      logDiv t / (t * (Real.log t) ^ 2) - Real.log t / (t * (Real.log t) ^ 2) := by
  unfold smcE
  ring

private lemma uIcc_two_le {x t : ℝ} (hx : 2 ≤ x) (ht : t ∈ Set.uIcc (2 : ℝ) x) : 2 ≤ t := by
  rw [Set.uIcc_of_le hx] at ht
  exact ht.1

private lemma uIcc_mem_two_le {a b t : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (ht : t ∈ Set.uIcc a b) : 2 ≤ t := by
  rw [Set.uIcc_of_le hab] at ht
  exact le_trans ha ht.1

private lemma intervalIntegrable_one_div_id_log_gen {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (1 : ℝ) / (t * Real.log t)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  have hz2 : 2 ≤ z := uIcc_mem_two_le ha hab hz
  have hz0 : z ≠ 0 := by linarith
  have hlog : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz2]
  fun_prop (disch := positivity)

private lemma intervalIntegrable_log_div_id_log_sq_gen {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Real.log t / (t * (Real.log t) ^ 2)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  have hz2 : 2 ≤ z := uIcc_mem_two_le ha hab hz
  have hz0 : z ≠ 0 := by linarith
  have hlog : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz2]
  fun_prop (disch := positivity)

private lemma intervalIntegrable_smcE_div_id_log_sq_gen {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => smcE t / (t * (Real.log t) ^ 2)) volume a b := by
  have hsub : IntervalIntegrable (fun t : ℝ => logDiv t / (t * (Real.log t) ^ 2) -
      Real.log t / (t * (Real.log t) ^ 2)) volume a b :=
    (intervalIntegrable_logDiv_div_id_log_sq_gen ha hab).sub
      (intervalIntegrable_log_div_id_log_sq_gen ha hab)
  exact hsub.congr (fun t ht => (smcE_div_eq_sub t).symm)

private lemma intervalIntegrable_one_div_id_log_sq_gen {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (1 : ℝ) / (t * (Real.log t) ^ 2)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro z hz
  have hz2 : 2 ≤ z := uIcc_mem_two_le ha hab hz
  have hz0 : z ≠ 0 := by linarith
  have hlog : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz2]
  fun_prop (disch := positivity)

/-- `logDiv x / log x = 1 + (logDiv x − log x)/log x` for `x ≥ 2`. -/
private lemma logDiv_div_log_eq (x : ℝ) (hx : 2 ≤ x) :
    logDiv x / Real.log x = 1 + smcE x / Real.log x := by
  have hlogx : Real.log x ≠ 0 := by
    have h1 : (1 : ℝ) < x := by linarith
    exact ne_of_gt (Real.log_pos h1)
  unfold smcE
  field_simp [hlogx]
  ring

private lemma integrand_decomp_on_uIcc {x t : ℝ} (hx : 2 ≤ x) (ht : t ∈ Set.uIcc (2 : ℝ) x) :
    logDiv t / (t * (Real.log t) ^ 2) =
      smcE t / (t * (Real.log t) ^ 2) + (1 : ℝ) / (t * Real.log t) := by
  have ht2 : 2 ≤ t := uIcc_two_le hx ht
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := by
    have h1 : (1 : ℝ) < t := by linarith
    exact ne_of_gt (Real.log_pos h1)
  unfold smcE
  field_simp [ht0, hlog]
  ring

/-- `∫_2^x logDiv/(t log²t) = R x + (log log x − log log 2)`. -/
private lemma integral_logDiv_decomp (x : ℝ) (hx : 2 ≤ x) :
    (∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2)) =
      smcR x + (smcLogLog x - smcLogLog 2) := by
  have hcong : (∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2)) =
      ∫ t in 2..x, (smcE t / (t * (Real.log t) ^ 2) + (1 : ℝ) / (t * Real.log t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact integrand_decomp_on_uIcc hx ht
  have hx1 : 1 < x := by linarith
  have hEq : (∫ t in 2..x, (1 : ℝ) / (t * Real.log t)) =
      ∫ t in 2..x, t⁻¹ / Real.log t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht2 : 2 ≤ t := uIcc_two_le hx ht
    have ht0 : t ≠ 0 := by linarith
    field_simp [ht0]
  calc
    (∫ t in 2..x, logDiv t / (t * (Real.log t) ^ 2))
        = ∫ t in 2..x, (smcE t / (t * (Real.log t) ^ 2) + (1 : ℝ) / (t * Real.log t)) := hcong
    _ = (∫ t in 2..x, smcE t / (t * (Real.log t) ^ 2)) +
        (∫ t in 2..x, (1 : ℝ) / (t * Real.log t)) := by
        rw [intervalIntegral.integral_add (intervalIntegrable_smcE_div_id_log_sq_gen
          (by norm_num : (2 : ℝ) ≤ 2) hx)
          (intervalIntegrable_one_div_id_log_gen (by norm_num : (2 : ℝ) ≤ 2) hx)]
    _ = smcR x + (smcLogLog x - smcLogLog 2) := by
        have h1 : (∫ t in 2..x, smcE t / (t * (Real.log t) ^ 2)) = smcR x := by
          rfl
        have h2 : (∫ t in 2..x, (1 : ℝ) / (t * Real.log t)) = smcLogLog x - smcLogLog 2 := by
          rw [hEq]
          rw [integral_inv_div_log (by norm_num : (1 : ℝ) < 2) hx1]
          rfl
        rw [h1, h2]

/-- The exact decomposition: `∑_{p≤x} 1/p − log log x` splits into a constant,
`E x / log x`, and `R x`. -/
private lemma primeRecips_sub_loglog_decomp (x : ℝ) (hx : 2 ≤ x) :
    primeRecips x - smcLogLog x =
      (1 - smcLogLog 2) + smcE x / Real.log x + smcR x := by
  rw [primeRecips_eq_logDiv_div_log_add_integral hx]
  rw [logDiv_div_log_eq x hx]
  rw [integral_logDiv_decomp x hx]
  ring

/-- `R x − R a = ∫_a^x E/(t log²t)` for `2 ≤ a ≤ x`. -/
private lemma smcR_sub (x a : ℝ) (ha : 2 ≤ a) (hax : a ≤ x) :
    smcR x - smcR a = ∫ t in a..x, smcE t / (t * (Real.log t) ^ 2) := by
  have h2a : IntervalIntegrable (fun t : ℝ => smcE t / (t * (Real.log t) ^ 2)) volume 2 a :=
    intervalIntegrable_smcE_div_id_log_sq_gen (by norm_num) ha
  have hax' : IntervalIntegrable (fun t : ℝ => smcE t / (t * (Real.log t) ^ 2)) volume a x :=
    intervalIntegrable_smcE_div_id_log_sq_gen ha hax
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h2a hax'
  unfold smcR
  rw [← hsplit]
  ring

/-- `∫_a^x 1/(t log²t) = 1/log a − 1/log x` for `2 ≤ a ≤ x`. -/
private lemma integral_one_div_id_log_sq_gen {a x : ℝ} (ha : 2 ≤ a) (hax : a ≤ x) :
    (∫ t in a..x, (1 : ℝ) / (t * (Real.log t) ^ 2)) =
      (1 / Real.log a - 1 / Real.log x) := by
  have hEq : (∫ t in a..x, (1 : ℝ) / (t * (Real.log t) ^ 2)) =
      ∫ t in a..x, t⁻¹ / (Real.log t) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : t ≠ 0 := by
      have ht2 : 2 ≤ t := uIcc_mem_two_le ha hax ht
      linarith
    field_simp [ht0]
  have ha1 : (1 : ℝ) < a := by linarith
  have hx1 : 1 < x := lt_of_lt_of_le ha1 hax
  rw [hEq]
  rw [integral_inv_div_log_sq ha1 hx1]
  simp [one_div]

/-- Pointwise bound `|E t/(t log²t)| ≤ C · 1/(t log²t)` for `t ≥ 2`, provided
`|E t| ≤ C` and `C ≥ 0`. -/
private lemma smcE_integrand_abs_le {t C : ℝ} (ht : 2 ≤ t) (hC : 0 ≤ C) (hE : |smcE t| ≤ C) :
    |smcE t / (t * (Real.log t) ^ 2)| ≤ C * (1 / (t * (Real.log t) ^ 2)) := by
  have hdenpos : 0 < t * (Real.log t) ^ 2 := by
    have htpos : 0 < t := by linarith
    have hlogpos : 0 < Real.log t := by
      have h1 : (1 : ℝ) < t := by linarith
      exact Real.log_pos h1
    positivity
  have hw : 0 ≤ 1 / (t * (Real.log t) ^ 2) :=
    div_nonneg zero_le_one (le_of_lt hdenpos)
  calc
    |smcE t / (t * (Real.log t) ^ 2)| = |smcE t| / (t * (Real.log t) ^ 2) := by
      rw [abs_div]
      rw [abs_of_pos hdenpos]
    _ = |smcE t| * (1 / (t * (Real.log t) ^ 2)) := by
      field_simp [ne_of_gt hdenpos]
    _ ≤ C * (1 / (t * (Real.log t) ^ 2)) :=
      mul_le_mul_of_nonneg_right hE hw

/-- Cauchy-type bound for `R`: `|R x − R a| ≤ C (1/log a − 1/log x)`. -/
private lemma smcR_cauchy_bound {x a C : ℝ} (hC : 0 ≤ C)
    (hEb : ∀ ⦃t : ℝ⦄, 2 ≤ t → |smcE t| ≤ C) (ha : 2 ≤ a) (hax : a ≤ x) :
    |smcR x - smcR a| ≤ C * (1 / Real.log a - 1 / Real.log x) := by
  let f : ℝ → ℝ := fun t => smcE t / (t * (Real.log t) ^ 2)
  let g : ℝ → ℝ := fun t => C * (1 / (t * (Real.log t) ^ 2))
  have hg_ii : IntervalIntegrable g volume a x :=
    (intervalIntegrable_one_div_id_log_sq_gen ha hax).const_mul C
  have hf_ii : IntervalIntegrable f volume a x := by
    simpa [f] using intervalIntegrable_smcE_div_id_log_sq_gen ha hax
  have hle : ∀ t ∈ Set.Ioc a x, ‖f t‖ ≤ g t := by
    intro t ht
    have ht2 : 2 ≤ t := le_trans ha ht.1.le
    have hE := hEb ht2
    dsimp [f, g]
    simpa [Real.norm_eq_abs] using smcE_integrand_abs_le ht2 hC hE
  have hnorm : ‖∫ t in a..x, f t ∂volume‖ ≤ ∫ t in a..x, g t ∂volume :=
    intervalIntegral.norm_integral_le_of_norm_le hax (Eventually.of_forall hle) hg_ii
  calc
    |smcR x - smcR a| = ‖∫ t in a..x, f t ∂volume‖ := by
      rw [smcR_sub x a ha hax]
      simp [f, Real.norm_eq_abs]
    _ = ‖∫ t in a..x, f t ∂volume‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ t in a..x, g t ∂volume := hnorm
    _ = C * (1 / Real.log a - 1 / Real.log x) := by
      dsimp [g]
      rw [intervalIntegral.integral_const_mul]
      rw [integral_one_div_id_log_sq_gen ha hax]

/-- `|E x| / log x ≤ C / log x` for `x ≥ 2` with `|E x| ≤ C`. -/
private lemma smcE_div_log_abs_le {x C : ℝ} (hC : 0 ≤ C) (hE : |smcE x| ≤ C) (hx : 2 ≤ x) :
    |smcE x / Real.log x| ≤ C / Real.log x := by
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  calc
    |smcE x / Real.log x| = |smcE x| / Real.log x := by
      rw [abs_div]
      rw [abs_of_pos hlogx]
    _ ≤ C / Real.log x := by
      exact div_le_div_of_nonneg_right hE (le_of_lt hlogx)

/-- Main Cauchy bound for `f x := ∑_{p≤x} 1/p − log log x`. -/
private lemma fval_cauchy {x a C : ℝ} (hC : 0 ≤ C)
    (hEb : ∀ ⦃t : ℝ⦄, 2 ≤ t → |smcE t| ≤ C) (ha : 2 ≤ a) (hax : a ≤ x) :
    |(primeRecips x - smcLogLog x) - (primeRecips a - smcLogLog a)| ≤
      3 * C / Real.log a := by
  have hx : 2 ≤ x := le_trans ha hax
  have hlogapos : 0 < Real.log a := Real.log_pos (by linarith : (1 : ℝ) < a)
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  have hlogxge : Real.log a ≤ Real.log x := Real.log_le_log (by linarith : (0 : ℝ) < a) hax
  have hlogxinvle : 1 / Real.log x ≤ 1 / Real.log a :=
    one_div_le_one_div_of_le hlogapos hlogxge
  have hdecx := primeRecips_sub_loglog_decomp x hx
  have hdeca := primeRecips_sub_loglog_decomp a ha
  have hdiff : (primeRecips x - smcLogLog x) - (primeRecips a - smcLogLog a) =
      (smcE x / Real.log x - smcE a / Real.log a) + (smcR x - smcR a) := by
    rw [hdecx, hdeca]
    ring
  have hA : |smcE x / Real.log x - smcE a / Real.log a| ≤ 2 * C / Real.log a := by
    have h1 : |smcE x / Real.log x| ≤ C / Real.log x :=
      smcE_div_log_abs_le hC (hEb hx) hx
    have h2 : |smcE a / Real.log a| ≤ C / Real.log a :=
      smcE_div_log_abs_le hC (hEb ha) ha
    have htri := abs_add_le (smcE x / Real.log x) (-(smcE a / Real.log a))
    have hsub : |smcE x / Real.log x - smcE a / Real.log a| ≤
        |smcE x / Real.log x| + |smcE a / Real.log a| := by
      simpa [sub_eq_add_neg, abs_neg] using htri
    have hxle : C / Real.log x ≤ C / Real.log a := by
      calc
        C / Real.log x = C * (1 / Real.log x) := by ring
        _ ≤ C * (1 / Real.log a) := mul_le_mul_of_nonneg_left hlogxinvle hC
        _ = C / Real.log a := by ring
    have hsum : |smcE x / Real.log x| + |smcE a / Real.log a| ≤
        2 * C / Real.log a := by
      have h1' : |smcE x / Real.log x| ≤ C / Real.log a := le_trans h1 hxle
      have hh : C / Real.log a + C / Real.log a = 2 * C / Real.log a := by ring
      nlinarith
    exact le_trans hsub hsum
  have hB : |smcR x - smcR a| ≤ C / Real.log a := by
    have hb := smcR_cauchy_bound hC hEb ha hax
    have hlogxinv0 : 0 ≤ 1 / Real.log x := div_nonneg zero_le_one (le_of_lt hlogxpos)
    have hsuble : 1 / Real.log a - 1 / Real.log x ≤ 1 / Real.log a := by linarith
    have hred : C * (1 / Real.log a - 1 / Real.log x) ≤ C / Real.log a := by
      have h' : C * (1 / Real.log a - 1 / Real.log x) ≤ C * (1 / Real.log a) :=
        mul_le_mul_of_nonneg_left hsuble hC
      have h'' : C * (1 / Real.log a) = C / Real.log a := by ring
      rw [h''] at h'
      exact h'
    exact le_trans hb hred
  rw [hdiff]
  have htri := abs_add_le (smcE x / Real.log x - smcE a / Real.log a) (smcR x - smcR a)
  have h2sum : |smcE x / Real.log x - smcE a / Real.log a| + |smcR x - smcR a| ≤
      3 * C / Real.log a := by
    have h2add : 2 * C / Real.log a + C / Real.log a = 3 * C / Real.log a := by ring
    nlinarith
  exact le_trans htri h2sum

/-- `fval x := ∑_{p≤x} 1/p − log log x`. -/
private def fval (x : ℝ) : ℝ :=
  primeRecips x - smcLogLog x

/-- `log u − log v ≤ (u−v)/v` (concavity of `log`, tangent bound). -/
private lemma log_sub_log_le_div (u v : ℝ) (hv : 0 < v) (huv : v ≤ u) :
    Real.log u - Real.log v ≤ (u - v) / v := by
  have hu : u ≠ 0 := by linarith
  have hv' : v ≠ 0 := ne_of_gt hv
  have hpos : 0 < u / v := div_pos (lt_of_lt_of_le hv huv) hv
  have hle := Real.log_le_sub_one_of_pos hpos
  have hlogdiv : Real.log (u / v) = Real.log u - Real.log v := Real.log_div hu hv'
  have hmain : Real.log u - Real.log v ≤ u / v - 1 := by
    simpa [hlogdiv] using hle
  have hstep : u / v - 1 = (u - v) / v := by
    field_simp [hv']
  rw [hstep] at hmain
  exact hmain

/-- `log log x − log log n ≤ 1/(n log n)` for `n ≤ x ≤ n+1`, `n ≥ 2`. -/
private lemma loglog_sub_le_of_between {n : ℕ} {x : ℝ} (hn : 2 ≤ n) (hxn : (n : ℝ) ≤ x)
    (hx1 : x ≤ ((n + 1 : ℕ) : ℝ)) :
    smcLogLog x - smcLogLog (n : ℝ) ≤ 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
  have hnposR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1R : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlogv : 0 < Real.log (n : ℝ) := Real.log_pos hn1R
  have hlogvle : Real.log (n : ℝ) ≤ Real.log x := by
    exact Real.log_le_log (by linarith : 0 < (n : ℝ)) hxn
  have hstep1 : Real.log (Real.log x) - Real.log (Real.log (n : ℝ)) ≤
      (Real.log x - Real.log (n : ℝ)) / Real.log (n : ℝ) := by
    exact log_sub_log_le_div (Real.log x) (Real.log (n : ℝ)) hlogv hlogvle
  have hx1pos : 0 < x := by linarith
  have hlogxle : Real.log x ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log hx1pos hx1
  have hdx : Real.log x - Real.log (n : ℝ) ≤
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by linarith
  have hdn : Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    have hnp1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hnn : (n : ℝ) ≠ 0 := ne_of_gt hnposR
    have hlogdiv : Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
        Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) :=
      Real.log_div hnp1 hnn
    have hpos : 0 < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by positivity
    have hle := Real.log_le_sub_one_of_pos hpos
    have hred : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 = 1 / (n : ℝ) := by
      field_simp [hnn] <;> norm_num
    calc
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)
          = Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := hlogdiv.symm
      _ ≤ (((n + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 := hle
      _ = 1 / (n : ℝ) := hred
  have hdivle : (Real.log x - Real.log (n : ℝ)) / Real.log (n : ℝ) ≤
      (1 / (n : ℝ)) / Real.log (n : ℝ) := by
    exact div_le_div_of_nonneg_right (le_trans hdx hdn) (le_of_lt hlogv)
  have hfinal : (1 / (n : ℝ)) / Real.log (n : ℝ) = 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
    have hnn' : (n : ℝ) ≠ 0 := ne_of_gt hnposR
    have hlogv' : Real.log (n : ℝ) ≠ 0 := ne_of_gt hlogv
    field_simp [hnn', hlogv'] <;> ring
  calc
    smcLogLog x - smcLogLog (n : ℝ) ≤
        (Real.log x - Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      simpa [smcLogLog] using hstep1
    _ ≤ (1 / (n : ℝ)) / Real.log (n : ℝ) := hdivle
    _ = 1 / ((n : ℝ) * Real.log (n : ℝ)) := hfinal

/-- Glue: for `x ≥ 3`, `fval x` is close to its value at `⌊x⌋₊`. -/
private lemma fval_floor_glue (x : ℝ) (hx : 3 ≤ x) :
    |fval x - fval ((⌊x⌋₊ : ℕ) : ℝ)| ≤
      1 / (((⌊x⌋₊ : ℕ) : ℝ) * Real.log ((⌊x⌋₊ : ℕ) : ℝ)) := by
  let n : ℕ := ⌊x⌋₊
  have hn3 : 3 ≤ n := by
    dsimp [n]
    exact Nat.le_floor (by linarith : (3 : ℝ) ≤ x)
  have hn2 : 2 ≤ n := by omega
  have hxn : (n : ℝ) ≤ x := by
    dsimp [n]
    exact Nat.floor_le (by linarith : 0 ≤ x)
  have hx1 : x ≤ ((n + 1 : ℕ) : ℝ) := by
    dsimp [n]
    have hlt := Nat.lt_floor_add_one x
    have hcast : ((⌊x⌋₊ + 1 : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) + 1 := by
      norm_num
    rw [← hcast] at hlt
    exact le_of_lt hlt
  have hP : primeRecips x = primeRecips ((n : ℕ) : ℝ) := by
    dsimp [n]
    unfold primeRecips
    congr 1
    rw [Nat.floor_natCast]
  have hdiff : fval x - fval ((n : ℕ) : ℝ) = smcLogLog ((n : ℕ) : ℝ) - smcLogLog x := by
    unfold fval
    rw [hP]
    ring
  have hmono : smcLogLog ((n : ℕ) : ℝ) ≤ smcLogLog x := by
    unfold smcLogLog
    have hposn : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlogposn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    exact Real.log_le_log hlogposn (Real.log_le_log hposn hxn)
  have hle : smcLogLog x - smcLogLog ((n : ℕ) : ℝ) ≤
      1 / (((n : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ)) :=
    loglog_sub_le_of_between hn2 hxn hx1
  calc
    |fval x - fval ((n : ℕ) : ℝ)| = |smcLogLog ((n : ℕ) : ℝ) - smcLogLog x| := by rw [hdiff]
    _ = smcLogLog x - smcLogLog ((n : ℕ) : ℝ) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
      ring
    _ ≤ 1 / (((n : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ)) := hle


/-- The sequence `n ↦ fval n`, `n : ℕ`. -/
private def gseq (n : ℕ) : ℝ :=
  fval (n : ℝ)

/-- The sequence `gseq` is Cauchy, provided the first Mertens bound holds. -/
private lemma gseq_cauchy {C : ℝ} (hC : 0 ≤ C)
    (hEb : ∀ ⦃t : ℝ⦄, 2 ≤ t → |smcE t| ≤ C) : CauchySeq gseq := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹) atTop (nhds 0) :=
    hlog.inv_tendsto_atTop
  have hlim : Tendsto (fun n : ℕ => (3 * C) * (Real.log (n : ℝ))⁻¹) atTop (nhds 0) := by
    simpa using (hinv.const_mul (3 * C))
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N₀, hN₀⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max (N₀ : ℝ) (2 / ε)) 3)
  have hN3 : 3 ≤ N := by
    have hlt : (3 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ 3) hN
    exact Nat.le_of_lt (by exact_mod_cast hlt)
  have hN0le : N₀ ≤ N := by
    have hlt : (N₀ : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    exact Nat.le_of_lt (by exact_mod_cast hlt)
  refine ⟨N, ?_⟩
  intro m hm n hn
  let s : ℕ := min m n
  have hsN : N ≤ s := by
    dsimp [s]
    exact le_min hm hn
  have hs3 : 3 ≤ s := le_trans hN3 hsN
  have hsN0 : N₀ ≤ s := le_trans hN0le hsN
  have hsmall : (3 * C) * (1 / Real.log (s : ℝ)) < ε := by
    have hlogs : 0 < Real.log (s : ℝ) :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < s by omega))
    have hd : |(3 * C) * (Real.log (s : ℝ))⁻¹| < ε := by
      simpa [Real.dist_eq] using hN₀ s hsN0
    have heq : (3 * C) * (1 / Real.log (s : ℝ)) = (3 * C) * (Real.log (s : ℝ))⁻¹ := by
      rw [one_div]
    rw [heq]
    exact lt_of_le_of_lt (le_abs_self _) hd
  by_cases hmn : m ≤ n
  · have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hbnd := fval_cauchy (x := (n : ℝ)) (a := (m : ℝ)) hC hEb hm2R hmnR
    have hs_eq : s = m := by
      dsimp [s]
      exact min_eq_left hmn
    have hbnd' : |gseq m - gseq n| ≤ 3 * C / Real.log (m : ℝ) := by
      simpa [gseq, fval, abs_sub_comm] using hbnd
    have hm3 : 3 ≤ m := le_trans hN3 hm
    have hm1 : (1 : ℕ) < m := by omega
    have hlogs : 0 < Real.log (s : ℝ) :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < s by omega))
    have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm1)
    have hlogle : Real.log (s : ℝ) ≤ Real.log (m : ℝ) := by
      have hsm : s ≤ m := by
        dsimp [s]
        exact min_le_left m n
      exact Real.log_le_log (by exact_mod_cast (by omega : 0 < s)) (by exact_mod_cast hsm)
    have hinvle : 1 / Real.log (m : ℝ) ≤ 1 / Real.log (s : ℝ) :=
      one_div_le_one_div_of_le hlogs hlogle
    have hle : 3 * C / Real.log (m : ℝ) ≤ 3 * C / Real.log (s : ℝ) := by
      simpa [hs_eq] using (mul_le_mul_of_nonneg_right hinvle (by nlinarith : 0 ≤ 3 * C))
    have hred : 3 * C / Real.log (s : ℝ) = (3 * C) * (1 / Real.log (s : ℝ)) := by ring
    calc
      dist (gseq m) (gseq n) = |gseq m - gseq n| := by rw [Real.dist_eq]
      _ ≤ 3 * C / Real.log (m : ℝ) := hbnd'
      _ ≤ 3 * C / Real.log (s : ℝ) := hle
      _ = (3 * C) * (1 / Real.log (s : ℝ)) := hred
      _ < ε := hsmall
  · have hmn' : n ≤ m := le_of_not_ge hmn
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
    have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmn'
    have hbnd := fval_cauchy (x := (m : ℝ)) (a := (n : ℝ)) hC hEb hn2R hnmR
    have hs_eq : s = n := by
      dsimp [s]
      exact min_eq_right hmn'
    have hbnd' : |gseq m - gseq n| ≤ 3 * C / Real.log (n : ℝ) := by
      simpa [gseq, fval] using hbnd
    have hn3 : 3 ≤ n := le_trans hN3 hn
    have hn1 : (1 : ℕ) < n := by omega
    have hlogs : 0 < Real.log (s : ℝ) :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < s by omega))
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
    have hlogle : Real.log (s : ℝ) ≤ Real.log (n : ℝ) := by
      have hsn : s ≤ n := by
        dsimp [s]
        exact min_le_right m n
      exact Real.log_le_log (by exact_mod_cast (by omega : 0 < s)) (by exact_mod_cast hsn)
    have hinvle : 1 / Real.log (n : ℝ) ≤ 1 / Real.log (s : ℝ) :=
      one_div_le_one_div_of_le hlogs hlogle
    have hle : 3 * C / Real.log (n : ℝ) ≤ 3 * C / Real.log (s : ℝ) := by
      simpa [hs_eq] using (mul_le_mul_of_nonneg_right hinvle (by nlinarith : 0 ≤ 3 * C))
    have hred : 3 * C / Real.log (s : ℝ) = (3 * C) * (1 / Real.log (s : ℝ)) := by ring
    calc
      dist (gseq m) (gseq n) = |gseq m - gseq n| := by rw [Real.dist_eq]
      _ ≤ 3 * C / Real.log (n : ℝ) := hbnd'
      _ ≤ 3 * C / Real.log (s : ℝ) := hle
      _ = (3 * C) * (1 / Real.log (s : ℝ)) := hred
      _ < ε := hsmall

/-- `fval` tends to a limit at `+∞` (given the first Mertens bound). -/
private theorem fval_tendsto_of_mertensI {C : ℝ} (hC : 0 ≤ C)
    (hEb : ∀ ⦃t : ℝ⦄, 2 ≤ t → |smcE t| ≤ C) :
    ∃ M : ℝ, Tendsto fval atTop (nhds M) := by
  have hCauchy : CauchySeq gseq := gseq_cauchy hC hEb
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hCauchy
  refine ⟨L, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rcases (Metric.tendsto_atTop.mp hL) (ε / 2) hε2 with ⟨N₀, hN₀⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max (N₀ : ℝ) (2 / ε)) 3)
  have hN3 : 3 ≤ N := by
    have hlt : (3 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ 3) hN
    exact Nat.le_of_lt (by exact_mod_cast hlt)
  have hN0le : N₀ ≤ N := by
    have hlt : (N₀ : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    exact Nat.le_of_lt (by exact_mod_cast hlt)
  refine ⟨(N : ℝ), ?_⟩
  intro x hx
  let n : ℕ := ⌊x⌋₊
  have hx3 : 3 ≤ x := by
    have hN3R : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
    linarith
  have hnN : N ≤ n := by
    dsimp [n]
    exact Nat.le_floor hx
  have hn3 : 3 ≤ n := le_trans hN3 hnN
  have hn0 : N₀ ≤ n := le_trans hN0le hnN
  have hglue := fval_floor_glue x hx3
  have hlogge : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hlog3 : (1 : ℝ) ≤ Real.log (3 : ℝ) := le_of_lt log_three_gt_one
    have hlog3le : Real.log (3 : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 3) hn3R
    linarith
  have hposn : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hle1n : 1 / ((n : ℝ) * Real.log (n : ℝ)) ≤ 1 / (n : ℝ) := by
    have hprodge : (n : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
      have : 0 ≤ (n : ℝ) * (Real.log (n : ℝ) - 1) := by
        exact mul_nonneg (le_of_lt hposn) (by linarith)
      nlinarith
    exact one_div_le_one_div_of_le hposn hprodge
  have h2N' : (2 : ℝ) / ε < (N : ℝ) := by
    have hlt := hN
    have hle : (2 : ℝ) / ε ≤ max (max (N₀ : ℝ) (2 / ε)) 3 :=
      le_trans (le_max_right (N₀ : ℝ) (2 / ε)) (le_max_left _ 3)
    exact lt_of_le_of_lt hle hlt
  have hsmall1 : 1 / (n : ℝ) < ε / 2 := by
    have h2e : (2 : ℝ) / ε < (n : ℝ) := by
      exact lt_of_lt_of_le h2N' (by exact_mod_cast hnN)
    have h2lt : 2 < (n : ℝ) * ε := by
      have hεpos : 0 < ε := hε
      rwa [div_lt_iff₀ hεpos] at h2e
    rw [div_lt_iff₀ hposn]
    nlinarith
  calc
    dist (fval x) L = |fval x - L| := by rw [Real.dist_eq]
    _ ≤ |fval x - fval ((n : ℕ) : ℝ)| + |fval ((n : ℕ) : ℝ) - L| := by
        have htri := abs_add_le (fval x - fval ((n : ℕ) : ℝ)) (fval ((n : ℕ) : ℝ) - L)
        have hsum : (fval x - fval ((n : ℕ) : ℝ)) + (fval ((n : ℕ) : ℝ) - L) = fval x - L := by
          ring
        rwa [hsum] at htri
    _ < ε := by
        have h1 : |fval x - fval ((n : ℕ) : ℝ)| < ε / 2 := by
          have hle0' : |fval x - fval ((n : ℕ) : ℝ)| ≤ 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
            simpa [n] using hglue
          exact lt_of_le_of_lt (le_trans hle0' hle1n) hsmall1
        have h2 : |fval ((n : ℕ) : ℝ) - L| < ε / 2 := by
          have hd : dist (fval ((n : ℕ) : ℝ)) L < ε / 2 := by
            simpa [gseq] using hN₀ n hn0
          simpa [Real.dist_eq] using hd
        linarith

/-- Second Mertens theorem (existence form). -/
theorem second_mertens_converges :
    ∃ M : ℝ, Filter.Tendsto (fun x : ℝ =>
      Commons.NumberTheory.Mertens.primeRecips x - Real.log (Real.log x))
      Filter.atTop (nhds M) := by
  obtain ⟨C, hCpos, hb⟩ := first_mertens_bounded
  have hEb : ∀ ⦃t : ℝ⦄, 2 ≤ t → |smcE t| ≤ C := by
    intro t ht
    simpa [smcE] using hb t ht
  obtain ⟨M, hM⟩ := fval_tendsto_of_mertensI (le_of_lt hCpos) hEb
  refine ⟨M, ?_⟩
  change Filter.Tendsto fval Filter.atTop (nhds M)
  exact hM

end

end Commons.NumberTheory.Mertens
