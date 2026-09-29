import Mathlib
import Submission.Work.TMComp.C7Aux.rtlSchedule

/-!
# Run-length bound for the rational-tower schedule (`TMC7Core.Scale`)

This file proves `rtlRunLeV2`.  Let `rtlU` be the `(scale, index)` recursion of
`Submission.Work.TMComp.C7Aux.rtlSchedule`:

* `rtli A cκ Q k N₀ t = rtlIdx A Q k (rtlN A cκ Q k N₀ t)` is the largest index `i ≤ k` with
  `A * Q i ≤ rtlN ... t`;
* `rtlN ... (t+1) = rtlMM cκ Q (rtli ... t) * rtlN ... t`.

The index `rtli` is non-decreasing in `t` (`rtli_mono`), so if `rtli ... t1 = rtli ... t2 = i`
then `rtli ... u = i` for **every** `u ∈ [t1, t2]`: a "run" of constant index.  On a run the
scale is multiplied at each step by the same factor `rtlMM cκ Q i`, which is sandwiched between
`exp (cκ * Q i / 2) / 10` and `exp (cκ * Q i / 2) / 5`.  Moreover:

* at the beginning of the run, `A * Q i ≤ rtlN ... t1` (maximality of `rtli ... t1 = i`);
* at the end of the run, `rtlN ... t2 < A * Q (i+1) ≤ A * exp (b * Q i)` (maximality of
  `rtli ... t2 = i` together with `i < k` and the growth hypothesis `hgrowth`).

So a run of length `m = t2 - t1` has to realise the multiplicative growth from
`A * Q i` to `A * exp (b * Q i)`, i.e. `(exp (cκ * Q i / 2) / 10) ^ m < exp (b * Q i) / Q i`.
Taking logarithms and using `log 10 ≤ cκ * Q i / 4` gives `m * (cκ / 4) < b`.

This is the form in which the bound is consumed by the counting estimate `rtl_card_le`.
-/

namespace Work.TMC7Core.Scale

open Work.TMComp.C7Aux

/-- Arithmetic core of the run-length bound.  If the `n`-th power of `exp (cκ * E / 2) / 10` is
dominated by `R`, and `R < exp (b * E) / E`, then `n * (cκ / 4) < b`.

Here `E = Q i ≥ 1` plays the role of the index of the run, `R = (rtlMM cκ Q i) ^ n` the scale
ratio realised over the run, and `exp (b * E) / E` the maximal ratio available at index `i`. -/
theorem rtlRunArith (n : ℕ) (b cκ E R : ℝ) (hE : 1 ≤ E)
    (hlog : Real.log 10 ≤ cκ * E / 4)
    (hRlo : (Real.exp (cκ * E / 2) / 10) ^ n ≤ R)
    (hRhi : R < Real.exp (b * E) / E) :
    (n : ℝ) * (cκ / 4) < b := by
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have h10 : (10 : ℝ) ≠ 0 := by norm_num
  have hlogbase : Real.log ((Real.exp (cκ * E / 2) / 10) ^ n)
      = (n : ℝ) * (cκ * E / 2 - Real.log 10) := by
    rw [Real.log_pow, Real.log_div (ne_of_gt (Real.exp_pos _)) h10, Real.log_exp]
  have hrhs : Real.log (Real.exp (b * E) / E) = b * E - Real.log E := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hEpos), Real.log_exp]
  have hlt : Real.log ((Real.exp (cκ * E / 2) / 10) ^ n) < Real.log (Real.exp (b * E) / E) :=
    Real.log_lt_log (by positivity) (lt_of_le_of_lt hRlo hRhi)
  rw [hlogbase, hrhs] at hlt
  -- `log 10 ≤ cκ * E / 4` dominates the loss `log 10` in the base of the power
  have hcoef : cκ * E / 4 ≤ cκ * E / 2 - Real.log 10 := by linarith
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have step : (n : ℝ) * (cκ * E / 4) ≤ (n : ℝ) * (cκ * E / 2 - Real.log 10) :=
    mul_le_mul_of_nonneg_left hcoef hn
  -- drop the nonnegative `log E` term
  have hlogE : 0 ≤ Real.log E := Real.log_nonneg hE
  have hBE : (n : ℝ) * (cκ * E / 4) < b * E := by linarith
  have hBE' : ((n : ℝ) * (cκ / 4)) * E < b * E := by nlinarith [hBE]
  exact lt_of_mul_lt_mul_right hBE' (le_of_lt hEpos)

/-- On an interval on which the index `rtli` is constant, the scale is the initial scale
multiplied by the constant power of `rtlMM` attached to that index. -/
theorem rtlRunN (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) (hQ : ∀ i ≤ k, 1 ≤ Q i)
    (hA0 : A * (Q 0 : ℝ) ≤ (N₀ : ℝ)) {i t1 t2 : ℕ}
    (h1 : rtli A cκ Q k N₀ t1 = i) (h2 : rtli A cκ Q k N₀ t2 = i) (ht : t1 ≤ t2) :
    rtlN A cκ Q k N₀ t2 = rtlMM cκ Q i ^ (t2 - t1) * rtlN A cκ Q k N₀ t1 := by
  have hmono := rtli_mono A cκ Q k N₀ hQ hA0
  -- the index is constant between the two times
  have hconst : ∀ u, t1 ≤ u → u ≤ t2 → rtli A cκ Q k N₀ u = i := by
    intro u hu1 hu2
    exact le_antisymm (by rw [← h2]; exact hmono hu2) (by rw [← h1]; exact hmono hu1)
  have h := rtlN_eq_pow A cκ Q k N₀ i t1 (t2 - t1) (fun u hu hu' => hconst u hu (by omega))
  rwa [Nat.add_sub_cancel' ht] at h

set_option linter.unusedVariables false in
/-- Two times at which the tower schedule `rtli A cκ Q k N₀` takes the same value `i < k` are
separated by fewer than `4 b / cκ` steps. -/
theorem rtlRunLeV2 (A cκ b : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ)
    (hA : 0 < A) (hcκ : 0 < cκ) (hb : 0 < b)
    (hQ1 : ∀ i ≤ k, 1 ≤ Q i)
    (hgrowth : ∀ i < k, (Q (i+1) : ℝ) ≤ Real.exp (b * (Q i : ℝ)))
    (hA0 : A * (Q 0 : ℝ) ≤ (N₀ : ℝ))
    (hbig : ∀ i ≤ k, Real.log 10 ≤ cκ * (Q i : ℝ) / 4)
    (hbig2 : ∀ i ≤ k, 2 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)))
    {i t1 t2 : ℕ} (hik : i < k) (h1 : Work.TMComp.C7Aux.rtli A cκ Q k N₀ t1 = i)
    (h2 : Work.TMComp.C7Aux.rtli A cκ Q k N₀ t2 = i) (ht : t1 ≤ t2) :
    (t2 - t1 : ℝ) * (cκ / 4) < b := by
  have hik' : i ≤ k := le_of_lt hik
  have hQpos : 0 < (Q i : ℝ) := by
    have h := hQ1 i hik'
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h)
  -- the scale along the run is the initial scale times a constant power of `rtlMM`
  have hdecomp : rtlN A cκ Q k N₀ t2
      = rtlMM cκ Q i ^ (t2 - t1) * rtlN A cκ Q k N₀ t1 :=
    rtlRunN A cκ Q k N₀ hQ1 hA0 h1 h2 ht
  -- bounds on the scales at the two ends of the run
  have hA0le1 : A * (Q 0 : ℝ) ≤ (rtlN A cκ Q k N₀ t1 : ℝ) :=
    le_trans hA0 (by exact_mod_cast N₀_le_rtlN A cκ Q k N₀ hQ1 t1)
  have hle1 : A * (Q i : ℝ) ≤ (rtlN A cκ Q k N₀ t1 : ℝ) := by
    have h := rtli_spec (A := A) (cκ := cκ) (Q := Q) (k := k) (N₀ := N₀) (s := t1) hA0le1
    rwa [h1] at h
  have hlt2 : (rtlN A cκ Q k N₀ t2 : ℝ) < A * (Q (i+1) : ℝ) := by
    have h := rtli_greatest (A := A) (cκ := cκ) (Q := Q) (k := k) (N₀ := N₀) (s := t2)
      (by rw [h2]; exact hik)
    rw [h2] at h
    exact not_le.mp h
  have hN1pos : 0 < (rtlN A cκ Q k N₀ t1 : ℝ) :=
    lt_of_lt_of_le (mul_pos hA hQpos) hle1
  have hRmul : ((rtlMM cκ Q i : ℝ)) ^ (t2 - t1) * (rtlN A cκ Q k N₀ t1 : ℝ)
      = (rtlN A cκ Q k N₀ t2 : ℝ) := by
    rw [hdecomp, Nat.cast_mul, Nat.cast_pow]
  -- the factor realised over the run is at least `exp (cκ * Q i / 2) / 10`
  have hRlo : (Real.exp (cκ * (Q i : ℝ) / 2) / 10) ^ (t2 - t1)
      ≤ ((rtlMM cκ Q i : ℝ)) ^ (t2 - t1) :=
    pow_le_pow_left₀ (a := Real.exp (cκ * (Q i : ℝ) / 2) / 10) (b := (rtlMM cκ Q i : ℝ))
      (by positivity) (rtlMM_ge cκ Q i (hbig2 i hik')) (t2 - t1)
  -- and at most `exp (b * Q i) / Q i`: the run stops before reaching `A * Q (i+1)`
  have hRhi : ((rtlMM cκ Q i : ℝ)) ^ (t2 - t1) < Real.exp (b * (Q i : ℝ)) / (Q i : ℝ) := by
    have s1 : ((rtlMM cκ Q i : ℝ)) ^ (t2 - t1)
        < (A * (Q (i+1) : ℝ)) / (rtlN A cκ Q k N₀ t1 : ℝ) := by
      rw [lt_div_iff₀ hN1pos, hRmul]
      exact hlt2
    have s2 : (A * (Q (i+1) : ℝ)) / (rtlN A cκ Q k N₀ t1 : ℝ)
        ≤ (Q (i+1) : ℝ) / (Q i : ℝ) := by
      have h1' : (A * (Q (i+1) : ℝ)) / (rtlN A cκ Q k N₀ t1 : ℝ)
          ≤ (A * (Q (i+1) : ℝ)) / (A * (Q i : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hA hQpos) hle1
      have h2' : (A * (Q (i+1) : ℝ)) / (A * (Q i : ℝ)) = (Q (i+1) : ℝ) / (Q i : ℝ) :=
        mul_div_mul_left _ _ (ne_of_gt hA)
      rwa [h2'] at h1'
    have s3 : (Q (i+1) : ℝ) / (Q i : ℝ) ≤ Real.exp (b * (Q i : ℝ)) / (Q i : ℝ) :=
      div_le_div_of_nonneg_right (hgrowth i hik) (le_of_lt hQpos)
    exact lt_of_lt_of_le s1 (le_trans s2 s3)
  simpa [Nat.cast_sub ht] using
    (rtlRunArith (t2 - t1) b cκ (Q i : ℝ) (((rtlMM cκ Q i : ℝ)) ^ (t2 - t1))
      (by exact_mod_cast hQ1 i hik') (hbig i hik') hRlo hRhi)

end Work.TMC7Core.Scale
