import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.Hfun_defs
import Submission.Work.CNum.cterm_deriv
import Submission.Work.CNum.cterm_bounds
import Submission.Work.CNum.sum_bound
import Submission.Work.CNum.chord

/-! # CNum: the chord bound for `Hfun`

`Hfun φ = log 192 + Σ' n, 24 log ‖1 + (3/4)^{n+1} e^{i(n+1)φ}‖` is the value of
`log ‖h((3/4) e^{iφ})‖` on the circle of radius `3/4`.  This file proves the *chord bound*

`Hfun φ ≤ max (Hfun a) (Hfun b) + 400 (b - a)²   (φ ∈ [a,b])`,

which lets one bound `Hfun` on an interval from its two endpoint values.

The proof has three steps.

* `Hfun_defs` rewrites every summand into the cosine form `cterm m φ = 12 log (1 + 2 r^m cos(mφ) + r^{2m})`
  and introduces the formal derivatives `ctermDeriv`, `ctermDeriv2`.
* `cterm_deriv`/`cterm_bounds` compute the derivatives and bound them uniformly in `φ`:
  `|ctermDeriv m φ| ≤ 24 m r^m/(1-r^m)²` and `|ctermDeriv2 m φ| ≤ 24 m² r^m/(1-r^m)²`.
  Summability of `24 m² r^m/(1-r^m)²` (bound by `384 m² r^m`) then gives, via `hasDerivAt_tsum`,
  that `Kfun = Σ' m, cterm (m+1)` has derivative `KfunDeriv = Σ' m, ctermDeriv (m+1)` whose
  derivative is `KfunDeriv2 = Σ' m, ctermDeriv2 (m+1)`.
* `sum_bound` shows `Σ' m, 24 (m+1)² r^{m+1}/(1-r^{m+1})² ≤ 3200` (the exact value is
  `3171.2852…`), so `KfunDeriv2 φ ≥ -3200` for every `φ`.
* `chord` is the general sharp estimate: a `C²` function on `[a,b]` with `g'' ≥ -3200`
  satisfies `g φ ≤ max (g a) (g b) + 400 (b-a)²` (since `3200/8 = 400`).
-/

namespace Work.CNum

open Complex Metric Filter Topology
open scoped BigOperators

/-- The comparison summand for the summability of the derivative bounds. -/
noncomputable def ub (n : ℕ) : ℝ :=
  24 * ((n : ℝ) + 1) ^ 2 * r34 ^ (n + 1) / (1 - r34 ^ (n + 1)) ^ 2

lemma h_norm_r34 : ‖r34‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos r34_pos]; exact r34_lt_one

lemma r34_pow_succ_le (n : ℕ) : r34 ^ (n + 1) ≤ r34 := by
  simpa using pow_le_pow_of_le_one r34_nonneg (le_of_lt r34_lt_one) (by omega : 1 ≤ n + 1)

lemma summable_base : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * r34 ^ (n + 1)) := by
  have h0 : Summable (fun n : ℕ => r34 ^ n) := summable_geometric_of_norm_lt_one h_norm_r34
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r34 ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := r34) h_norm_r34
    simpa using this
  have h2 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * r34 ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := r34) h_norm_r34
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * r34 ^ n) := by
    have h := (h2.add (h1.mul_left 2)).add h0
    refine h.congr (fun n => ?_)
    ring
  have := hsum.mul_left r34
  refine this.congr (fun n => ?_)
  rw [pow_succ]; ring

lemma ub_nonneg (n : ℕ) : 0 ≤ ub n := by
  unfold ub
  have h1 : 0 < (1 - r34 ^ (n + 1)) := by
    have := r34_pow_lt_one (m := n + 1) (by omega); linarith
  have h2 : 0 ≤ 24 * ((n : ℝ) + 1) ^ 2 * r34 ^ (n + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (le_of_lt (r34_pow_pos _))
  exact div_nonneg h2 (le_of_lt (pow_pos h1 2))

lemma ub_le (n : ℕ) : ub n ≤ 384 * (((n : ℝ) + 1) ^ 2 * r34 ^ (n + 1)) := by
  unfold ub
  have h1 : 0 < (1 - r34 ^ (n + 1)) := by
    have := r34_pow_lt_one (m := n + 1) (by omega); linarith
  have hpos : 0 < (1 - r34 ^ (n + 1)) ^ 2 := pow_pos h1 2
  rw [div_le_iff₀ hpos]
  have h3 : r34 ^ (n + 1) ≤ (3 / 4 : ℝ) := by
    have := r34_pow_succ_le n; simpa [r34] using this
  have hD : (1 / 16 : ℝ) ≤ (1 - r34 ^ (n + 1)) ^ 2 := by nlinarith
  have hA : 0 ≤ ((n : ℝ) + 1) ^ 2 * r34 ^ (n + 1) :=
    mul_nonneg (sq_nonneg _) (le_of_lt (r34_pow_pos _))
  nlinarith

lemma summable_ub : Summable ub :=
  Summable.of_nonneg_of_le ub_nonneg ub_le (summable_base.mul_left 384)

lemma cterm_zero_eq (n : ℕ) : cterm (n + 1) 0 = 24 * Real.log (1 + r34 ^ (n + 1)) := by
  unfold cterm eterm
  have h1 : ((n + 1 : ℕ) : ℝ) * 0 = 0 := by ring
  rw [h1, Real.cos_zero, mul_one]
  have h2 : (1 : ℝ) + 2 * r34 ^ (n + 1) + (r34 ^ (n + 1)) ^ 2 = (1 + r34 ^ (n + 1)) ^ 2 := by
    ring
  rw [h2, Real.log_pow]
  ring

lemma cterm_zero_nonneg (n : ℕ) : 0 ≤ cterm (n + 1) 0 := by
  rw [cterm_zero_eq n]
  refine mul_nonneg (by norm_num) (Real.log_nonneg ?_)
  have := r34_pow_pos (n + 1); linarith

lemma cterm_zero_le (n : ℕ) : cterm (n + 1) 0 ≤ 24 * r34 ^ (n + 1) := by
  rw [cterm_zero_eq n]
  have hpos : 0 < 1 + r34 ^ (n + 1) := by have := r34_pow_pos (n + 1); linarith
  have := Real.log_le_sub_one_of_pos hpos
  linarith

lemma summable_cterm_zero : Summable (fun n : ℕ => cterm (n + 1) 0) := by
  refine Summable.of_nonneg_of_le cterm_zero_nonneg cterm_zero_le ?_
  have h : Summable (fun n : ℕ => r34 * r34 ^ n) :=
    (summable_geometric_of_norm_lt_one h_norm_r34).mul_left r34
  have h' : Summable (fun n : ℕ => r34 ^ (n + 1)) := by
    refine h.congr (fun n => ?_); rw [pow_succ]; ring
  simpa using h'.mul_left 24

lemma ub1_le_ub (n : ℕ) :
    24 * ((n : ℝ) + 1) * r34 ^ (n + 1) / (1 - r34 ^ (n + 1)) ^ 2 ≤ ub n := by
  unfold ub
  have h1 : 0 < (1 - r34 ^ (n + 1)) := by
    have := r34_pow_lt_one (m := n + 1) (by omega); linarith
  have hpos : 0 < (1 - r34 ^ (n + 1)) ^ 2 := pow_pos h1 2
  rw [div_le_div_iff_of_pos_right hpos]
  have hr : 0 ≤ r34 ^ (n + 1) := le_of_lt (r34_pow_pos _)
  have hk : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have h24 : (0 : ℝ) ≤ 24 * r34 ^ (n + 1) := mul_nonneg (by norm_num) hr
  calc 24 * ((n : ℝ) + 1) * r34 ^ (n + 1) = ((n : ℝ) + 1) * (24 * r34 ^ (n + 1)) := by ring
    _ ≤ ((n : ℝ) + 1) ^ 2 * (24 * r34 ^ (n + 1)) := mul_le_mul_of_nonneg_right h2 h24
    _ = 24 * ((n : ℝ) + 1) ^ 2 * r34 ^ (n + 1) := by ring

/-- `Kfun` is differentiable, with derivative the termwise derivative. -/
lemma hasDerivAt_Kfun (φ : ℝ) : HasDerivAt Kfun (KfunDeriv φ) φ := by
  unfold Kfun KfunDeriv
  refine hasDerivAt_tsum (u := ub) summable_ub ?_ ?_ summable_cterm_zero φ
  · intro n y; exact (cterm_deriv (n + 1) y).1
  · intro n y
    have h := (cterm_bounds (n + 1) (by omega) y).1
    calc |ctermDeriv (n + 1) y| ≤
          24 * ((n : ℝ) + 1) * r34 ^ (n + 1) / (1 - r34 ^ (n + 1)) ^ 2 := by
          simpa [Real.norm_eq_abs] using h
      _ ≤ ub n := ub1_le_ub n

/-- The termwise derivative series is differentiable, with derivative `KfunDeriv2`. -/
lemma hasDerivAt_KfunDeriv (φ : ℝ) : HasDerivAt KfunDeriv (KfunDeriv2 φ) φ := by
  unfold KfunDeriv KfunDeriv2
  refine hasDerivAt_tsum (u := ub) (y₀ := 0) summable_ub ?_ ?_ ?_ φ
  · intro n y; exact (cterm_deriv (n + 1) y).2
  · intro n y
    have := (cterm_bounds (n + 1) (by omega) y).2
    simpa [ub, Real.norm_eq_abs] using this
  · refine Summable.of_norm_bounded summable_ub (fun n => ?_)
    have h := (cterm_bounds (n + 1) (by omega) 0).1
    calc ‖ctermDeriv (n + 1) 0‖ = |ctermDeriv (n + 1) 0| := Real.norm_eq_abs _
      _ ≤ 24 * ((n : ℝ) + 1) * r34 ^ (n + 1) / (1 - r34 ^ (n + 1)) ^ 2 := by simpa using h
      _ ≤ ub n := ub1_le_ub n

/-- `Hfun` is differentiable, with derivative `KfunDeriv`. -/
lemma hasDerivAt_Hfun (x : ℝ) : HasDerivAt Hfun (KfunDeriv x) x := by
  have h : HasDerivAt (fun φ => Real.log 192 + Kfun φ) (KfunDeriv x) x :=
    (hasDerivAt_Kfun x).const_add (Real.log 192)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with φ
  exact Hfun_eq φ

/-- `KfunDeriv2` is bounded below by `-3200` (the true upper bound of `Σ 24 m² r^m/(1-r^m)²`
is `3171.28…`, and `-3200/8 = -400`). -/
lemma KfunDeriv2_ge (φ : ℝ) : -3200 ≤ KfunDeriv2 φ := by
  have hsum : Summable (fun n : ℕ => -ctermDeriv2 (n + 1) φ) := by
    refine Summable.of_norm_bounded summable_ub (fun n => ?_)
    have h := (cterm_bounds (n + 1) (by omega) φ).2
    rw [Real.norm_eq_abs, abs_neg]
    simpa [ub] using h
  have hle : (∑' n : ℕ, -ctermDeriv2 (n + 1) φ) ≤ ∑' n : ℕ, ub n :=
    Summable.tsum_le_tsum (fun n => by
      have h := (cterm_bounds (n + 1) (by omega) φ).2
      calc -ctermDeriv2 (n + 1) φ ≤ |ctermDeriv2 (n + 1) φ| := neg_le_abs _
        _ ≤ ub n := by simpa [ub] using h) hsum summable_ub
  have hfin : -KfunDeriv2 φ ≤ 3200 := by
    have hneg : (∑' n : ℕ, -ctermDeriv2 (n + 1) φ) = -KfunDeriv2 φ := by
      rw [KfunDeriv2, tsum_neg]
    rw [← hneg]
    exact le_trans hle sum_bound
  linarith

theorem Hfun_chord {a b : ℝ} (hab : a ≤ b) :
    ∀ φ ∈ Set.Icc a b, Hfun φ ≤ max (Hfun a) (Hfun b) + 400 * (b - a) ^ 2 :=
  chord hab hasDerivAt_Hfun hasDerivAt_KfunDeriv KfunDeriv2_ge

end Work.CNum
