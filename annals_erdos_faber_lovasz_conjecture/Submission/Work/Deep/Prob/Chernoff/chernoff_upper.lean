/-
# The one-sided weighted Chernoff (Bernstein) bound for independent events

`chernoff_upper` is the upper-tail form of the weighted Bernstein bound for a finite family of
independent events.  For a finite probability space `P`, independent events `A i`, weights
`0 ≤ w i ≤ C` and `t ≥ 0`,

`ℙ[∑ i, w i · 1[A i] - ∑ i, ℙ[A i] · w i ≥ t] ≤ exp (- t ^ 2 / (2 C (μ + t / 3)))`,

where `μ = ∑ i, ℙ[A i] · w i`.

## Proof

1. *Reduction to the pattern space.*  Both the weighted sum and its mean depend on `ω` only
   through the outcome pattern `pattern A ω : ι → Bool`, and `IndepEvents` says that the law
   of that pattern is the product of the marginals `ℙ[A i]`.  Hence (`pattern_expect`) the
   probability of the deviation event is the weighted sum over all Boolean configurations `s`
   of `∏ i, (if s i then ℙ[A i] else 1 - ℙ[A i])` times the indicator of the deviation at `s`.

2. *Exponential moment bound.*  `Commons.Probability.Chernoff.upper_tail` (the workspace's
   finite weighted Chernoff bound, proved by the exponential-moment method) bounds that sum,
   for every `lam ≥ 0`, by `exp (-(lam t) - lam μ + (μ / C) (exp (lam C) - 1))`.

3. *Optimisation.*  `opt_exponent` chooses `lam` so that this exponent is at most
   `- t ^ 2 / (2 C (μ + t / 3))`; the key estimate is
   `Commons.Analysis.Real.mul_exp_sub_one_sub_le`, which for `B = μ + t / 3` and `u = t / B`
   gives `μ (exp u - 1 - u) ≤ u t / 2`.

The degenerate cases `C = 0` (where the right-hand side is `exp 0 = 1`, by `x / 0 = 0`) and
`μ = 0` are handled separately.
-/
import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Prob.Basic
import Submission.Work.Deep.Prob.Spaces
import Submission.Work.Deep.Prob.Indep.pattern_expect
import Submission.Work.Deep.Prob.Chernoff.expect_sum_indicators
import Submission.Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted
import Submission.Commons.Analysis.Real.mul_exp_sub_one_sub_le

namespace Work.Deep.Prob.Chernoff

open scoped BigOperators

/-- A single weighted indicator is the corresponding pattern summand. -/
private lemma ind_eq_pattern {Ω : Type*} [Fintype Ω] {ι : Type*} {A : ι → Set Ω} (w : ι → ℝ)
    (i : ι) (ω : Ω) :
    (A i).indicator (fun _ => w i) ω = if FinProbSpace.pattern A ω i then w i else 0 := by
  by_cases h : ω ∈ A i
  · have hpat : FinProbSpace.pattern A ω i = true := (FinProbSpace.pattern_eq_true_iff A ω i).mpr h
    rw [Set.indicator_of_mem h, hpat]; simp
  · have hpat : FinProbSpace.pattern A ω i = false :=
      (FinProbSpace.pattern_eq_false_iff A ω i).mpr h
    rw [Set.indicator_of_notMem h, hpat]; simp

/-- The weighted sum of indicators, read off the outcome pattern of the event family. -/
private lemma sum_ind_eq_sum_pattern {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι]
    {A : ι → Set Ω} (w : ι → ℝ) (ω : Ω) :
    (∑ i, (A i).indicator (fun _ => w i) ω)
      = ∑ i, (if FinProbSpace.pattern A ω i then w i else 0) :=
  Finset.sum_congr rfl fun i _ => ind_eq_pattern w i ω

/-- **Optimisation of the Bernstein exponent.**

For `μ = ∑ i, ℙ[A i] · w i ≥ 0`, `C > 0` and `t ≥ 0` there is `lam ≥ 0` with
`-(lam t) - lam μ + (μ / C) (exp (lam C) - 1) ≤ - t ^ 2 / (2 C (μ + t / 3))`.

For `μ = 0` take `lam = 3 / (2 C)` (both sides are then `-3t/(2C)`); for `μ > 0` take
`lam = u / C` with `B = μ + t / 3` and `u = t / B`, and use
`μ (exp u - 1 - u) ≤ u t / 2` (`mul_exp_sub_one_sub_le`, valid since `μ ≤ B - t / 3`). -/
private lemma opt_exponent {μ t C : ℝ} (hμ : 0 ≤ μ) (hC : 0 < C) (ht : 0 ≤ t) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      -(lam * t) - lam * μ + (μ / C) * (Real.exp (lam * C) - 1)
        ≤ -(t ^ 2) / (2 * C * (μ + t / 3)) := by
  rcases eq_or_lt_of_le hμ with hμ0 | hμpos
  · refine ⟨3 / (2 * C), by positivity, ?_⟩
    rw [← hμ0]
    simp only [mul_zero, sub_zero, zero_div, zero_mul, add_zero]
    rw [zero_add, neg_div, Commons.Probability.Chernoff.sq_div_two_C_third t C]
    exact le_of_eq (by ring)
  · set B : ℝ := μ + t / 3 with hBdef
    have hBpos : 0 < B := by rw [hBdef]; linarith
    set u : ℝ := t / B with hudef
    have hkey : μ * (Real.exp u - 1 - u) ≤ u * t / 2 := by
      have hle : μ ≤ B - t / 3 := by rw [hBdef]; linarith
      have h := Commons.Analysis.Real.mul_exp_sub_one_sub_le hBpos ht hμ hle
      simpa only [← hudef] using h
    refine ⟨u / C, by positivity, ?_⟩
    have hlamC : (u / C) * C = u := by field_simp
    have hgoal : -(u / C * t) - u / C * μ + (μ / C) * (Real.exp u - 1)
        = (1 / C) * (μ * (Real.exp u - 1 - u) - u * t) := by
      field_simp
      ring
    rw [hlamC, hgoal]
    have hut : u * t = t ^ 2 / B := by rw [hudef]; field_simp
    refine le_of_mul_le_mul_left ?_ hC
    have hr : C * (-(t ^ 2) / (2 * C * B)) = -(t ^ 2) / (2 * B) := by
      field_simp
    rw [hr]
    have hl : C * ((1 / C) * (μ * (Real.exp u - 1 - u) - u * t))
        = μ * (Real.exp u - 1 - u) - u * t := by
      field_simp
    rw [hl]
    have hr2 : t ^ 2 / (2 * B) = u * t / 2 := by rw [hut]; field_simp
    rw [neg_div, hr2]
    linarith [hkey]

/-- **The one-sided weighted Chernoff/Bernstein bound.**  For independent events `A i` with
weights `0 ≤ w i ≤ C`, the weighted number of events that occur exceeds its mean
`μ = ∑ i, ℙ[A i] * w i` by at least `t` with probability at most
`exp (-(t ^ 2) / (2 * C * (μ + t / 3)))`. -/
theorem chernoff_upper {Ω : Type*} [Fintype Ω] (P : FinProbSpace Ω) {ι : Type*} [Fintype ι]
    {A : ι → Set Ω} (hA : FinProbSpace.IndepEvents P A) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    {C : ℝ} (hC0 : 0 ≤ C) (hwC : ∀ i, w i ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    P.prob {ω | t ≤ (∑ i, (A i).indicator (fun _ => w i) ω) - ∑ i, P.prob (A i) * w i}
      ≤ Real.exp (-(t ^ 2) / (2 * C * (∑ i, P.prob (A i) * w i + t / 3))) := by
  classical
  -- The deviation event depends on `ω` only through the outcome pattern; `hpoint` records
  -- this indicator by indicator, using the pointwise identity `sum_ind_eq_sum_pattern`
  -- which turns the weighted sum of indicators into the corresponding pattern sum.
  have hpoint : ∀ ω : Ω,
      ({ω | t ≤ (∑ i, (A i).indicator (fun _ => w i) ω) - ∑ i, P.prob (A i) * w i} : Set Ω).indicator
          (fun _ => (1 : ℝ)) ω
        = (fun s : ι → Bool =>
            (if t ≤ (∑ i, (if s i then w i else 0)) - ∑ i, P.prob (A i) * w i
              then (1 : ℝ) else 0))
          (FinProbSpace.pattern A ω) := by
    intro ω
    have hsum := sum_ind_eq_sum_pattern (A := A) w ω
    by_cases h : t ≤ (∑ i, (A i).indicator (fun _ => w i) ω) - ∑ i, P.prob (A i) * w i
    · rw [Set.indicator_of_mem (show ω ∈ ({ω | t ≤ (∑ i, (A i).indicator (fun _ => w i) ω)
          - ∑ i, P.prob (A i) * w i} : Set Ω) from h)]
      show (1 : ℝ) = (if t ≤ (∑ i, (if FinProbSpace.pattern A ω i then w i else 0))
        - ∑ i, P.prob (A i) * w i then (1 : ℝ) else 0)
      rw [if_pos (by rw [← hsum]; exact h)]
    · rw [Set.indicator_of_notMem (show ω ∉ ({ω | t ≤ (∑ i, (A i).indicator (fun _ => w i) ω)
          - ∑ i, P.prob (A i) * w i} : Set Ω) from h)]
      show (0 : ℝ) = (if t ≤ (∑ i, (if FinProbSpace.pattern A ω i then w i else 0))
        - ∑ i, P.prob (A i) * w i then (1 : ℝ) else 0)
      rw [if_neg (by rw [← hsum]; exact h)]
  -- Step 1: reduce the probability to a sum over Boolean patterns.
  have htrans : P.prob {ω | t ≤ (∑ i, (A i).indicator (fun _ => w i) ω) - ∑ i, P.prob (A i) * w i}
      = ∑ s : ι → Bool, (∏ i, (if s i then P.prob (A i) else 1 - P.prob (A i))) *
          (if t ≤ (∑ i, (if s i then w i else 0)) - ∑ i, P.prob (A i) * w i
            then (1 : ℝ) else 0) := by
    calc P.prob {ω | t ≤ (∑ i, (A i).indicator (fun _ => w i) ω) - ∑ i, P.prob (A i) * w i}
        = P.expect (fun ω => ({ω | t ≤ (∑ i, (A i).indicator (fun _ => w i) ω)
            - ∑ i, P.prob (A i) * w i} : Set Ω).indicator (fun _ => (1 : ℝ)) ω) :=
          (P.expect_indicator _).symm
      _ = P.expect (fun ω => (fun s : ι → Bool =>
            (if t ≤ (∑ i, (if s i then w i else 0)) - ∑ i, P.prob (A i) * w i
              then (1 : ℝ) else 0)) (FinProbSpace.pattern A ω)) := by
          simp only [FinProbSpace.expect]
          exact Finset.sum_congr rfl fun ω _ => by rw [hpoint ω]
      _ = ∑ s : ι → Bool, (∏ i, (if s i then P.prob (A i) else 1 - P.prob (A i))) *
          (if t ≤ (∑ i, (if s i then w i else 0)) - ∑ i, P.prob (A i) * w i
            then (1 : ℝ) else 0) :=
          Work.Deep.Prob.Indep.pattern_expect P hA
            (fun s : ι → Bool =>
              (if t ≤ (∑ i, (if s i then w i else 0)) - ∑ i, P.prob (A i) * w i
                then (1 : ℝ) else 0))
  rw [htrans]
  rcases eq_or_lt_of_le hC0 with hCzero | hCpos
  · -- `C = 0`: the right-hand side is `exp 0 = 1`, and a probability never exceeds one.
    subst hCzero
    have hprod : ∀ s : ι → Bool, 0 ≤ ∏ i, (if s i then P.prob (A i) else 1 - P.prob (A i)) := by
      intro s
      apply Finset.prod_nonneg
      intro i _
      split_ifs with h
      · exact FinProbSpace.prob_nonneg P (A i)
      · linarith [FinProbSpace.prob_le_one P (A i)]
    have hle1 : (∑ s : ι → Bool, (∏ i, (if s i then P.prob (A i) else 1 - P.prob (A i))) *
        (if t ≤ (∑ i, (if s i then w i else 0)) - ∑ i, P.prob (A i) * w i
          then (1 : ℝ) else 0)) ≤ 1 := by
      calc (∑ s : ι → Bool, (∏ i, (if s i then P.prob (A i) else 1 - P.prob (A i))) *
            (if t ≤ (∑ i, (if s i then w i else 0)) - ∑ i, P.prob (A i) * w i
              then (1 : ℝ) else 0))
          ≤ ∑ s : ι → Bool, (∏ i, (if s i then P.prob (A i) else 1 - P.prob (A i))) * 1 := by
            apply Finset.sum_le_sum
            intro s _
            apply mul_le_mul_of_nonneg_left _ (hprod s)
            split_ifs <;> norm_num
        _ = ∑ s : ι → Bool, ∏ i, (if s i then P.prob (A i) else 1 - P.prob (A i)) := by
            simp
        _ = 1 := Commons.Probability.Chernoff.sum_weight_eq_one (fun i => P.prob (A i))
    have hRHS : Real.exp (-(t ^ 2) / (2 * (0 : ℝ) * (∑ i, P.prob (A i) * w i + t / 3))) = 1 := by
      norm_num
    rw [hRHS]
    exact hle1
  · -- `C > 0`: exponential moment bound plus the optimisation of the exponent.
    have hp0 : ∀ i, 0 ≤ P.prob (A i) := fun i => FinProbSpace.prob_nonneg P (A i)
    have hp1 : ∀ i, P.prob (A i) ≤ 1 := fun i => FinProbSpace.prob_le_one P (A i)
    have hμ0 : 0 ≤ ∑ i, P.prob (A i) * w i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hp0 i) (hw0 i)
    obtain ⟨lam, hlam0, hopt⟩ := opt_exponent hμ0 hCpos ht
    refine le_trans (Commons.Probability.Chernoff.upper_tail (p := fun i => P.prob (A i))
      (X := w) (C := C) hCpos hp0 hp1 hw0 hwC (lam := lam) (T := t) hlam0) ?_
    exact Real.exp_le_exp.mpr hopt

end Work.Deep.Prob.Chernoff
