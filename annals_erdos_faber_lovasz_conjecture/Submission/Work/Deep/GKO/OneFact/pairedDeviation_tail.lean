import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Fintype.Pi

/-!
# A Hoeffding tail bound for weighted Rademacher sums on the cube

For `c : ι → ℝ` with `|c i| ≤ 1` and `t ≥ 0`, the average over the `2 ^ |ι|` vertices
`x : ι → Bool` of the indicator of the event
`t ≤ |∑ i, c i * (x i - 1/2)|` is at most `2 * exp (-(2 * t ^ 2) / |ι|)`.

This is Hoeffding's inequality for the sum of the independent bounded random variables
`c i * (X i - 1/2)`, `X i` uniform on `{0,1}`, with the sub-gaussian parameter `∑ c i ^ 2`
dominated by `|ι|`.  The proof is the classical one, carried out by finite sums only (no
measure theory):

* the exact moment generating identity
  `∑ x, 2 ^ (-|ι|) * exp (λ * ∑ i, c i * (x i - 1/2)) = ∏ i, cosh (λ * c i / 2)`;
* Hoeffding's lemma `cosh u ≤ exp (u ^ 2 / 2)` (Mathlib's `Real.cosh_le_exp_half_sq`)
  applied coordinatewise, giving the bound `exp (λ ^ 2 * (∑ i, c i ^ 2) / 8)`;
* Markov for the two one-sided tails, summed, with the choice `λ = 4 * t / |ι|`.
-/

namespace Work.Deep.GKO.OneFact

open Finset

/-- The moment generating identity: the weighted sum of `exp (λ * ∑ i, c i * (x i - 1/2))`
over the cube is the product of the per-coordinate hyperbolic cosines. -/
theorem pairedDeviation_mgf_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (lam : ℝ) :
    (∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        Real.exp (lam * ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)))
      = ∏ i, Real.cosh (lam * c i / 2) := by
  have hW : ((1 : ℝ) / 2) ^ (Fintype.card ι) = ∏ _i : ι, ((1 : ℝ) / 2) := by
    rw [Finset.prod_const, Finset.card_univ]
  have hE : ∀ x : ι → Bool,
      Real.exp (lam * ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2))
        = ∏ i, Real.exp (lam * (c i * ((if x i then (1 : ℝ) else 0) - 1 / 2))) := by
    intro x
    rw [Finset.mul_sum, Real.exp_sum]
  rw [hW]
  calc ∑ x : ι → Bool, (∏ _i : ι, ((1 : ℝ) / 2)) *
        Real.exp (lam * ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2))
      = ∑ x : ι → Bool, ∏ i, (((1 : ℝ) / 2) *
          Real.exp (lam * (c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)))) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hE x, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool, (((1 : ℝ) / 2) *
          Real.exp (lam * (c i * ((if b then (1 : ℝ) else 0) - 1 / 2)))) := by
        have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset Bool))
          (g := fun i (b : Bool) =>
            ((1 : ℝ) / 2) * Real.exp (lam * (c i * ((if b then (1 : ℝ) else 0) - 1 / 2))))
        rw [Fintype.piFinset_univ] at h
        simpa using h
    _ = ∏ i, Real.cosh (lam * c i / 2) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [Fintype.sum_bool, Real.cosh_eq]
        simp only [if_true, if_false, Bool.false_eq_true]
        rw [show lam * (c i * (1 - 1 / 2)) = lam * c i / 2 by ring,
            show lam * (c i * (0 - 1 / 2)) = -(lam * c i / 2) by ring]
        ring

/-- Hoeffding's exponential moment bound for the weighted Bernoulli sum. -/
theorem pairedDeviation_mgf_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (lam : ℝ) :
    (∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        Real.exp (lam * ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)))
      ≤ Real.exp (lam ^ 2 * (∑ i, (c i) ^ 2) / 8) := by
  rw [pairedDeviation_mgf_eq c lam]
  calc ∏ i, Real.cosh (lam * c i / 2)
      ≤ ∏ i, Real.exp ((lam * c i / 2) ^ 2 / 2) :=
        Finset.prod_le_prod₀ (fun i _ => le_of_lt (Real.cosh_pos _))
          (fun i _ => Real.cosh_le_exp_half_sq _)
    _ = Real.exp (∑ i, (lam * c i / 2) ^ 2 / 2) := by rw [Real.exp_sum]
    _ = Real.exp (lam ^ 2 * (∑ i, (c i) ^ 2) / 8) := by
        congr 1
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- Upper one-sided tail. -/
theorem pairedDeviation_upper_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) {lam t : ℝ} (hlam : 0 ≤ lam) :
    (∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        (if t ≤ ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2) then 1 else 0))
      ≤ Real.exp (lam ^ 2 * (∑ i, (c i) ^ 2) / 8 - lam * t) := by
  have hw : ∀ x : ι → Bool, (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (Fintype.card ι) := fun _ => by
    positivity
  have hterm : ∀ x : ι → Bool,
      ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        (if t ≤ ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2) then 1 else 0)
      ≤ ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        Real.exp (lam * ((∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) - t)) := by
    intro x
    apply mul_le_mul_of_nonneg_left _ (hw x)
    by_cases h : t ≤ ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)
    · rw [if_pos h]
      calc (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (lam * ((∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) - t)) :=
            Real.exp_le_exp.mpr (mul_nonneg hlam (by linarith))
    · rw [if_neg h]
      exact Real.exp_nonneg _
  calc ∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        (if t ≤ ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2) then 1 else 0)
      ≤ ∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
          Real.exp (lam * ((∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) - t)) :=
        Finset.sum_le_sum (fun x _ => hterm x)
    _ = Real.exp (-(lam * t)) * ∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
          Real.exp (lam * ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [show lam * ((∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) - t)
              = -(lam * t) + lam * ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2) by
            ring,
          Real.exp_add]
        ring
    _ ≤ Real.exp (-(lam * t)) * Real.exp (lam ^ 2 * (∑ i, (c i) ^ 2) / 8) :=
        mul_le_mul_of_nonneg_left (pairedDeviation_mgf_le c lam) (Real.exp_nonneg _)
    _ = Real.exp (lam ^ 2 * (∑ i, (c i) ^ 2) / 8 - lam * t) := by
        rw [← Real.exp_add]; congr 1; ring

/-- Lower one-sided tail. -/
theorem pairedDeviation_lower_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) {lam t : ℝ} (hlam : 0 ≤ lam) :
    (∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        (if t ≤ -(∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) then 1 else 0))
      ≤ Real.exp (lam ^ 2 * (∑ i, (c i) ^ 2) / 8 - lam * t) := by
  have hw : ∀ x : ι → Bool, (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (Fintype.card ι) := fun _ => by
    positivity
  have hterm : ∀ x : ι → Bool,
      ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        (if t ≤ -(∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) then 1 else 0)
      ≤ ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        Real.exp (-(lam * ((∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) + t))) := by
    intro x
    apply mul_le_mul_of_nonneg_left _ (hw x)
    by_cases h : t ≤ -(∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2))
    · rw [if_pos h]
      calc (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (-(lam * ((∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) + t))) :=
            Real.exp_le_exp.mpr (by nlinarith [hlam, h])
    · rw [if_neg h]
      exact Real.exp_nonneg _
  calc ∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        (if t ≤ -(∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) then 1 else 0)
      ≤ ∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
          Real.exp (-(lam * ((∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) + t))) :=
        Finset.sum_le_sum (fun x _ => hterm x)
    _ = Real.exp (-(lam * t)) * ∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
          Real.exp ((-lam) * ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [show -(lam * ((∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) + t))
              = -(lam * t) + (-lam) * ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2) by
            ring,
          Real.exp_add]
        ring
    _ ≤ Real.exp (-(lam * t)) * Real.exp ((-lam) ^ 2 * (∑ i, (c i) ^ 2) / 8) :=
        mul_le_mul_of_nonneg_left (pairedDeviation_mgf_le c (-lam)) (Real.exp_nonneg _)
    _ = Real.exp (lam ^ 2 * (∑ i, (c i) ^ 2) / 8 - lam * t) := by
        rw [← Real.exp_add]; congr 1; ring

/-- The absolute-value indicator is at most the sum of the two one-sided indicators. -/
theorem pairedDeviation_indicator_abs (t z : ℝ) :
    (if t ≤ |z| then (1 : ℝ) else 0) ≤ (if t ≤ z then 1 else 0) + (if t ≤ -z then 1 else 0) := by
  by_cases h : t ≤ |z|
  · rw [if_pos h]
    rcases le_abs.mp h with h' | h'
    · rw [if_pos h']
      have h2 : (0 : ℝ) ≤ (if t ≤ -z then 1 else 0) := by split_ifs <;> norm_num
      linarith
    · rw [if_pos h']
      have h2 : (0 : ℝ) ≤ (if t ≤ z then 1 else 0) := by split_ifs <;> norm_num
      linarith
  · rw [if_neg h]
    have h2 : (0 : ℝ) ≤ (if t ≤ z then 1 else 0) := by split_ifs <;> norm_num
    have h3 : (0 : ℝ) ≤ (if t ≤ -z then 1 else 0) := by split_ifs <;> norm_num
    linarith

theorem pairedDeviation_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        (if t ≤ |∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)| then 1 else 0))
      ≤ 2 * Real.exp (-(2 * t ^ 2) / (Fintype.card ι)) := by
  -- the sub-gaussian parameter is at most the number of coordinates
  have hSle : (∑ i, (c i) ^ 2) ≤ (Fintype.card ι : ℝ) := by
    have h1 : ∀ i, (c i) ^ 2 ≤ (1 : ℝ) := fun i => by
      rw [← sq_abs (c i)]
      exact pow_le_one₀ (abs_nonneg _) (hc i)
    calc ∑ i, (c i) ^ 2 ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => h1 i)
      _ = (Fintype.card ι : ℝ) := by simp
  -- the arithmetic choice `λ = 4 * t / |ι|`
  have hlam0 : (0 : ℝ) ≤ 4 * t / (Fintype.card ι : ℝ) := by positivity
  have hfinal : (4 * t / (Fintype.card ι : ℝ)) ^ 2 * (∑ i, (c i) ^ 2) / 8
        - (4 * t / (Fintype.card ι : ℝ)) * t
      ≤ -(2 * t ^ 2) / (Fintype.card ι : ℝ) := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg (Fintype.card ι) :
        (0 : ℝ) ≤ (Fintype.card ι : ℝ)) with hN0 | hNpos
    · rw [← hN0]; simp
    · have hNne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hNpos
      field_simp
      nlinarith [hSle, sq_nonneg t]
  -- pointwise splitting of the absolute-value indicator
  have hpoint : ∀ x : ι → Bool,
      ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        (if t ≤ |∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)| then 1 else 0)
      ≤ ((1 : ℝ) / 2) ^ (Fintype.card ι) *
          (if t ≤ ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2) then 1 else 0)
        + ((1 : ℝ) / 2) ^ (Fintype.card ι) *
          (if t ≤ -(∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) then 1 else 0) := by
    intro x
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      (pairedDeviation_indicator_abs t (∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)))
      (by positivity)
  calc ∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        (if t ≤ |∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)| then 1 else 0)
      ≤ ∑ x : ι → Bool, (((1 : ℝ) / 2) ^ (Fintype.card ι) *
            (if t ≤ ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2) then 1 else 0)
          + ((1 : ℝ) / 2) ^ (Fintype.card ι) *
            (if t ≤ -(∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) then 1 else 0)) :=
        Finset.sum_le_sum (fun x _ => hpoint x)
    _ = (∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
            (if t ≤ ∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2) then 1 else 0))
          + (∑ x : ι → Bool, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
            (if t ≤ -(∑ i, c i * ((if x i then (1 : ℝ) else 0) - 1 / 2)) then 1 else 0)) := by
        rw [Finset.sum_add_distrib]
    _ ≤ Real.exp ((4 * t / (Fintype.card ι : ℝ)) ^ 2 * (∑ i, (c i) ^ 2) / 8
            - (4 * t / (Fintype.card ι : ℝ)) * t)
          + Real.exp ((4 * t / (Fintype.card ι : ℝ)) ^ 2 * (∑ i, (c i) ^ 2) / 8
            - (4 * t / (Fintype.card ι : ℝ)) * t) :=
        add_le_add (pairedDeviation_upper_tail c hlam0) (pairedDeviation_lower_tail c hlam0)
    _ = 2 * Real.exp ((4 * t / (Fintype.card ι : ℝ)) ^ 2 * (∑ i, (c i) ^ 2) / 8
            - (4 * t / (Fintype.card ι : ℝ)) * t) := by ring
    _ ≤ 2 * Real.exp (-(2 * t ^ 2) / (Fintype.card ι : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hfinal) (by norm_num)

end Work.Deep.GKO.OneFact
