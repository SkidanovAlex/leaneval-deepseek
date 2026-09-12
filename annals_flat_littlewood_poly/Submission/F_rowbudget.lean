import Mathlib
import Submission.LMProbs
import Submission.LMMeas
import Submission.F_rowtail

/-!
Budget for frozen rows: E|B_T| ≤ 7n/36 (child task).

TASK: prove `frozenRows_card_integral` and `row_budget` below.
Add helpers above as needed.

`row_budget` conclusion:  Σ_j P(j is frozen after T steps) ≤ 7n/36.

The proof combines three ingredients:
 (1) `frozenRows_card_integral`:
       ∫ ω, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) = Σ_j P(j ∈ B_T).
     The cardinal is Σ_j (if j ∈ B_T then 1 else 0) (Finset.card_eq_sum_ones /
     `frozenRows_card_eq_sum'` in Submission.LMMeas), real integrals are linear,
     and ∫ of an indicator 1_{j ∈ B_T} equals the real measure
     `(mu n T).real {ω | j ∈ frozenRows ...}` via
     `MeasureTheory.integral_indicator_one` (the indicator equals the
     characteristic function of the measurable set; the sets are measurable by
     `measurableSet_frozen_row` in Submission.LMMeas).
 (2) `row_frozen_prob_le` (Submission.F_rowtail), for rows with ‖v j‖ ≠ 0 and
     δ ≤ c j:
       P(j ∈ B_T) ≤ 2·exp(-(c j - δ)² / (2 γ² T)).
 (3) Split rows into J := {j | c j ≤ 10 δ} and its complement.
     * |J|·(15/16) ≤ |J|·exp(-1/16) ≤ Σ_{j∈J} exp(-(c j)²/16) ≤ n/16, because
       c j ≤ 10δ ≤ 1 gives -(c j)²/16 ≥ -1/16 and exp(-1/16) ≥ 15/16
       (use the standard bound exp(-x) ≥ 1 - x for x ≥ 0, or
       `Real.exp_neg` + `one_sub_le_exp`-type lemmas, or any other proof);
       hence |J| ≤ (10/9)·n/16·(15/16)^{-1}...  actually |J| ≤ (n/16)/(15/16)
       = n/15 is NOT what we want; we only need |J| ≤ 5n/72, which follows
       from |J|·(9/10) ≤ n/16 because 15/16 > 9/10.  So prove |J|·(9/10) ≤ n/16
       using exp(-1/16) ≥ 15/16 > 9/10, and conclude |J| ≤ (5/72)·n (nlinarith
       on reals after clearing the denominator).
     * For j ∉ J: c j > 10δ, so δ ≤ c j and c j - δ > 0.9·c j, and
       row_frozen_prob_le gives
         P(j ∈ B_T) ≤ 2 exp(-(0.9 c j)²/(2γ²T)).
       Since γ²T ≤ 6, 0.9²/(2γ²T) ≥ 0.81/12 = 27/400 ≥ 1/16, so
         2 exp(-(0.9 c j)²/(2γ²T)) ≤ 2 exp(-(c j)²/16)
       (exp is decreasing: compare the arguments; all squared quantities ≥ 0).
       Hence Σ_{j∉J} P(j ∈ B_T) ≤ Σ_{j∉J} 2 exp(-(c j)²/16) ≤ 2·(n/16) = n/8.
     Sum:  E|B_T| ≤ |J| + n/8 ≤ 5n/72 + n/8 = 5n/72 + 9n/72 = 14n/72 = 7n/36.
     (5/72 = 5·n/72?  careful: |J|·(9/10) ≤ n/16 gives |J| ≤ (10/9)(n/16) =
     5n/72.)  All arithmetic in ℝ; conclude with nlinarith/ring.

NOTE on notation: P(j frozen) is `(mu n T).real {ω : Omega n T |
j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)}`.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy

/-- The expected number of frozen rows is the sum of the per-row frozen
probabilities. -/
lemma frozenRows_card_integral {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) :
    (∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T)) =
      ∑ j : ι, (mu n T).real {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)} := by
  let S : ι → Set (Omega n T) := fun j =>
    {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)}
  have hmeasS : ∀ j : ι, MeasurableSet (S j) := by
    intro j
    exact measurableSet_frozen_row (n := n) (ι := ι) (T := T) (t := T) (le_refl T) δ γ x0 v c j
  have hintg : ∀ j : ι,
      Integrable (fun ω : Omega n T => (S j).indicator (fun _ : Omega n T => (1 : ℝ)) ω)
        (mu n T) := by
    intro j
    exact (integrableOn_const (μ := mu n T) (s := S j) (C := (1 : ℝ))).integrable_indicator
      (hmeasS j)
  have hcard : (fun ω : Omega n T => ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ)) =
      fun ω => ∑ j : ι, (S j).indicator (fun _ : Omega n T => (1 : ℝ)) ω := by
    funext ω
    rw [frozenRows_card_eq_sum' (n := n) (T := T) (t := T) (le_refl T) δ γ x0 v c ω]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Set.indicator_apply]
    by_cases h : j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)
    · have hmem : ω ∈ S j := by simp [S, h]
      simp [hmem, h]
    · have hmem : ω ∉ S j := by simp [S, h]
      simp [hmem, h]
  calc
    (∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))
        = ∫ ω : Omega n T, ∑ j : ι,
            (S j).indicator (fun _ : Omega n T => (1 : ℝ)) ω ∂(mu n T) := by
            rw [hcard]
    _ = ∑ j : ι, ∫ ω : Omega n T,
          (S j).indicator (fun _ : Omega n T => (1 : ℝ)) ω ∂(mu n T) := by
          exact integral_finsetSum (s := (Finset.univ : Finset ι))
            (f := fun j => fun ω : Omega n T => (S j).indicator (fun _ : Omega n T => (1 : ℝ)) ω)
            (fun j hj => hintg j)
    _ = ∑ j : ι, (mu n T).real (S j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [integral_indicator_const (e := (1 : ℝ)) (s := S j) (s_meas := hmeasS j)]
          simp
    _ = ∑ j : ι, (mu n T).real {ω : Omega n T |
          j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)} := by
          simp [S]

/-- For a row with `10 δ < c j`, the frozen probability is bounded by the
`2·exp(-(c j)²/16)` term of the discrepancy sum. -/
lemma frozen_prob_of_gt {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (hγ : 0 < γ) (hT1 : 1 ≤ T) (hKle : γ ^ 2 * (T : ℝ) ≤ 6) {j : ι}
    (hcj : 0 ≤ c j) (hgt : 10 * δ < c j) (hne : ‖v j‖ ≠ 0) :
    (mu n T).real {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)} ≤
      2 * Real.exp (-(c j) ^ 2 / 16) := by
  have hδle : δ ≤ c j := by
    by_cases hδ0 : δ ≤ 0
    · exact le_trans hδ0 hcj
    · have hδpos : 0 < δ := lt_of_not_ge hδ0
      nlinarith
  have hT0 : (0 : ℝ) < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hT1)
  have hg2 : 0 < γ ^ 2 := sq_pos_of_ne_zero hγ.ne'
  have hden : 0 < 2 * γ ^ 2 * (T : ℝ) := by
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hg2) hT0
  have hrow := row_frozen_prob_le (n := n) (T := T) (δ := δ) (γ := γ) (x0 := x0) (v := v)
    (c := c) hγ hT1 (hvj := hne) (hcj := hδle)
  have h1 : (9 / 10) * c j ≤ c j - δ := by nlinarith [le_of_lt hgt]
  have hnon : 0 ≤ (9 / 10) * c j := by positivity
  have hd0 : 0 ≤ c j - δ := by nlinarith
  have hsq : ((9 / 10) * c j) ^ 2 ≤ (c j - δ) ^ 2 := by
    nlinarith [mul_le_mul h1 h1 hnon hd0]
  have hE : Real.exp (-(c j - δ) ^ 2 / (2 * γ ^ 2 * (T : ℝ))) ≤
      Real.exp (-(c j) ^ 2 / 16) := by
    apply Real.exp_le_exp.2
    have hE0 : (c j) ^ 2 / 16 ≤ (c j - δ) ^ 2 / (2 * γ ^ 2 * (T : ℝ)) := by
      field_simp [hden.ne']
      nlinarith [hKle, hsq, sq_nonneg (c j)]
    simpa [neg_div] using neg_le_neg hE0
  calc
    (mu n T).real {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)}
        ≤ 2 * Real.exp (-(c j - δ) ^ 2 / (2 * γ ^ 2 * (T : ℝ))) := hrow
    _ ≤ 2 * Real.exp (-(c j) ^ 2 / 16) := mul_le_mul_of_nonneg_left hE (by norm_num)

/-- Budget on the expected number of frozen rows after T steps. -/
lemma row_budget {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (hγ : 0 < γ) (hT1 : 1 ≤ T) (hKle : γ ^ 2 * (T : ℝ) ≤ 6) (hδ10 : δ ≤ 1 / 10)
    (hc : ∀ j : ι, 0 ≤ c j) (hne : ∀ j : ι, ‖v j‖ ≠ 0)
    (hsum : ∑ j : ι, Real.exp (-(c j) ^ 2 / 16) ≤ (n : ℝ) / 16) :
    ∑ j : ι, (mu n T).real {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)} ≤
      (7 / 36) * (n : ℝ) := by
  let P : ι → ℝ := fun j =>
    (mu n T).real {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)}
  let J := Finset.univ.filter (fun j : ι => c j ≤ 10 * δ)
  let K := Finset.univ.filter (fun j : ι => ¬ c j ≤ 10 * δ)
  have hP1 : ∀ j : ι, P j ≤ 1 := by
    intro j
    dsimp [P]
    exact measureReal_le_one
  have hJexp : ∀ j : ι, j ∈ J → (15 / 16 : ℝ) ≤ Real.exp (-(c j) ^ 2 / 16) := by
    intro j hj
    have hmem : c j ≤ 10 * δ := by simpa [J] using hj
    have hcj1 : c j ≤ 1 := by nlinarith [hmem, hδ10]
    have hsq1 : (c j) ^ 2 ≤ 1 := by nlinarith [hc j, hcj1]
    have hcmp : -(1 : ℝ) ^ 2 / 16 ≤ -(c j) ^ 2 / 16 := by nlinarith
    have h_exp : Real.exp (-(1 : ℝ) ^ 2 / 16) ≤ Real.exp (-(c j) ^ 2 / 16) :=
      (Real.exp_le_exp).2 hcmp
    have h1516 : (15 / 16 : ℝ) ≤ Real.exp (-(1 : ℝ) ^ 2 / 16) := by
      have h0 := Real.one_sub_le_exp_neg ((1 : ℝ) / 16)
      norm_num at h0 ⊢
      exact h0
    exact le_trans h1516 h_exp
  have hPJ : ∑ j ∈ J, P j ≤ (J.card : ℝ) := by
    calc
      (∑ j ∈ J, P j) ≤ ∑ j ∈ J, (1 : ℝ) := Finset.sum_le_sum (by intro j hj; exact hP1 j)
      _ = (J.card : ℝ) := by simp
  have hJcount : (J.card : ℝ) * (15 / 16) ≤ (n : ℝ) / 16 := by
    calc
      (J.card : ℝ) * (15 / 16) = ∑ j ∈ J, (15 / 16 : ℝ) := by
        rw [Finset.sum_const]
        simp
      _ ≤ ∑ j ∈ J, Real.exp (-(c j) ^ 2 / 16) :=
        Finset.sum_le_sum (fun j hj => hJexp j hj)
      _ ≤ ∑ j : ι, Real.exp (-(c j) ^ 2 / 16) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro j hj
          exact Finset.mem_univ j
        · intro j _ _
          exact (Real.exp_pos _).le
      _ ≤ (n : ℝ) / 16 := hsum
  have hJcard : (J.card : ℝ) ≤ (5 / 72) * (n : ℝ) := by
    have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    nlinarith
  have hPtail : ∀ j : ι, j ∈ K → P j ≤ 2 * Real.exp (-(c j) ^ 2 / 16) := by
    intro j hj
    have hmem : ¬ c j ≤ 10 * δ := by simpa [K] using hj
    have hgt : 10 * δ < c j := lt_of_not_ge hmem
    exact frozen_prob_of_gt n T δ γ x0 v c hγ hT1 hKle (hc j) hgt (hne j)
  have hKle_sumP : ∑ j ∈ K, P j ≤ ∑ j ∈ K, 2 * Real.exp (-(c j) ^ 2 / 16) :=
    Finset.sum_le_sum (by intro j hj; exact hPtail j hj)
  have hKexp : ∑ j ∈ K, 2 * Real.exp (-(c j) ^ 2 / 16) ≤ 2 * ((n : ℝ) / 16) := by
    calc
      (∑ j ∈ K, 2 * Real.exp (-(c j) ^ 2 / 16))
          ≤ ∑ j : ι, 2 * Real.exp (-(c j) ^ 2 / 16) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro j hj
              exact Finset.mem_univ j
            · intro j _ _
              exact mul_nonneg (by norm_num) (Real.exp_pos _).le
      _ = 2 * (∑ j : ι, Real.exp (-(c j) ^ 2 / 16)) := by
            rw [Finset.mul_sum]
      _ ≤ 2 * ((n : ℝ) / 16) := mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hK : ∑ j ∈ K, P j ≤ 2 * ((n : ℝ) / 16) := le_trans hKle_sumP hKexp
  have hPboundJ : ∑ j ∈ J, P j ≤ (5 / 72) * (n : ℝ) := le_trans hPJ hJcard
  calc
    (∑ j : ι, (mu n T).real {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)})
        = ∑ j : ι, P j := by
            rfl
    _ = (∑ j ∈ J, P j) + ∑ j ∈ K, P j := by
            dsimp [J, K]
            rw [Finset.sum_filter_add_sum_filter_not]
    _ ≤ (5 / 72) * (n : ℝ) + 2 * ((n : ℝ) / 16) := add_le_add hPboundJ hK
    _ ≤ (7 / 36) * (n : ℝ) := by nlinarith

end Discrepancy

end Submission
