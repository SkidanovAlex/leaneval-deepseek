import Submission.Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted

/-!
# Finite sampling: a subset with prescribed intersection sizes

Fix a finite ground set `E`, a target density `p ∈ [0,1]`, a finite family `(A i)` of
subsets of `E` and tolerances `t i ≥ 0`.  If the union bound
`∑ i, 2 * exp (-(t i)² / (2 * (p * |A i| + t i / 3)))`
is strictly smaller than `1`, then there is a subset `R ⊆ E` whose intersection with
every `A i` deviates from `p * |A i|` by at most `t i`.

The proof is the probabilistic method: sample `R` by including every element of `E`
independently with probability `p`.  For each `i`, the random variable `|R ∩ A i|` is a
sum of `|A i|` independent Bernoulli(`p`) variables, so the weighted Chernoff bound
`Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted` (with the constant
`C = 1`, i.e. `X e = 1_{e ∈ A i}`) controls the probability that it deviates from its
mean `p * |A i|` by at least `t i`.  Summing over `i` with the union bound gives a total
failure probability `< 1`, hence some outcome survives, and that outcome yields the
required set `R`.
-/

namespace Commons.Combinatorics.FiniteSampling

open Finset

section Sampling

variable {E ι : Type*} [Fintype E] [DecidableEq E] [Fintype ι]

/-- `∑ e, p * 1_{e ∈ A} = p * |A|`. -/
private lemma sum_mul_indic (p : ℝ) (A : Finset E) :
    (∑ e : E, p * (if e ∈ A then (1 : ℝ) else 0)) = p * (A.card : ℝ) := by
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The number of sampled elements of `A`, both as a sum over `E` and as a sum over `A`. -/
private lemma sum_indic_bool (A : Finset E) (x : E → Bool) :
    (∑ e : E, (if x e then (if e ∈ A then (1 : ℝ) else 0) else 0))
      = ∑ e ∈ A, (if x e then (1 : ℝ) else 0) := by
  rw [show (∑ e : E, (if x e then (if e ∈ A then (1 : ℝ) else 0) else 0))
      = ∑ e : E, (if e ∈ A then (if x e then (1 : ℝ) else 0) else 0) from
    Finset.sum_congr rfl
      (fun e _ => by by_cases hx : x e <;> by_cases he : e ∈ A <;> simp [hx, he])]
  rw [Finset.sum_ite_mem_eq]

/-- Two-sided Chernoff tail for the number of sampled elements of a finite set. -/
private lemma tail_two_sided (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset E) (τ : ℝ)
    (hτ : 0 ≤ τ) :
    (∑ x : E → Bool, (∏ e : E, (if x e then p else 1 - p)) *
        (if τ ≤ |(∑ e ∈ A, (if x e then (1 : ℝ) else 0)) - p * (A.card : ℝ)| then 1 else 0))
      ≤ 2 * Real.exp (-(τ ^ 2) / (2 * (p * (A.card : ℝ) + τ / 3))) := by
  have key := Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted
    (ι := E) (p := fun _ : E => p) (fun _ => hp0) (fun _ => hp1)
    (X := fun e : E => if e ∈ A then (1 : ℝ) else 0) (fun e => by split_ifs <;> norm_num)
    (C := 1) zero_le_one (fun e => by split_ifs <;> norm_num) (t := τ) hτ
  simp only [sum_indic_bool, sum_mul_indic, mul_one] at key
  exact key

/-- Union bound: the total weight of the event that some index `i` has a large deviation
is at most the sum of the individual tail bounds. -/
private lemma sum_bad_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : ι → Finset E) (τ : ι → ℝ) (hτ : ∀ i, 0 ≤ τ i) :
    (∑ x : E → Bool, (∏ e : E, (if x e then p else 1 - p)) *
        (if ∃ i : ι, τ i ≤
            |(∑ e ∈ A i, (if x e then (1 : ℝ) else 0)) - p * ((A i).card : ℝ)| then 1 else 0))
      ≤ ∑ i : ι, 2 * Real.exp (-(τ i ^ 2) / (2 * (p * ((A i).card : ℝ) + τ i / 3))) := by
  classical
  have key : ∀ x : E → Bool,
      (if ∃ i : ι, τ i ≤
          |(∑ e ∈ A i, (if x e then (1 : ℝ) else 0)) - p * ((A i).card : ℝ)| then (1 : ℝ) else 0)
        ≤ ∑ i : ι, (if τ i ≤
            |(∑ e ∈ A i, (if x e then (1 : ℝ) else 0)) - p * ((A i).card : ℝ)| then (1 : ℝ) else 0) := by
    intro x
    by_cases h : ∃ i : ι, τ i ≤
        |(∑ e ∈ A i, (if x e then (1 : ℝ) else 0)) - p * ((A i).card : ℝ)|
    · rw [if_pos h]
      obtain ⟨i, hi⟩ := h
      have hle : (if τ i ≤
            |(∑ e ∈ A i, (if x e then (1 : ℝ) else 0)) - p * ((A i).card : ℝ)| then (1 : ℝ) else 0)
          ≤ ∑ j : ι, (if τ j ≤
            |(∑ e ∈ A j, (if x e then (1 : ℝ) else 0)) - p * ((A j).card : ℝ)| then (1 : ℝ) else 0) :=
        Finset.single_le_sum
          (f := fun j : ι => if τ j ≤
            |(∑ e ∈ A j, (if x e then (1 : ℝ) else 0)) - p * ((A j).card : ℝ)| then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
      rwa [if_pos hi] at hle
    · rw [if_neg h]
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
  calc ∑ x : E → Bool, (∏ e : E, (if x e then p else 1 - p)) *
        (if ∃ i : ι, τ i ≤
            |(∑ e ∈ A i, (if x e then (1 : ℝ) else 0)) - p * ((A i).card : ℝ)| then 1 else 0)
      ≤ ∑ x : E → Bool, (∏ e : E, (if x e then p else 1 - p)) *
          ∑ i : ι, (if τ i ≤
            |(∑ e ∈ A i, (if x e then (1 : ℝ) else 0)) - p * ((A i).card : ℝ)| then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (key x)
          (Finset.prod_nonneg fun e _ => by split_ifs <;> linarith)
    _ = ∑ i : ι, ∑ x : E → Bool, (∏ e : E, (if x e then p else 1 - p)) *
          (if τ i ≤ |(∑ e ∈ A i, (if x e then (1 : ℝ) else 0)) - p * ((A i).card : ℝ)| then 1 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
    _ ≤ ∑ i : ι, 2 * Real.exp (-(τ i ^ 2) / (2 * (p * ((A i).card : ℝ) + τ i / 3))) :=
        Finset.sum_le_sum fun i _ => tail_two_sided p hp0 hp1 (A i) (τ i) (hτ i)

end Sampling

/-- **Finite sampling.** Given a finite ground set `E`, a density `p ∈ [0,1]`, a finite
family of subsets `A i ⊆ E` and tolerances `t i ≥ 0`, if
`∑ i, 2 * exp (-(t i)² / (2 * (p |A i| + t i / 3))) < 1` then there is a subset `R ⊆ E`
with `| |R ∩ A i| - p |A i| | ≤ t i` for every `i`. -/
theorem exists_finset_sum_close {E ι : Type*} [Fintype E] [DecidableEq E] [Fintype ι]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {A : ι → Finset E} {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i)
    (hbad : (Finset.univ.sum fun i : ι =>
        2 * Real.exp (-((t i) ^ 2) / (2 * (p * ((A i).card : ℝ) + t i / 3)))) < 1) :
    ∃ R : Finset E, ∀ i : ι,
      |(((R ∩ A i).card : ℝ)) - p * ((A i).card : ℝ)| ≤ t i := by
  classical
  have htot : (∑ x : E → Bool, ∏ e : E, (if x e then p else 1 - p)) = 1 :=
    Commons.Probability.Chernoff.sum_weight_eq_one (fun _ : E => p)
  have hbound := sum_bad_bound p hp0 hp1 A t ht
  have hlt : (∑ x : E → Bool, (∏ e : E, (if x e then p else 1 - p)) *
      (if ∃ i : ι, t i ≤
          |(∑ e ∈ A i, (if x e then (1 : ℝ) else 0)) - p * ((A i).card : ℝ)| then 1 else 0)) < 1 :=
    lt_of_le_of_lt hbound hbad
  have hex : ∃ x : E → Bool, ∀ i : ι,
      ¬ (t i ≤ |(∑ e ∈ A i, (if x e then (1 : ℝ) else 0)) - p * ((A i).card : ℝ)|) := by
    by_contra hcon
    push Not at hcon
    have : (∑ x : E → Bool, (∏ e : E, (if x e then p else 1 - p)) *
        (if ∃ i : ι, t i ≤
            |(∑ e ∈ A i, (if x e then (1 : ℝ) else 0)) - p * ((A i).card : ℝ)| then 1 else 0))
        = ∑ x : E → Bool, ∏ e : E, (if x e then p else 1 - p) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [if_pos (hcon x)]
      ring
    linarith
  obtain ⟨x, hx⟩ := hex
  refine ⟨Finset.univ.filter (fun e => x e), ?_⟩
  intro i
  have hcard : (((Finset.univ.filter (fun e => x e)) ∩ A i).card : ℝ)
      = ∑ e ∈ A i, (if x e then (1 : ℝ) else 0) := by
    have h1 : (Finset.univ.filter (fun e => x e)) ∩ A i = (A i).filter (fun e => x e) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and]
      exact and_comm
    rw [h1, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp
  rw [hcard]
  exact le_of_lt (not_le.mp (hx i))

end Commons.Combinatorics.FiniteSampling
