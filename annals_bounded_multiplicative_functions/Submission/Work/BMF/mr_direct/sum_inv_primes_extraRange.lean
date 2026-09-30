import Mathlib
import Submission.Work.BMF.mr_direct.dupExtra_defs
import Submission.Work.BMF.mr_direct.sum_inv_primes_le
import Submission.Work.BMF.mr_direct.sum_inv_primes_near
import Submission.Work.BMF.mr_direct.sum_inv_primes_near_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- For nonnegative `f`, the sum over a union is at most the sum of the two sums. -/
private lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have hun : s ∪ t = s ∪ (t \ s) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rw [hun, Finset.sum_union Finset.disjoint_sdiff]
  have h2 : ∑ x ∈ t \ s, f x ≤ ∑ x ∈ t, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => hf i)
  linarith

/-- Elementary arithmetic: with `L = P e^{-1/K}` and `U = Q e^{1/K}`,
`(P + 1 - L)/L + (U + 1 - Q)/Q ≤ 32 (1/K + 1/P)` for `K ≥ 1`, `2 ≤ P ≤ Q`.

Writing `y = e^{1/K}` and using `e^{-1/K} = y⁻¹`, the left hand side equals
`(2 + 1/P) y - 2 + 1/Q = 2(y - 1) + y/P + 1/Q`, and the three pieces are bounded by
`4/K`, `3/P`, `1/P` using `y - 1 ≤ 2/K` and `y ≤ 3`. -/
private lemma extra_arith (K P Q : ℝ) (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    (P + 1 - P * Real.exp (-(1 / K))) / (P * Real.exp (-(1 / K))) +
      (Q * Real.exp (1 / K) + 1 - Q) / Q ≤ 32 * (1 / K + 1 / P) := by
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by linarith
  have hKpos : 0 < K := by linarith
  have hmain : (P + 1 - P * Real.exp (-(1 / K))) / (P * Real.exp (-(1 / K))) +
      (Q * Real.exp (1 / K) + 1 - Q) / Q
      = (2 + 1 / P) * Real.exp (1 / K) + 1 / Q - 2 := by
    rw [Real.exp_neg]
    field_simp
    ring
  set y := Real.exp (1 / K) with hy
  have hy3 : y ≤ 3 := by
    have h1 : y ≤ Real.exp 1 := by
      rw [hy]; exact Real.exp_le_exp.mpr (by rw [div_le_one hKpos]; linarith)
    linarith [Real.exp_one_lt_three]
  have hyb : y - 1 ≤ 2 * (1 / K) := by
    have h2 := Real.abs_exp_sub_one_le (x := 1 / K) (by
      rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / K), div_le_one hKpos]; linarith)
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / K)] at h2
    rw [hy]
    linarith [le_abs_self (Real.exp (1 / K) - 1)]
  have hyP : (2 + 1 / P) * y + 1 / Q - 2 = 2 * (y - 1) + y / P + 1 / Q := by
    field_simp; ring
  have h2v : 2 * (y - 1) ≤ 4 / K := by
    have : 2 * (2 * (1 / K)) = 4 / K := by ring
    linarith [hyb]
  have hyP' : y / P ≤ 3 / P := div_le_div_of_nonneg_right hy3 hPpos.le
  have hQinv : 1 / Q ≤ 1 / P := one_div_le_one_div_of_le hPpos hPQ
  have hsumP : y / P + 1 / Q ≤ 4 / P := by
    have h := add_le_add hyP' hQinv
    have e2 : (3 : ℝ) / P + 1 / P = 4 / P := by ring
    linarith [h, e2]
  have hbound : 2 * (y - 1) + y / P + 1 / Q ≤ 4 / K + 4 / P := by
    have h := add_le_add h2v hsumP; linarith [h]
  have hfin : 4 / K + 4 / P ≤ 32 * (1 / K + 1 / P) := by
    have h1 : 4 / K ≤ 32 / K := div_le_div_of_nonneg_right (by norm_num) hKpos.le
    have h2 : 4 / P ≤ 32 / P := div_le_div_of_nonneg_right (by norm_num) hPpos.le
    rw [show (32 : ℝ) * (1 / K + 1 / P) = 32 / K + 32 / P by ring]
    linarith [h1, h2]
  have hgoal2 : (2 + 1 / P) * y + 1 / Q - 2 ≤ 32 * (1 / K + 1 / P) := by
    linarith [hyP, hbound, hfin]
  rw [hmain]
  exact hgoal2

theorem sum_inv_primes_extraRange (K P Q : ℝ) (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∑ p ∈ Work.BMF.mr_direct.extraRange K P Q, (1 : ℝ) / (p : ℝ) ≤ 32 * (1 / K + 1 / P) := by
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by linarith
  have hLpos : 0 < P * Real.exp (-(1 / K)) := by positivity
  have hUpos : 0 < Q * Real.exp (1 / K) := by positivity
  have hLP : P * Real.exp (-(1 / K)) ≤ P := by
    have he : Real.exp (-(1 / K)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ 1 / K := by positivity
      linarith
    calc P * Real.exp (-(1 / K)) ≤ P * 1 := mul_le_mul_of_nonneg_left he hPpos.le
      _ = P := mul_one P
  have hQU : Q ≤ Q * Real.exp (1 / K) := by
    have he : (1 : ℝ) ≤ Real.exp (1 / K) := Real.one_le_exp (by positivity)
    calc Q = Q * 1 := (mul_one Q).symm
      _ ≤ Q * Real.exp (1 / K) := mul_le_mul_of_nonneg_left he hQpos.le
  have hunion : ∑ p ∈ Work.BMF.mr_direct.extraRange K P Q, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ Work.BMF.primesIn (P * Real.exp (-(1 / K))) P, (1 : ℝ) / (p : ℝ)
        + ∑ p ∈ Work.BMF.primesIn Q (Q * Real.exp (1 / K)), (1 : ℝ) / (p : ℝ) := by
    rw [Work.BMF.mr_direct.extraRange]
    exact sum_union_le_of_nonneg _ _ _ (fun p => by positivity)
  have h1 := sum_inv_primes_le (P * Real.exp (-(1 / K))) P hLpos hLP
  have h2 := sum_inv_primes_le Q (Q * Real.exp (1 / K)) hQpos hQU
  refine le_trans hunion ?_
  refine le_trans (add_le_add h1 h2) ?_
  exact extra_arith K P Q hK hP hPQ

end Work.BMF.mr_direct
