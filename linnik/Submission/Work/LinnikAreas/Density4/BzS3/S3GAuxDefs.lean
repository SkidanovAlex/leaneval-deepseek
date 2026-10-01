/-
# Auxiliary objects for the sharp two-Abel estimate for `s3G`

This file collects the definitions used by
`Work.LinnikAreas.Density4.BzS3.S3G_abel_sharp` and by the pieces it is assembled from.

* `sqfreeCop c m = μ(m)²·[m ⊥ c]` is the indicator of the squarefree integers coprime to `c`
  (as a real number);
* `wfun α β m = (log m − α)(log m − β)` is the Abel weight.

The Abel summation producing `s3G c α β X = Σ_{m ≤ X} sqfreeCop c m · wfun α β m`
is then compared against the squarefree-coprime count
`Work.LinnikAreas.Density4.squarefree_coprime_count`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.BzS3.S3InnerDefs

namespace Work.LinnikAreas.Density4.BzS3

open Finset

noncomputable section

/-- `μ(m)²·[m ⊥ c]`: the indicator of the squarefree integers coprime to `c`, as a real number. -/
def sqfreeCop (c : ℕ) (m : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius m : ℝ)) ^ 2 * (if Nat.Coprime m c then 1 else 0)

/-- The Abel weight `w(m) = (log m − α)·(log m − β)`. -/
def wfun (α β : ℝ) (m : ℕ) : ℝ := (Real.log (m : ℝ) - α) * (Real.log (m : ℝ) - β)

lemma sqfreeCop_nonneg (c m : ℕ) : 0 ≤ sqfreeCop c m := by
  unfold sqfreeCop
  split_ifs <;> positivity

lemma sqfreeCop_eq_ite (c m : ℕ) :
    sqfreeCop c m = if Nat.Coprime m c then ((ArithmeticFunction.moebius m : ℝ)) ^ 2 else 0 := by
  unfold sqfreeCop
  by_cases h : Nat.Coprime m c <;> simp [h]

/-- The sum of `sqfreeCop c ·` over `Icc 1 M` is the Möbius-square sum over the coprime class,
i.e. the quantity estimated by `Work.LinnikAreas.Density4.squarefree_coprime_count`. -/
lemma sum_sqfreeCop_eq_sum_filter (c M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, sqfreeCop c m
      = ∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m c),
          ((ArithmeticFunction.moebius m : ℝ)) ^ 2 := by
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun m _ => sqfreeCop_eq_ite c m

lemma s3c_nonneg (c : ℕ) : 0 ≤ s3c c := by
  unfold s3c
  have h1 : (0:ℝ) < Real.pi ^ 2 / 6 := by positivity
  have h2 : 0 ≤ ∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1) := by
    apply Finset.prod_nonneg
    intro p hp
    positivity
  positivity

lemma s3c_le_one (c : ℕ) : s3c c ≤ 1 := by
  unfold s3c
  have hpi : (1:ℝ) < Real.pi ^ 2 / 6 := by
    have h3 := Real.pi_gt_three
    nlinarith [Real.pi_pos]
  have h1 : (Real.pi ^ 2 / 6)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact le_of_lt hpi
  have h2 : ∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro p hp
      have hp2 : (0:ℝ) ≤ (p:ℝ) := by positivity
      have : (0:ℝ) < (p:ℝ) + 1 := by linarith
      exact div_nonneg hp2 this.le
    · intro p hp
      have hp2 : (0:ℝ) ≤ (p:ℝ) := by positivity
      rw [div_le_one (by linarith)]
      linarith
  calc (Real.pi ^ 2 / 6)⁻¹ * ∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1)
      ≤ 1 * 1 := by
        apply mul_le_mul h1 h2
        · exact Finset.prod_nonneg (fun p hp => by positivity)
        · norm_num
    _ = 1 := by norm_num

end

end Work.LinnikAreas.Density4.BzS3
