import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum.NatFactorial

namespace Commons.Algebra.BigOperators

/-- Pascal-type identity for the exponential-type sums `∑ m, C(n,m) t^m / m!`:
the sum for `k` splits, by Pascal's rule, into the two sums for `k - 1`
consisting of the terms of degree `m` and of degree `m + 1` respectively. -/
theorem choose_pascal_sum_identity_pos (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    (∑ i ∈ Finset.range k, (((k - 1).choose i : ℕ) : ℝ) * t ^ i / (((i.factorial : ℕ) : ℝ)))
      + (∑ i ∈ Finset.range k, (((k - 1).choose i : ℕ) : ℝ) * t ^ (i + 1) / ((((i + 1).factorial : ℕ) : ℝ)))
    = ∑ m ∈ Finset.range (k + 1), (((k).choose m : ℕ) : ℝ) * t ^ m / (((m.factorial : ℕ) : ℝ)) := by
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  set g : ℕ → ℝ := fun m => t ^ m / (((m.factorial : ℕ) : ℝ)) with hg
  have hg' : ∀ m, g m = t ^ m / (((m.factorial : ℕ) : ℝ)) := by intro m; rw [hg]
  have hg0 : g 0 = 1 := by rw [hg']; norm_num
  -- Rewrite both sides in terms of the auxiliary function `g`.
  have hL : (∑ i ∈ Finset.range k, (((k - 1).choose i : ℕ) : ℝ) * t ^ i / (((i.factorial : ℕ) : ℝ)))
        + (∑ i ∈ Finset.range k, (((k - 1).choose i : ℕ) : ℝ) * t ^ (i + 1) / ((((i + 1).factorial : ℕ) : ℝ)))
      = (∑ i ∈ Finset.range k, (((k - 1).choose i : ℕ) : ℝ) * g i)
        + (∑ i ∈ Finset.range k, (((k - 1).choose i : ℕ) : ℝ) * g (i + 1)) := by
    congr 1
    · apply Finset.sum_congr rfl; intro i hi; rw [hg', mul_div_assoc]
    · apply Finset.sum_congr rfl; intro i hi; rw [hg', mul_div_assoc]
  have hR : (∑ m ∈ Finset.range (k + 1), (((k).choose m : ℕ) : ℝ) * t ^ m / (((m.factorial : ℕ) : ℝ)))
      = ∑ m ∈ Finset.range (k + 1), (((k).choose m : ℕ) : ℝ) * g m := by
    apply Finset.sum_congr rfl; intro m hm; rw [hg', mul_div_assoc]
  rw [hL, hR]
  clear hL hR
  -- Pascal's rule, pointwise.
  have hchoose : ∀ m : ℕ, ((k).choose (m + 1) : ℕ) = (k - 1).choose m + (k - 1).choose (m + 1) := by
    intro m
    have h := Nat.choose_succ_succ' (k - 1) m
    rwa [hk1] at h
  have e0 : (((k).choose 0 : ℕ) : ℝ) * g 0 = 1 := by rw [hg0]; simp
  have e1 : (((k - 1).choose 0 : ℕ) : ℝ) * g 0 = 1 := by rw [hg0]; simp
  have e2 : (((k - 1).choose k : ℕ) : ℝ) * g k = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have hsplt : (∑ m ∈ Finset.range k, (((k).choose (m + 1) : ℕ) : ℝ) * g (m + 1))
      = (∑ m ∈ Finset.range k, (((k - 1).choose (m + 1) : ℕ) : ℝ) * g (m + 1))
        + (∑ m ∈ Finset.range k, (((k - 1).choose m : ℕ) : ℝ) * g (m + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hchoose m]
    push_cast
    ring
  have h1 : (∑ m ∈ Finset.range (k + 1), (((k).choose m : ℕ) : ℝ) * g m)
      = (∑ m ∈ Finset.range k, (((k).choose (m + 1) : ℕ) : ℝ) * g (m + 1))
        + (((k).choose 0 : ℕ) : ℝ) * g 0 :=
    Finset.sum_range_succ' (fun m => (((k).choose m : ℕ) : ℝ) * g m) k
  have h2 : (∑ m ∈ Finset.range (k + 1), (((k - 1).choose m : ℕ) : ℝ) * g m)
      = (∑ m ∈ Finset.range k, (((k - 1).choose (m + 1) : ℕ) : ℝ) * g (m + 1))
        + (((k - 1).choose 0 : ℕ) : ℝ) * g 0 :=
    Finset.sum_range_succ' (fun m => (((k - 1).choose m : ℕ) : ℝ) * g m) k
  have h3 : (∑ m ∈ Finset.range (k + 1), (((k - 1).choose m : ℕ) : ℝ) * g m)
      = (∑ m ∈ Finset.range k, (((k - 1).choose m : ℕ) : ℝ) * g m)
        + (((k - 1).choose k : ℕ) : ℝ) * g k :=
    Finset.sum_range_succ (fun m => (((k - 1).choose m : ℕ) : ℝ) * g m) k
  calc
    (∑ i ∈ Finset.range k, (((k - 1).choose i : ℕ) : ℝ) * g i)
        + (∑ i ∈ Finset.range k, (((k - 1).choose i : ℕ) : ℝ) * g (i + 1))
        = ((∑ m ∈ Finset.range k, (((k - 1).choose m : ℕ) : ℝ) * g m) + 0)
          + (∑ m ∈ Finset.range k, (((k - 1).choose m : ℕ) : ℝ) * g (m + 1)) := by
              rw [add_zero]
    _ = ((∑ m ∈ Finset.range k, (((k - 1).choose m : ℕ) : ℝ) * g m) + (((k - 1).choose k : ℕ) : ℝ) * g k)
          + (∑ m ∈ Finset.range k, (((k - 1).choose m : ℕ) : ℝ) * g (m + 1)) := by rw [e2]
    _ = (∑ m ∈ Finset.range (k + 1), (((k - 1).choose m : ℕ) : ℝ) * g m)
          + (∑ m ∈ Finset.range k, (((k - 1).choose m : ℕ) : ℝ) * g (m + 1)) := by rw [← h3]
    _ = ((∑ m ∈ Finset.range k, (((k - 1).choose (m + 1) : ℕ) : ℝ) * g (m + 1)) + 1)
          + (∑ m ∈ Finset.range k, (((k - 1).choose m : ℕ) : ℝ) * g (m + 1)) := by rw [← e1, ← h2]
    _ = ((∑ m ∈ Finset.range k, (((k - 1).choose (m + 1) : ℕ) : ℝ) * g (m + 1))
          + (∑ m ∈ Finset.range k, (((k - 1).choose m : ℕ) : ℝ) * g (m + 1))) + 1 := by ring
    _ = (∑ m ∈ Finset.range k, (((k).choose (m + 1) : ℕ) : ℝ) * g (m + 1)) + 1 := by rw [← hsplt]
    _ = (∑ m ∈ Finset.range k, (((k).choose (m + 1) : ℕ) : ℝ) * g (m + 1)) + (((k).choose 0 : ℕ) : ℝ) * g 0 := by rw [e0]
    _ = ∑ m ∈ Finset.range (k + 1), (((k).choose m : ℕ) : ℝ) * g m := by rw [← h1]

end Commons.Algebra.BigOperators