import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summability of a product of geometric series over a multi-index

We prove that the multi-index geometric series `k ↦ ∏ i, s i ^ k i` (over
`k : ι → ℕ` for a finite type `ι`) is summable whenever `0 ≤ s i < 1` for all
`i`, and deduce that the product of such a series with a one-variable geometric
series is summable.
-/

namespace Commons.Analysis.TSum

open scoped BigOperators

/-- The multi-index geometric series `k ↦ ∏ i, s i ^ k i` is summable whenever
`0 ≤ s i < 1` for every `i`. -/
theorem summable_pi_geometric {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i < 1) :
    Summable (fun k : ι → ℕ => ∏ i, s i ^ k i) := by
  classical
  revert s
  refine Fintype.induction_empty_option (P := fun ι _ => ∀ s : ι → ℝ, (∀ i, 0 ≤ s i) →
      (∀ i, s i < 1) → Summable (fun k : ι → ℕ => ∏ i, s i ^ k i)) ?_ ?_ ?_ ι
  · intro α β hβ e hα s hs hs1
    letI : Fintype α := @Fintype.ofEquiv α β hβ e.symm
    have h' : Summable (fun k : α → ℕ => ∏ i, s (e i) ^ k i) :=
      hα (fun i => s (e i)) (fun i => hs (e i)) (fun i => hs1 (e i))
    refine (Equiv.summable_iff (Equiv.arrowCongr e (Equiv.refl ℕ))
      (f := fun k : β → ℕ => ∏ i, s i ^ k i)).1 ?_
    exact h'.congr (fun k => by
      rw [Fintype.prod_equiv e (fun i : α => s (e i) ^ k i)
        (fun i : β => s i ^ k (e.symm i)) (fun x => by simp)]
      exact Finset.prod_congr rfl (fun i _ => by simp [Equiv.arrowCongr_apply]))
  · intro s _hs _hs1
    exact (hasSum_unique (fun k : PEmpty → ℕ => ∏ i, s i ^ k i)).summable
  · intro α _ ih s hs hs1
    have hg : Summable (fun m : ℕ => s none ^ m) :=
      summable_geometric_of_lt_one (hs none) (hs1 none)
    have hh : Summable (fun k : α → ℕ => ∏ a, s (some a) ^ k a) :=
      ih (fun a => s (some a)) (fun a => hs (some a)) (fun a => hs1 (some a))
    have hgh : Summable (fun y : ℕ × (α → ℕ) =>
        s none ^ y.1 * ∏ a, s (some a) ^ y.2 a) :=
      hg.mul_of_nonneg hh (fun m => pow_nonneg (hs none) m)
        (fun k => Finset.prod_nonneg (fun a _ => pow_nonneg (hs (some a)) (k a)))
    refine (Equiv.summable_iff (Equiv.piOptionEquivProd (β := fun _ => ℕ)).symm
      (f := fun k : Option α → ℕ => ∏ i, s i ^ k i)).1 ?_
    exact hgh.congr (fun y => by
      show s none ^ y.1 * ∏ a, s (some a) ^ y.2 a =
        ∏ i : Option α, s i ^ (Equiv.piOptionEquivProd.symm y) i
      rw [Fintype.prod_option]
      simp [Equiv.piOptionEquivProd])

theorem summable_mul_multiIndex_geometric {n : ℕ} {s : Fin n → ℝ} {t C : ℝ}
    (hs : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i < 1) (ht : 0 ≤ t) (ht1 : t < 1) (hC : 0 ≤ C) :
    Summable (fun p : (Fin n → ℕ) × ℕ => C * (∏ i, s i ^ (p.1 i)) * t ^ p.2) := by
  have _ : 0 ≤ C := hC
  have h1 : Summable (fun k : Fin n → ℕ => ∏ i, s i ^ k i) := summable_pi_geometric s hs hs1
  have h2 : Summable (fun m : ℕ => t ^ m) := summable_geometric_of_lt_one ht ht1
  have h12 : Summable (fun p : (Fin n → ℕ) × ℕ => (∏ i, s i ^ (p.1 i)) * t ^ p.2) :=
    h1.mul_of_nonneg h2 (fun k => Finset.prod_nonneg (fun i _ => pow_nonneg (hs i) (k i)))
      (fun m => pow_nonneg ht m)
  refine (h12.mul_left C).congr (fun p => ?_)
  rw [mul_assoc]

end Commons.Analysis.TSum