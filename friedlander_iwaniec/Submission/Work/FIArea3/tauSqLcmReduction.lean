import Mathlib
import Submission.Work.FIArea3.JointCount.joint_sum_le_double

namespace Work.FIArea3

/-- **Reduction of `∑ τ(g z)²` to a double lcm-sum.**

For `g z ≤ K⁴` the elementary truncated divisor bound `τ(m) ≤ 256 ∑_{d ∣ m, d ≤ K} τ(d)⁸`
(`tau_le_sum_Icc_aux`) applied to both factors of `τ(g z)²` turns the squared divisor sum into the
double divisor sum over the pair counts; the condition `d ∣ g z ∧ e ∣ g z` of the two factors is
equivalent to `lcm d e ∣ g z`. -/
lemma tauSqLcmReduction {α : Type*} [DecidableEq α] (B : Finset α) (g : α → ℕ) (K : ℕ)
    (h : ∀ z ∈ B, (g z : ℝ) ≤ (K : ℝ) ^ (4 : ℕ)) :
    (∑ z ∈ B, (((g z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
      ≤ 65536 * ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          ((((d.divisors.card : ℕ) : ℝ) ^ (8 : ℕ)) * (((e.divisors.card : ℕ) : ℝ) ^ (8 : ℕ))
            * (((B.filter (fun z => Nat.lcm d e ∣ g z)).card : ℕ) : ℝ)) := by
  classical
  -- pointwise truncated divisor bound, from FI Lemma 2.2 with `k = 4`
  have hτg : ∀ z ∈ B, ((g z).divisors.card : ℝ)
      ≤ 256 * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) :=
    fun z hz => Work.FIArea3.JointCount.tau_le_sum_Icc_aux (g z) K (h z hz)
  -- the purely combinatorial rearrangement of the two truncated bounds
  have key := Work.FIArea3.JointCount.joint_double_sum_bound_aux B g g K K hτg hτg
  have hL : (∑ z ∈ B, (((g z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
      = ∑ z ∈ B, (((g z).divisors.card : ℕ) : ℝ) * (((g z).divisors.card : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl; intro z _; rw [pow_two]
  -- replace the conjunction of divisibilities by the lcm divisibility
  have hR : (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
        ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
          * (((B.filter (fun z => d ∣ g z ∧ e ∣ g z)).card : ℕ) : ℝ))
      = ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
        ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
          * (((B.filter (fun z => Nat.lcm d e ∣ g z)).card : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro e _
    have hfil : B.filter (fun z => d ∣ g z ∧ e ∣ g z) = B.filter (fun z => Nat.lcm d e ∣ g z) := by
      apply Finset.filter_congr
      intro z _
      exact Nat.lcm_dvd_iff.symm
    rw [hfil]
  calc (∑ z ∈ B, (((g z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
      = ∑ z ∈ B, (((g z).divisors.card : ℕ) : ℝ) * (((g z).divisors.card : ℕ) : ℝ) := hL
    _ ≤ 65536 * ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
            * (((B.filter (fun z => d ∣ g z ∧ e ∣ g z)).card : ℕ) : ℝ) := key
    _ = 65536 * ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
            * (((B.filter (fun z => Nat.lcm d e ∣ g z)).card : ℕ) : ℝ) := by rw [hR]

end Work.FIArea3
