import Mathlib
import Submission.Commons.NumberTheory.ZMod.sum_minrep_weight_le

namespace Commons.Data.ZMod

/-- The sum over `ZMod p` of `f` applied to the distance of `x` to `0`,
`min x.val (p - x.val)`, equals `f 0` plus twice the sum of `f` over the
positive half `1, …, p / 2`.  Here `p` is an odd prime (`p ≥ 3`), so the
distance function takes the value `0` once (at `x = 0`) and each value
`1, …, (p-1)/2 = p/2` exactly twice. -/
theorem sum_dist_to_zero (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (f : ℕ → ℝ) :
    ∑ x : ZMod p, f (min x.val (p - x.val)) = f 0 + 2 * ∑ n ∈ Finset.Icc 1 (p / 2), f n := by
  set m := p / 2 with hmdef
  have hm : p = 2 * m + 1 := by
    have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    rw [Nat.odd_iff] at hodd
    omega
  -- Step 1: reindex the `ZMod p` sum as a sum over `Finset.range p`.
  have h1 : (∑ x : ZMod p, f (min x.val (p - x.val)))
      = ∑ j ∈ Finset.range p, f (min j (p - j)) :=
    Commons.NumberTheory.ZMod.sum_zmod_val_eq_sum_range p (fun j => f (min j (p - j)))
  rw [h1]
  -- The lower half: for `1 ≤ k + 1 ≤ m`, `min (k+1) (p - (k+1)) = k + 1`.
  have hG1 : (∑ k ∈ Finset.range m, f (min (k + 1) (p - (k + 1))))
      = ∑ k ∈ Finset.range m, f (k + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [min_eq_left (by omega)]
  -- The upper half: for `x < m`, `min ((m+1)+x) (p - ((m+1)+x)) = m - x`.
  have hG2 : (∑ x ∈ Finset.range m, f (min ((m + 1) + x) (p - ((m + 1) + x))))
      = ∑ x ∈ Finset.range m, f (m - x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    have hsub : p - ((m + 1) + x) = m - x := by omega
    have hmin : min ((m + 1) + x) (p - ((m + 1) + x)) = p - ((m + 1) + x) :=
      min_eq_right (by omega)
    rw [hmin, hsub]
  -- Reflection: `∑_{x < m} f (m - x) = ∑_{x < m} f (x + 1)`.
  have hG3 : (∑ x ∈ Finset.range m, f (m - x)) = ∑ x ∈ Finset.range m, f (x + 1) := by
    have hcong : (∑ x ∈ Finset.range m, f (m - x))
        = ∑ x ∈ Finset.range m, f ((m - 1 - x) + 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      congr 1
      omega
    rw [hcong]
    exact Finset.sum_range_reflect (fun k => f (k + 1)) m
  have hG0 : f (min 0 (p - 0)) = f 0 := by rw [Nat.sub_zero, Nat.zero_min]
  -- The half-interval sum as a sum over `range m`.
  have hIcc : (∑ n ∈ Finset.Icc 1 m, f n) = ∑ k ∈ Finset.range m, f (k + 1) := by
    have hIco : Finset.Ico 1 (m + 1) = Finset.Icc 1 m := by
      simpa [Nat.succ_eq_add_one] using Finset.Ico_succ_right_eq_Icc (a := 1) (b := m)
    rw [← hIco, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    omega
  have hpm : (m + 1) + m = p := by omega
  have hrange : Finset.range p = Finset.range ((m + 1) + m) := by rw [hpm]
  calc (∑ j ∈ Finset.range p, f (min j (p - j)))
      = (∑ k ∈ Finset.range m, f (k + 1) + f 0) + ∑ k ∈ Finset.range m, f (k + 1) := by
          rw [hrange, Finset.sum_range_add, Finset.sum_range_succ', hG1, hG2, hG3, hG0]
    _ = f 0 + 2 * ∑ k ∈ Finset.range m, f (k + 1) := by ring
    _ = f 0 + 2 * ∑ n ∈ Finset.Icc 1 m, f n := by rw [hIcc]

end Commons.Data.ZMod
