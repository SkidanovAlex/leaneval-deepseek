import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- For `n ≥ 2`, we have `n + 1 < 2 ^ n`. -/
lemma two_pow_gt_succ (n : ℕ) (hn : 2 ≤ n) : n + 1 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
      nlinarith [ih, hpos]

theorem geom_sum_gt_prime {A p : ℕ} (hA : 2 ≤ A) (hp : p.Prime) (hp2 : p ≠ 2) :
    p < ∑ i ∈ Finset.range p, A ^ i := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hp0 : 0 < p := by omega
  -- the last term `A ^ (p - 1)` is one of the summands
  have hmem : p - 1 ∈ Finset.range p := Finset.mem_range.mpr (Nat.sub_lt hp0 (by norm_num))
  have hterm : A ^ (p - 1) ≤ ∑ i ∈ Finset.range p, A ^ i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) hmem
  -- and it dominates `p`
  have h2p : p < 2 ^ (p - 1) := by
    have h := two_pow_gt_succ (p - 1) (by omega)
    omega
  have hA' : 2 ^ (p - 1) ≤ A ^ (p - 1) := Nat.pow_le_pow_left hA _
  omega

end Work.PSU3.StageA
