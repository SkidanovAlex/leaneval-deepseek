import Mathlib

namespace Work.TMC16Core.Core

/-- Splitting lemma. Given `Q ≥ 1` and `s` with `40*Q + 178 ≤ s*Q`, there exist `a' b'` with `a' + b' = s`, `8*a'*Q + 6 ≤ 5*(s*Q)` and `10*b'*Q + 37 ≤ 4*(s*Q)`. Construction: with `T = s*Q`, take `a' = (6*T + 37 + 10*Q - 1) / (10*Q)` (i.e. `⌈(6*T+37)/(10*Q)⌉`) and `b' = s - a'`. -/
theorem scale_split_nr2 (Q s : ℕ) (hQ : 1 ≤ Q) (hT : 40 * Q + 178 ≤ s * Q) :
    ∃ a' b' : ℕ, a' + b' = s ∧ 8 * a' * Q + 6 ≤ 5 * (s * Q) ∧
      10 * b' * Q + 37 ≤ 4 * (s * Q) := by
  have hdpos : 0 < 10 * Q := by omega
  refine ⟨(6 * (s*Q) + 37) ⌈/⌉ (10*Q), s - (6 * (s*Q) + 37) ⌈/⌉ (10*Q), ?_, ?_, ?_⟩
  · -- sum condition: `a' ≤ s` via the Galois connection for `⌈/⌉`
    have h3 : (6 * (s*Q) + 37) ⌈/⌉ (10*Q) ≤ s := by
      rw [ceilDiv_le_iff_le_smul hdpos, smul_eq_mul]
      nlinarith [hT]
    exact Nat.add_sub_of_le h3
  · -- first bound, from the floor bound `⌈n/d⌉ * d ≤ n + d - 1`
    have h2 : 10 * (((6*(s*Q)+37) ⌈/⌉ (10*Q)) * Q) ≤ 6*(s*Q) + 10*Q + 36 := by
      rw [Nat.ceilDiv_eq_add_pred_div]
      have key : (6*(s*Q)+37 + 10*Q - 1) = 6*(s*Q) + 10*Q + 36 := by omega
      rw [key]
      have hh := Nat.div_mul_le_self (6*(s*Q)+10*Q+36) (10*Q)
      nlinarith [hh]
    rw [Nat.mul_assoc]
    nlinarith [h2, hT]
  · -- second bound, from `n ≤ d * ⌈n/d⌉` (the defining property of the ceiling)
    have h1 : 6*(s*Q)+37 ≤ 10 * (((6*(s*Q)+37) ⌈/⌉ (10*Q)) * Q) := by
      have hh := le_smul_ceilDiv (a := 10*Q) (b := 6*(s*Q)+37) hdpos
      rw [smul_eq_mul] at hh
      nlinarith [hh]
    rw [Nat.mul_assoc, Nat.sub_mul, Nat.mul_sub_left_distrib]
    omega

end Work.TMC16Core.Core
