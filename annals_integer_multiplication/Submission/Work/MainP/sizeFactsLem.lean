import Mathlib
import Submission.HvdH.Interfaces

set_option linter.unusedVariables false

namespace Work.MainP

/-- Paper Prop 5.2, sizes of the integer values produced by the parameter computation `D0`.

`α ^ 2 < p`, `2·D·α² ≤ p` and `100 ≤ p` (from `ResParams`/`PowTwoParams`) give `α ≤ p`, so
`2·D·α² + 2 ≤ p + 2`; every `isz` below is at most `p + 16`:
`isz (2·D) = 14`, `isz α = α.size + 2 ≤ p + 2`,
`isz (2·D·α) = (3458·α).size + 2 ≤ (12 + α.size) + 2 ≤ p + 14`
(using `n.size ≤ k ↔ n < 2^k`, `α ≤ p < 2^p`, `3458 < 2^12`), and similarly
`isz (α·(2·D·α)) = (2·D·α²).size + 2 ≤ p + 2` (from `2·D·α² ≤ p`).
`(α·(2·D·α)).toNat = 2·D·α² ≤ p ≤ p + 16` and the integer is nonnegative. -/
theorem sizeFactsLem {p α : ℕ} (hα2p : α ^ 2 < p) (h2Da : 2 * HvdH.D * α ^ 2 ≤ p) (hp : 100 ≤ p) :
    HvdH.isz (2 * HvdH.D : ℤ) ≤ p + 16 ∧ HvdH.isz (α : ℤ) ≤ p + 16 ∧
    HvdH.isz ((2 * HvdH.D) * (α : ℤ)) ≤ p + 16 ∧
    HvdH.isz ((α : ℤ) * ((2 * HvdH.D) * (α : ℤ))) ≤ p + 16 ∧
    ((α : ℤ) * ((2 * HvdH.D) * (α : ℤ))).toNat ≤ p + 16 ∧
    ((α : ℤ) * ((2 * HvdH.D) * (α : ℤ))).toNat = 2 * HvdH.D * α ^ 2 ∧
    (0 : ℤ) ≤ (α : ℤ) * ((2 * HvdH.D) * (α : ℤ)) := by
  -- All bounds are governed by `n.size ≤ k ↔ n < 2 ^ k` and `p < 2 ^ p`.
  have hple : p < 2 ^ p := Nat.lt_two_pow_self
  -- `α ≤ α ^ 2 < p ≤ 2 ^ p`, so `α.size ≤ p`.
  have hαsq : α ≤ α ^ 2 := by rw [pow_two]; exact Nat.le_mul_self α
  have hαp : α < p := lt_of_le_of_lt hαsq hα2p
  have hsizeα : α.size ≤ p := Nat.size_le.mpr (lt_trans hαp hple)
  -- The three products, as casts of natural numbers.
  have hmul1 : (2 * HvdH.D : ℤ) = ((2 * HvdH.D : ℕ) : ℤ) := by push_cast; ring
  have hmul2 : ((2 * HvdH.D : ℤ) * (α : ℤ)) = ((2 * HvdH.D * α : ℕ) : ℤ) := by push_cast; ring
  have hmul3 : ((α : ℤ) * ((2 * HvdH.D : ℤ) * (α : ℤ))) = ((2 * HvdH.D * α ^ 2 : ℕ) : ℤ) := by
    push_cast; ring
  -- `2·D·α ≤ 2·D·α² ≤ p`.
  have hle3 : 2 * HvdH.D * α ≤ 2 * HvdH.D * α ^ 2 := Nat.mul_le_mul_left (2 * HvdH.D) hαsq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [HvdH.isz, hmul1, Int.natAbs_natCast]
    have : (2 * HvdH.D : ℕ).size ≤ 12 := by rw [HvdH.D, Nat.size_le]; norm_num
    omega
  · rw [HvdH.isz, Int.natAbs_natCast]; omega
  · rw [HvdH.isz, hmul2, Int.natAbs_natCast]
    have : (2 * HvdH.D * α).size ≤ p :=
      Nat.size_le.mpr (lt_of_le_of_lt (le_trans hle3 h2Da) hple)
    omega
  · rw [HvdH.isz, hmul3, Int.natAbs_natCast]
    have : (2 * HvdH.D * α ^ 2).size ≤ p := Nat.size_le.mpr (lt_of_le_of_lt h2Da hple)
    omega
  · rw [hmul3, Int.toNat_natCast]; omega
  · rw [hmul3, Int.toNat_natCast]
  · rw [hmul3]; exact Int.natCast_nonneg _

end Work.MainP
