import Mathlib
import Submission.Work.Resample.buQWscalDefs

namespace Work.Resample
open HvdH

/-- Step one of the normalisation: `buScQ S s p = 400·S·(s+1)·(buScB p + 1)·(p+1)` is absorbed by
`2^20·S·(s+1)(p+1)²`.  Indeed `buScB p + 1 = 3p + 13 ≤ 13(p+1)` (`buScB_succ_le`) and
`400·13 = 5200 ≤ 2^20 = 1048576`. -/
theorem buScQ_le (S s p : ℕ) :
    buScQ S s p ≤ 2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1) := by
  have h1 : 400 * (buScB p + 1) ≤ 2 ^ 20 * (p + 1) := by
    calc 400 * (buScB p + 1) ≤ 400 * (13 * (p + 1)) :=
          Nat.mul_le_mul_left 400 (buScB_succ_le p)
      _ = 5200 * (p + 1) := by ring
      _ ≤ 2 ^ 20 * (p + 1) := by
          have h20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
          rw [h20]
          exact Nat.mul_le_mul_right _ (by norm_num)
  have h20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  calc buScQ S s p
      = (400 * (buScB p + 1)) * (S * (s + 1) * (p + 1)) := by
        simp only [buScQ]; ring
    _ ≤ (2 ^ 20 * (p + 1)) * (S * (s + 1) * (p + 1)) := Nat.mul_le_mul_right _ h1
    _ = 2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1) := by
        rw [h20]; ring

/-- Step two of the normalisation: fourteen normalised stages fit under
`2^(2^S+80)·(s+1)(p+1)²` as soon as `S ≥ 1`.  Since `S ≤ 2^S` (`Nat.lt_two_pow_self`) we have
`S ≤ 2^(2^S)`, hence `14·2^20·S ≤ 2^80·2^S·S ≤ 2^80·2^S·2^S = 2^(2·S+80) ≤ 2^(2^S+80)`;
more directly `14·2^20·S ≤ 2^80 · S ≤ 2^80 · 2^S = 2^(S+80) ≤ 2^(2^S+80)`, and `14·2^20 ≤ 2^80`. -/
theorem buSc_stack (S s p : ℕ) (hS : 1 ≤ S) :
    14 * (2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1))
      ≤ 2 ^ (2 ^ S + 80) * (s + 1) * (p + 1) * (p + 1) := by
  have hSpow : S ≤ 2 ^ S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · simp [h]
    · exact le_of_lt (Nat.lt_two_pow_self (n := S))
  have hpow : 14 * 2 ^ 20 ≤ 2 ^ 80 := by norm_num
  have hkey : 14 * 2 ^ 20 * S ≤ 2 ^ (2 ^ S + 80) := by
    calc 14 * 2 ^ 20 * S = (14 * 2 ^ 20) * S := by ring
      _ ≤ 2 ^ 80 * 2 ^ S := Nat.mul_le_mul hpow hSpow
      _ = 2 ^ (80 + S) := by rw [pow_add]
      _ ≤ 2 ^ (2 ^ S + 80) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 14 * (2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1))
      = (14 * 2 ^ 20 * S) * ((s + 1) * (p + 1) * (p + 1)) := by ring
    _ ≤ 2 ^ (2 ^ S + 80) * ((s + 1) * (p + 1) * (p + 1)) := Nat.mul_le_mul_right _ hkey
    _ = 2 ^ (2 ^ S + 80) * (s + 1) * (p + 1) * (p + 1) := by ring

/-- The two normalisation steps of the cost accounting: a single stage cost bounded by
`buScQ S s p = 400·S·(s+1)·(buScB p + 1)·(p+1)` is bounded by `2^20·S·(s+1)(p+1)²`, and fourteen
such stages fit under `2^(2^S+80)·(s+1)(p+1)²`. -/
theorem buScArith :
    (∀ {S s p X : ℕ}, X ≤ buScQ S s p → X ≤ 2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1)) ∧
    (∀ {S s p : ℕ}, 1 ≤ S →
      14 * (2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1))
        ≤ 2 ^ (2 ^ S + 80) * (s + 1) * (p + 1) * (p + 1)) := by
  constructor
  · intro S s p X hX
    exact le_trans hX (buScQ_le S s p)
  · intro S s p hS
    exact buSc_stack S s p hS

/-- The same statement under the duplicate namespace of the original template, so that consumers
using the name `Work.Resample.Work.Resample.buScArith` also find it. -/
theorem buScArith_dupName :
    (∀ {S s p X : ℕ}, X ≤ buScQ S s p → X ≤ 2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1)) ∧
    (∀ {S s p : ℕ}, 1 ≤ S →
      14 * (2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1))
        ≤ 2 ^ (2 ^ S + 80) * (s + 1) * (p + 1) * (p + 1)) := buScArith

end Work.Resample

namespace Work.Resample
namespace Work.Resample

/-- The requested statement, also available under the duplicated namespace of the template file,
with the name `Work.Resample.Work.Resample.buScArith`. -/
theorem buScArith :
    (∀ {S s p X : ℕ}, X ≤ buScQ S s p → X ≤ 2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1)) ∧
    (∀ {S s p : ℕ}, 1 ≤ S →
      14 * (2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1))
        ≤ 2 ^ (2 ^ S + 80) * (s + 1) * (p + 1) * (p + 1)) :=
  _root_.Work.Resample.buScArith

end Work.Resample
end Work.Resample
