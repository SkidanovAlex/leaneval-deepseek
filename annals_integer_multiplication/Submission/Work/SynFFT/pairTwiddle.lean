import Mathlib
import Submission.Work.SynFFT.kit2

/-!
# `Work.SynFFT.pairTwiddle`

The twiddle parameters of `HasYMulShift` (`kit2.lean`), spelled out for the concrete twiddle
exponent `t = j · 2^sh` of the butterfly word: the shift `s` passed to `yMulS` is `≤ r`, the
sign `sg = 1 - 2·(max sgn 0 · [0 < t])` agrees with the sign `yMulList` computes from its own
residue, and the resulting list operation is `yMulList r (sgn · t)` — which is exactly
`YMulTwiddleProp` at `t = j · 2^sh`.  All four conjuncts are pure integer/`ℕ` arithmetic
(the last one being the instantiation of `htw`).
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

theorem pairTwiddle (htw : Work.SynFFT.YMulTwiddleProp) (r j sh : ℕ) (sgn : ℤ) (w : List (ℤ × ℤ)) (hr : 0 < r) (hsgn : sgn = 1 ∨ sgn = -1) (ht : j * 2 ^ sh < r) (hw : w.length = r) : (((if sgn = 1 then (if j * 2 ^ sh = 0 then 0 else r - j * 2 ^ sh) else j * 2 ^ sh) : ℕ) ≤ r) ∧ (((if 0 < ((j * 2 ^ sh : ℕ) : ℤ) then (1 : ℤ) else 0) * (((j * 2 ^ sh : ℕ) : ℤ) + max sgn 0 * ((r : ℤ) - 2 * ((j * 2 ^ sh : ℕ) : ℤ)))) = (((if sgn = 1 then (if j * 2 ^ sh = 0 then 0 else r - j * 2 ^ sh) else j * 2 ^ sh) : ℕ) : ℤ)) ∧ ((1 - 2 * (max sgn 0 * (if 0 < ((j * 2 ^ sh : ℕ) : ℤ) then (1 : ℤ) else 0))) = (if sgn = 1 ∧ j * 2 ^ sh ≠ 0 then (-1 : ℤ) else 1)) ∧ (Work.SynFFT.yMulS r (if sgn = 1 then (if j * 2 ^ sh = 0 then 0 else r - j * 2 ^ sh) else j * 2 ^ sh) (1 - 2 * (max sgn 0 * (if 0 < ((j * 2 ^ sh : ℕ) : ℤ) then (1 : ℤ) else 0))) w = Work.SynFFT.yMulList r (sgn * ((j * 2 ^ sh : ℕ) : ℤ)) w) := by
  have hle : j * 2 ^ sh ≤ r := le_of_lt ht
  -- the sign `1 - 2·(max sgn 0 · [0 < t])` is exactly the sign `YMulTwiddleProp` uses
  have hC : (1 - 2 * (max sgn 0 * (if 0 < ((j * 2 ^ sh : ℕ) : ℤ) then (1 : ℤ) else 0)))
      = (if sgn = 1 ∧ j * 2 ^ sh ≠ 0 then (-1 : ℤ) else 1) := by
    rcases hsgn with h | h <;> subst h
    · rw [show max (1 : ℤ) 0 = 1 by norm_num]
      by_cases h0 : j * 2 ^ sh = 0
      · rw [h0]; norm_num
      · have h0' : 0 < ((j * 2 ^ sh : ℕ) : ℤ) := by
          exact_mod_cast Nat.pos_of_ne_zero h0
        rw [ite_eq_left h0', mul_one, ite_eq_left ⟨rfl, h0⟩]
        norm_num
    · rw [show max (-1 : ℤ) 0 = 0 by norm_num]
      norm_num
  refine ⟨?_, ?_, hC, ?_⟩
  · -- the shift `s` is at most `r`
    rcases hsgn with h | h <;> subst h
    · rw [ite_eq_left rfl]
      by_cases h0 : j * 2 ^ sh = 0
      · rw [ite_eq_left h0]
        exact Nat.zero_le r
      · rw [ite_eq_right h0]
        exact Nat.sub_le _ _
    · rw [ite_eq_right (by norm_num : ¬ ((-1 : ℤ) = 1))]
      exact le_of_lt ht
  · -- the sign-magnitude product of `yMulList`
    rcases hsgn with h | h <;> subst h
    · rw [show max (1 : ℤ) 0 = 1 by norm_num]
      by_cases h0 : j * 2 ^ sh = 0
      · rw [h0]; norm_num
      · have h0' : 0 < ((j * 2 ^ sh : ℕ) : ℤ) := by
          exact_mod_cast Nat.pos_of_ne_zero h0
        rw [ite_eq_left h0', one_mul, ite_eq_left rfl, ite_eq_right h0, Nat.cast_sub hle]
        ring
    · rw [show max (-1 : ℤ) 0 = 0 by norm_num,
        ite_eq_right (by norm_num : ¬ ((-1 : ℤ) = 1))]
      by_cases h0 : j * 2 ^ sh = 0
      · rw [h0]; norm_num
      · rw [ite_eq_left (by
          exact_mod_cast Nat.pos_of_ne_zero h0 : (0 : ℤ) < ((j * 2 ^ sh : ℕ) : ℤ))]
        simp
  · -- the list operation: instantiate `YMulTwiddleProp` at `t = j · 2^sh`
    rw [hC]
    exact htw r hr sgn hsgn (j * 2 ^ sh) ht w

end Work.SynFFT
