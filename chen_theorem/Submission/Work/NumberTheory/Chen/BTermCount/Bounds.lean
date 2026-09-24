import Submission.Work.NumberTheory.Chen.BTermCount.Basic

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# Elementary bounds for the Chen parameters

`chenSiftLimit x = ⌊cut x^{1/8} 1⌋ + 1 = ⌊x^{599/8000}⌋ + 1` and
`chenWindowTop x = ⌊x^{1/3}⌋ + 2`; here we record the crude bounds that the analytic estimate of
the `B`-term needs:

* `x^{1/14} ≤ chenSiftLimit x`;
* `x^{1/3} ≤ chenWindowTop x`;
* `chenWindowTop x ≤ 2 x^{1/3}`  (for `x ≥ 8`).

The proofs only unfold `Submission.chenSiftLimit`/`Submission.chenWindowTop` and use the floor
bounds, so they are insensitive to the value of the additive constant in the definitions.
-/

/-- `chenSiftLimit x ≥ x^{1/14}`. -/
theorem chenSiftLimit_ge_rpow (x : ℕ) :
    (x : ℝ) ^ ((1:ℝ)/14) ≤ (Submission.chenSiftLimit x : ℝ) := by
  rcases eq_or_lt_of_le (Nat.zero_le x) with hx0 | hx0
  · subst hx0
    have h0 : ((0:ℕ):ℝ) ^ ((1:ℝ)/14) = 0 := by
      rw [show ((0:ℕ):ℝ) = (0:ℝ) by norm_num]
      exact Real.zero_rpow (by norm_num)
    rw [h0]
    positivity
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx0' : (0:ℝ) < (x:ℝ) := by linarith
  have hcut : cut (Real.rpow (x:ℝ) ((1:ℝ)/8)) 1 = (x:ℝ) ^ (sieveAlpha/8) := by
    unfold cut
    rw [pow_one, show Real.rpow (x:ℝ) ((1:ℝ)/8) = (x:ℝ) ^ ((1:ℝ)/8) from rfl,
      ← Real.rpow_mul (le_of_lt hx0')]
    congr 1
    ring
  have hfloor : cut (Real.rpow (x:ℝ) ((1:ℝ)/8)) 1 ≤ (Submission.chenSiftLimit x : ℝ) := by
    rw [Submission.chenSiftLimit]
    push_cast
    have h := Nat.lt_floor_add_one (cut (Real.rpow (x:ℝ) ((1:ℝ)/8)) 1)
    linarith
  have hle : (x:ℝ) ^ ((1:ℝ)/14) ≤ cut (Real.rpow (x:ℝ) ((1:ℝ)/8)) 1 := by
    rw [hcut]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    rw [sieveAlpha]; norm_num
  linarith

/-- `chenWindowTop x ≥ x^{1/3}`. -/
theorem chenWindowTop_ge_rpow (x : ℕ) :
    (x : ℝ) ^ ((1:ℝ)/3) ≤ (Submission.chenWindowTop x : ℝ) := by
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
  rw [Submission.chenWindowTop]
  push_cast
  rw [show Real.rpow (x:ℝ) ((1:ℝ)/3) = (x:ℝ) ^ ((1:ℝ)/3) from rfl]
  have hfloor : (x:ℝ) ^ ((1:ℝ)/3) < ((⌊(x:ℝ) ^ ((1:ℝ)/3)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  linarith

/-- `chenWindowTop x ≤ 2 x^{1/3}` for `x ≥ 8`. -/
theorem chenWindowTop_le_two_rpow (x : ℕ) (hx : 8 ≤ x) :
    (Submission.chenWindowTop x : ℝ) ≤ 2 * (x:ℝ) ^ ((1:ℝ)/3) := by
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  have h2 : (2:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/3) := by
    have hx8 : (8:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
    calc (2:ℝ) = (8:ℝ) ^ ((1:ℝ)/3) := by
          rw [show (8:ℝ) = (2:ℝ)^3 by norm_num, ← Real.rpow_natCast (2:ℝ) 3,
            ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
          norm_num
      _ ≤ (x:ℝ) ^ ((1:ℝ)/3) := Real.rpow_le_rpow (by norm_num) hx8 (by norm_num)
  rw [Submission.chenWindowTop]
  push_cast
  rw [show Real.rpow (x:ℝ) ((1:ℝ)/3) = (x:ℝ) ^ ((1:ℝ)/3) from rfl]
  have hfloor : ((⌊(x:ℝ) ^ ((1:ℝ)/3)⌋₊ : ℕ) : ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/3) :=
    Nat.floor_le (Real.rpow_nonneg (le_of_lt hx0) _)
  linarith

end Work.NumberTheory.Chen.BTermCount
