import Mathlib
import Submission.Work.IntLib.SqrtGcd.SubDefs
import Submission.Work.IntLib.SqrtGcd.subDigitsSpec

/-!
# Arithmetic corollaries of the ripple subtraction `SG.subDigits`

The (already proved) identity `subDigitsSpec` reads

  `⟨padTo n as⟩ + 2ⁿ · borrow = ⟨padTo n bs⟩ + ⟨digits⟩ + c`,

where `⟨·⟩ = ofBits`.  Here we extract the four arithmetic facts about `subDigits` that the
top-level `sqrt`/`gcd` specifications consume:

* the outgoing borrow is `true` exactly when `⟨padTo n as⟩ < ⟨padTo n bs⟩` (the subtraction
  goes negative);
* if the borrow is `false`, the digits are exactly the difference `⟨padTo n as⟩ - ⟨padTo n bs⟩`;
* padding a list beyond its length does not change its value;
* the digit list always has length `n`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open Work.IntLib (ofBits)

/-- `ofBits` of a run of `false`s is `0`. -/
theorem ofBits_replicate_false_subDigitsArith (k : ℕ) : ofBits (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, ofBits_cons, ih]; simp

/-- Padding a bit list to at least its own length does not change its value. -/
theorem ofBits_padTo_of_le (n : ℕ) (as : List Bool) (h : as.length ≤ n) :
    ofBits (SG.padTo n as) = ofBits as := by
  unfold SG.padTo
  rw [List.take_of_length_le h, ofBits_append, ofBits_replicate_false_subDigitsArith]
  simp

/-- The digit list produced by `n` ripple subtraction steps has length `n`. -/
theorem subDigits_len (n : ℕ) (as bs : List Bool) (c : Bool) :
    (SG.subDigits n as bs c).2.length = n := by
  induction n generalizing as bs c with
  | zero => rfl
  | succ n ih =>
      simp only [SG.subDigits]
      simp [ih]

/-- If the outgoing borrow of `subDigits n as bs false` is `false`, then the subtrahend is at
most the minuend, i.e. the subtraction does not go negative. -/
theorem ofBits_padTo_le_of_subDigits_false (n : ℕ) (as bs : List Bool)
    (hf : (SG.subDigits n as bs false).1 = false) :
    ofBits (SG.padTo n bs) ≤ ofBits (SG.padTo n as) := by
  have h := subDigitsSpec n as bs false
  rw [hf] at h
  simp only [Bool.toNat_false, mul_zero, add_zero] at h
  omega

theorem subDigitsArith :
    (∀ (n : ℕ) (as bs : List Bool),
        (Work.IntLib.SG.subDigits n as bs false).1 = true ↔
          Work.IntLib.ofBits (Work.IntLib.SG.padTo n as) <
            Work.IntLib.ofBits (Work.IntLib.SG.padTo n bs)) ∧
    (∀ (n : ℕ) (as bs : List Bool), (Work.IntLib.SG.subDigits n as bs false).1 = false →
        Work.IntLib.ofBits (Work.IntLib.SG.subDigits n as bs false).2 =
          Work.IntLib.ofBits (Work.IntLib.SG.padTo n as) -
            Work.IntLib.ofBits (Work.IntLib.SG.padTo n bs)) ∧
    (∀ (n : ℕ) (as : List Bool), as.length ≤ n →
        Work.IntLib.ofBits (Work.IntLib.SG.padTo n as) = Work.IntLib.ofBits as) ∧
    (∀ (n : ℕ) (as bs : List Bool) (c : Bool),
        (Work.IntLib.SG.subDigits n as bs c).2.length = n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n as bs
    constructor
    · intro hbor
      have h := subDigitsSpec n as bs false
      rw [hbor] at h
      simp only [Bool.toNat_true, mul_one, Bool.toNat_false, add_zero] at h
      have hd : ofBits (SG.subDigits n as bs false).2 < 2 ^ n := by
        have := ofBits_lt_two_pow (SG.subDigits n as bs false).2
        rwa [subDigits_len] at this
      omega
    · intro hlt
      by_cases hbor : (SG.subDigits n as bs false).1 = true
      · exact hbor
      · have hf : (SG.subDigits n as bs false).1 = false := by
          cases h : (SG.subDigits n as bs false).1 <;> simp_all
        have := ofBits_padTo_le_of_subDigits_false n as bs hf
        omega
  · intro n as bs hf
    have h := subDigitsSpec n as bs false
    rw [hf] at h
    simp only [Bool.toNat_false, mul_zero, add_zero] at h
    omega
  · intro n as h
    exact ofBits_padTo_of_le n as h
  · intro n as bs c
    exact subDigits_len n as bs c

end Work.IntLib.SqrtGcd
