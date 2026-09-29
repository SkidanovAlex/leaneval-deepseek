import Mathlib
import Submission.Work.IntLib.SqrtGcd.SubDefs

/-!
# Correctness of the ripple subtraction `SG.subDigits`

`SG.subDigits n as bs c` performs `n` ripple subtraction steps on the least-significant-first
bit lists `as`, `bs` starting from the incoming borrow `c`, and returns the outgoing borrow
together with the digit list (least significant first).  The identity proved here is the
usual one for schoolbook subtraction with borrow:

  `⟨as⟩ + 2ⁿ · borrow = ⟨bs⟩ + ⟨digits⟩ + c`,

where `⟨·⟩` reads a list as the corresponding `ℕ` (`ofBits`), the lists being zero-padded to
length `n` by `SG.padTo` (so that `subDigits` sees exactly the same bits as `ofBits`).
This is the arithmetic content of the ripple subtracter used by the word
`HvdH.IntLib.sqrt`/`gcd`: it says that the borrow returned by the loop is exactly what has to
be carried out beyond the top digit.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

/-- `padTo` one step: the padding of a list to length `n+1` is its (defaulted) head followed by
the padding of its tail to length `n`. -/
theorem padTo_succ (n : ℕ) (as : List Bool) :
    Work.IntLib.SG.padTo (n + 1) as =
      as.headD false :: Work.IntLib.SG.padTo n as.tail := by
  cases as with
  | nil => simp [Work.IntLib.SG.padTo, List.replicate_succ]
  | cons a t => simp [Work.IntLib.SG.padTo, List.take_succ_cons]

/-- **Ripple subtraction is correct.**  After `n` steps of `subDigits` starting from the
incoming borrow `c`, the padded minuend plus `2 ^ n` times the outgoing borrow equals the
padded subtrahend plus the produced digits plus the incoming borrow. -/
theorem subDigitsSpec : ∀ (n : ℕ) (as bs : List Bool) (c : Bool),
    Work.IntLib.ofBits (Work.IntLib.SG.padTo n as) +
        2 ^ n * (Work.IntLib.SG.subDigits n as bs c).1.toNat
      = Work.IntLib.ofBits (Work.IntLib.SG.padTo n bs) +
        Work.IntLib.ofBits (Work.IntLib.SG.subDigits n as bs c).2 + c.toNat := by
  intro n
  induction n with
  | zero =>
      intro as bs c
      simp [Work.IntLib.SG.padTo, Work.IntLib.SG.subDigits, Work.IntLib.ofBits]
  | succ n ih =>
      intro as bs c
      simp only [Work.IntLib.SG.subDigits]
      rw [padTo_succ, padTo_succ]
      simp only [Work.IntLib.ofBits_cons]
      -- the inductive hypothesis, with the borrow `subBw x y c` fed in
      have h := ih as.tail bs.tail
        (Work.IntLib.SG.subBw (as.headD false) (bs.headD false) c)
      -- the single-bit identity `x + 2·(borrow out) = y + c + (digit)`
      have h2 := Work.IntLib.SG.subBw_subBit (as.headD false) (bs.headD false) c
      -- `2 ^ (n+1) · b = 2 · (2 ^ n · b)`
      have hp : 2 ^ (n + 1) * (Work.IntLib.SG.subDigits n as.tail bs.tail
              (Work.IntLib.SG.subBw (as.headD false) (bs.headD false) c)).1.toNat
          = 2 * (2 ^ n * (Work.IntLib.SG.subDigits n as.tail bs.tail
              (Work.IntLib.SG.subBw (as.headD false) (bs.headD false) c)).1.toNat) := by
        rw [pow_succ]; ring
      rw [hp]
      omega

end Work.IntLib.SqrtGcd
