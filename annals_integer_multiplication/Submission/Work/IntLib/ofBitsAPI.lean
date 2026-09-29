import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.ofBits_bits
import Submission.Work.IntLib.bits_ofBits_of_isBits
import Submission.Work.IntLib.ofBits_take_drop_bits

namespace Work.IntLib

/-- On canonical bit strings, `ofBits` vanishes only on the empty list. -/
theorem ofBits_eq_zero_iff_of_isBits (xs : List Bool) (h : IsBits xs) :
    ofBits xs = 0 ↔ xs = [] := by
  constructor
  · intro h0
    have h1 := bits_ofBits_of_isBits xs h
    rw [h0] at h1
    rw [← h1]; simp
  · rintro rfl; rfl

theorem ofBitsAPI : (∀ n : ℕ, Work.IntLib.ofBits n.bits = n) ∧ (∀ xs : List Bool, Work.IntLib.IsBits xs → (Work.IntLib.ofBits xs).bits = xs) ∧ (∀ xs ys : List Bool, Work.IntLib.ofBits (xs ++ ys) = Work.IntLib.ofBits xs + 2 ^ xs.length * Work.IntLib.ofBits ys) ∧ (∀ xs : List Bool, Work.IntLib.ofBits xs < 2 ^ xs.length) ∧ (∀ (b : Bool) (xs : List Bool), Work.IntLib.ofBits (b :: xs) = b.toNat + 2 * Work.IntLib.ofBits xs) ∧ (∀ (xs : List Bool) (k : ℕ), Work.IntLib.ofBits xs = Work.IntLib.ofBits (xs.take k) + 2 ^ k * Work.IntLib.ofBits (xs.drop k)) ∧ (∀ (n k : ℕ), Work.IntLib.ofBits ((n.bits).take k) = n % 2 ^ k) ∧ (∀ (n k : ℕ), Work.IntLib.ofBits ((n.bits).drop k) = n / 2 ^ k) ∧ (∀ xs : List Bool, Work.IntLib.IsBits xs → (Work.IntLib.ofBits xs = 0 ↔ xs = [])) ∧ (∀ xs ys : List Bool, Work.IntLib.IsBits xs → Work.IntLib.IsBits ys → Work.IntLib.IsBits (xs ++ ys)) ∧ (∀ (b : Bool) (xs : List Bool), Work.IntLib.IsBits xs → xs ≠ [] → Work.IntLib.IsBits (b :: xs)) := by
  exact ⟨ofBits_bits, fun xs h => bits_ofBits_of_isBits xs h, ofBits_append,
    ofBits_lt_two_pow, ofBits_cons, ofBits_take_drop,
    fun n k => (ofBits_take_drop_bits n k).1, fun n k => (ofBits_take_drop_bits n k).2,
    ofBits_eq_zero_iff_of_isBits, fun xs ys hx hy => isBits_append hx hy,
    fun b xs h hne => isBits_cons h hne⟩

end Work.IntLib
