import Mathlib
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.ofBits_bits

namespace Work.IntLib

/-- `foldr` over a `List Bool` with the `ℕ`-step `acc ↦ 2*acc + b` is the same as with the
step `acc ↦ b + 2*acc`; only the order of the two summands differs.  This is the bridge
between `bval` (a `foldl` of `acc ↦ 2*acc + b`) and `ofBits` (a `foldr` of `acc ↦ b + 2*acc`). -/
theorem foldr_two_mul_add_comm (l : List Bool) :
    List.foldr (fun (x : Bool) (y : ℕ) => 2 * y + x.toNat) 0 l =
      List.foldr (fun (x : Bool) (y : ℕ) => x.toNat + 2 * y) 0 l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.foldr_cons, List.foldr_cons, ih, Nat.add_comm]

/-- `bval` (the most-significant-bit-first fold of `divFold`) is `ofBits` of the reversed
list (the least-significant-bit-first reading). -/
theorem bval_eq_ofBits_reverse (A : List Bool) :
    Work.IntLib.bval A = Work.IntLib.ofBits A.reverse := by
  simp only [Work.IntLib.bval, Work.IntLib.ofBits, List.foldl_eq_foldr_reverse]
  exact foldr_two_mul_add_comm A.reverse

theorem divFoldBvalBridge :
    (∀ (A : List Bool), Work.IntLib.bval A = Work.IntLib.ofBits A.reverse) ∧
    (∀ (n : ℕ), Work.IntLib.bval n.bits.reverse = n) := by
  refine ⟨bval_eq_ofBits_reverse, ?_⟩
  intro n
  simp only [Work.IntLib.bval, List.foldl_eq_foldr_reverse, List.reverse_reverse]
  rw [foldr_two_mul_add_comm n.bits]
  exact Work.IntLib.ofBits_bits n

end Work.IntLib
