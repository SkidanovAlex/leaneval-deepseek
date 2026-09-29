import Mathlib
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.ofBits_bits
import Submission.Work.IntLib.divFoldBvalBridge

/-!
# The arithmetic core of binary long division (`IntLib`)

`Work.IntLib.dstep` and `Work.IntLib.divFold` (defined in `Submission/Work/IntLib/divRaw.lean`)
are the pure-arithmetic long-division step and fold underlying the raw division word: `dstep bv st d`
reads the next dividend bit `d` (most significant first) into the state `st = (quotient, remainder)`
of the division of the already-read prefix by `bv`, and `divFold bv A` runs this over the whole bit
list `A`.

This file proves the API the correctness proof of the division word needs:

* `dstep` preserves the bound `st.2 < bv` and satisfies the long-division invariant
  `bv * q + r = 2 * (bv * a + b) + d`;
* consequently the same holds for the whole fold `divFold`, whose value identity gives
  `bv * (divFold bv A).1 + (divFold bv A).2 = bval A` (the number read most-significant first);
* the last two conjuncts, comparing `bval` (a left fold, most-significant first) with `ofBits`
  (a right fold, least-significant first) after reversing the list, are proved in the companion
  module `Submission/Work/IntLib/divFoldBvalBridge.lean` and imported here.
-/

namespace Work.IntLib

/-! ## The one-step division invariant -/

/-- Reading one more most-significant-first bit appends it to the right of the number read so far. -/
theorem bval_append_singleton (A : List Bool) (b : Bool) :
    bval (A ++ [b]) = 2 * bval A + b.toNat := by
  simp [bval, List.foldl_append]

/-- `dstep` maps states with `st.2 < bv` to states with `st.2 < bv` (for `0 < bv`). -/
theorem dstep_snd_lt (bv : ℕ) (st : ℕ × ℕ) (d : Bool) (hbv : 0 < bv) (h : st.2 < bv) :
    (dstep bv st d).2 < bv := by
  have hd : d.toNat ≤ 1 := by cases d <;> simp
  unfold dstep
  dsimp only
  split_ifs with hq
  · omega
  · omega

/-- The long-division invariant: one `dstep` doubles the number read so far (adding the new bit),
keeping the identity `bv * quotient + remainder` true. -/
theorem dstep_val (bv : ℕ) (st : ℕ × ℕ) (d : Bool) :
    bv * (dstep bv st d).1 + (dstep bv st d).2 = 2 * (bv * st.1 + st.2) + d.toNat := by
  unfold dstep
  dsimp only
  split_ifs with hq
  · simp only [one_mul]
    have hkey : bv * (2 * st.1 + 1) + (2 * st.2 + d.toNat)
        = (2 * (bv * st.1 + st.2) + d.toNat) + bv := by ring
    have hsub : 2 * st.2 + d.toNat - bv + bv = 2 * st.2 + d.toNat := Nat.sub_add_cancel hq
    have hL : bv * (2 * st.1 + 1) + (2 * st.2 + d.toNat - bv) + bv
        = (2 * (bv * st.1 + st.2) + d.toNat) + bv := by
      calc bv * (2 * st.1 + 1) + (2 * st.2 + d.toNat - bv) + bv
          = bv * (2 * st.1 + 1) + ((2 * st.2 + d.toNat - bv) + bv) := Nat.add_assoc _ _ _
        _ = bv * (2 * st.1 + 1) + (2 * st.2 + d.toNat) := by rw [hsub]
        _ = (2 * (bv * st.1 + st.2) + d.toNat) + bv := hkey
    exact Nat.add_right_cancel hL
  · simp only [zero_mul, Nat.sub_zero]
    ring

/-! ## The fold -/

/-- One `divFold` step at the end of the list. -/
theorem divFold_step (bv : ℕ) (A : List Bool) (b : Bool) :
    divFold bv (A ++ [b]) = dstep bv (divFold bv A) b := by
  simp [divFold, List.foldl_append]

/-- `divFold` maps into states with `st.2 < bv` (for `0 < bv`). -/
theorem divFold_snd_lt (bv : ℕ) (A : List Bool) (hbv : 0 < bv) :
    (divFold bv A).2 < bv := by
  induction A using List.reverseRecOn with
  | nil => simpa [divFold] using hbv
  | append_singleton A b ih =>
    rw [divFold_step]
    exact dstep_snd_lt bv (divFold bv A) b hbv ih

/-- The value identity for the whole division fold: `divFold bv A` reads the number `bval A`. -/
theorem divFold_val (bv : ℕ) (A : List Bool) :
    bv * (divFold bv A).1 + (divFold bv A).2 = bval A := by
  induction A using List.reverseRecOn with
  | nil => simp [divFold, bval]
  | append_singleton A b ih =>
    rw [divFold_step, dstep_val, ih, bval_append_singleton]

/-! ## The API -/

theorem divFoldAPI :
    (∀ (bv : ℕ) (st : ℕ × ℕ) (d : Bool), 0 < bv → st.2 < bv →
      (Work.IntLib.dstep bv st d).2 < bv) ∧
    (∀ (bv : ℕ) (st : ℕ × ℕ) (d : Bool), 0 < bv → st.2 < bv →
      bv * (Work.IntLib.dstep bv st d).1 + (Work.IntLib.dstep bv st d).2 =
        2 * (bv * st.1 + st.2) + d.toNat) ∧
    (∀ (bv : ℕ) (A : List Bool), 0 < bv → (Work.IntLib.divFold bv A).2 < bv) ∧
    (∀ (bv : ℕ) (A : List Bool), 0 < bv →
      bv * (Work.IntLib.divFold bv A).1 + (Work.IntLib.divFold bv A).2 = Work.IntLib.bval A) ∧
    (∀ (A : List Bool), Work.IntLib.bval A = Work.IntLib.ofBits A.reverse) ∧
    (∀ (n : ℕ), Work.IntLib.bval n.bits.reverse = n) := by
  exact ⟨fun bv st d hbv h => dstep_snd_lt bv st d hbv h,
    fun bv st d _ _ => dstep_val bv st d,
    fun bv A hbv => divFold_snd_lt bv A hbv,
    fun bv A _ => divFold_val bv A,
    divFoldBvalBridge.1,
    divFoldBvalBridge.2⟩

end Work.IntLib
