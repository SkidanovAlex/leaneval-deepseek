import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate
import Submission.Work.OROneRel.ntDefs

/-!
# A cyclically reduced conjugate has no more non-`t` letters

For a letter `t : α` and an element `w` of a free group, `letterCountNot t w` counts the letters of
the reduced word of `w` which are different from `t` (the length of the Magnus rewriting of `w`).

The main result of this file, `Work.OROneRel.letterCountNot_conj_cyclicReduced_le`, says that a
*cyclically reduced* conjugate `v` of `X` satisfies `letterCountNot t v ≤ letterCountNot t X`.

The classical reason is that the word of `v` is a rotation of the cyclic reduction of the word of
`X`, hence a factor of a rotation of the word of `X`.  The proof below avoids that structure theory
entirely, using instead that the letter count is subadditive under multiplication and that powers of
a cyclically reduced element do not reduce further:

* `letterCountNot t v` is recovered from `v ^ k`, because `v` is cyclically reduced so that powers
  of `v` concatenate without cancellation: `letterCountNot t (v ^ k) = k * letterCountNot t v`;
* writing `v = c * X * c⁻¹` and `v ^ k = c * X ^ k * c⁻¹`, subadditivity gives
  `letterCountNot t (v ^ k) ≤ 2 * letterCountNot t c + k * letterCountNot t X`.

Combining the two for the single (large enough) exponent `k = 2 * letterCountNot t c + 1` gives
`k * letterCountNot t v ≤ 2 * letterCountNot t c + k * letterCountNot t X`; cancelling
`k * letterCountNot t X` leaves `k ≤ 2 * letterCountNot t c`, which contradicts the choice of `k`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### Elementary facts about the letter count, expressed for `letterCountNot` -/

/-- `letterCountNot t w` is `nt t` applied to the reduced word of `w`.  (Both `letterCountNot` and
`nt` are defined using the classical `DecidableEq` instance, which is the one named here.) -/
theorem letterCountNot_eq_nt (t : α) (w : FreeGroup α) :
    letterCountNot t w = nt t (@FreeGroup.toWord α (Classical.decEq α) w) := by
  rw [nt_eq_countP]
  rfl

/-- The count of letters different from `t` on a concatenation of `k` copies of a word. -/
theorem nt_flatten_replicate (t : α) (L : List (α × Bool)) (k : ℕ) :
    nt t (List.replicate k L).flatten = k * nt t L := by
  induction k with
  | zero => simp [nt]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, nt_append, ih]
    ring

/-- The count of letters different from `t` of a `k`-th power is at most `k` times the count of the
base: reduction can only delete letters. -/
theorem nt_toWord_pow_le (t : α) (X : FreeGroup α) (k : ℕ) :
    nt t (@FreeGroup.toWord α (Classical.decEq α) (X ^ k)) ≤
      k * nt t (@FreeGroup.toWord α (Classical.decEq α) X) := by
  classical
  rw [FreeGroup.toWord_pow]
  calc nt t (FreeGroup.reduce (List.replicate k X.toWord).flatten)
      ≤ nt t ((List.replicate k X.toWord).flatten) := nt_red_le FreeGroup.reduce.red
    _ = k * nt t X.toWord := nt_flatten_replicate t X.toWord k

/-- The count of letters different from `t` of a `k`-th power is at most `k` times the count of the
base. -/
theorem letterCountNot_pow_le (t : α) (X : FreeGroup α) (k : ℕ) :
    letterCountNot t (X ^ k) ≤ k * letterCountNot t X := by
  classical
  rw [letterCountNot_eq_nt, letterCountNot_eq_nt]
  exact nt_toWord_pow_le t X k

/-- For a *cyclically reduced* element `v`, the count of letters different from `t` is additive
under taking powers: `v ^ k` is the concatenation of `k` copies of the reduced word of `v`. -/
theorem letterCountNot_pow_of_isCyclicallyReduced (t : α) {v : FreeGroup α}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator v) (k : ℕ) :
    letterCountNot t (v ^ k) = k * letterCountNot t v := by
  classical
  have h_cyc : FreeGroup.IsCyclicallyReduced v.toWord := hcyc
  rw [letterCountNot_eq_nt, letterCountNot_eq_nt, FreeGroup.toWord_pow]
  have hred : FreeGroup.IsReduced (List.replicate k v.toWord).flatten :=
    (h_cyc.flatten_replicate k).isReduced
  rw [(FreeGroup.isReduced_iff_reduce_eq).mp hred]
  exact nt_flatten_replicate t v.toWord k

/-- The count of letters different from `t` is subadditive under multiplication. -/
theorem letterCountNot_mul_le (t : α) (x y : FreeGroup α) :
    letterCountNot t (x * y) ≤ letterCountNot t x + letterCountNot t y := by
  classical
  rw [letterCountNot_eq_nt, letterCountNot_eq_nt, letterCountNot_eq_nt]
  exact nt_mul_le t x y

/-- The count of letters different from `t` is invariant under inversion. -/
theorem letterCountNot_inv (t : α) (x : FreeGroup α) :
    letterCountNot t x⁻¹ = letterCountNot t x := by
  classical
  rw [letterCountNot_eq_nt, letterCountNot_eq_nt]
  exact nt_inv t x

/-! ### The main theorem -/

/-- A cyclically reduced conjugate `v` of `X` has no more letters different from `t` than `X`:
`v` is obtained from `X` by conjugation followed by cyclic reduction, i.e. its word is a rotation of
the cyclic reduction of the word of `X`, which is a factor of a rotation of the word of `X`;
counting letters different from `t` is invariant under rotation and inverse and monotone under
factors. -/
theorem letterCountNot_conj_cyclicReduced_le {α : Type u} (X v : FreeGroup α) (t : α)
    (hconj : IsConj X v) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator v) :
    Work.OROneRel.letterCountNot t v ≤ Work.OROneRel.letterCountNot t X := by
  classical
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  -- `hc : c * X * c⁻¹ = v`
  by_contra hcon
  rw [not_le] at hcon
  -- the exponent is chosen so large that `2 * letterCountNot t c < k`
  set K : ℕ := 2 * letterCountNot t c + 1 with hK
  have hpow : v ^ K = c * X ^ K * c⁻¹ := by
    rw [← hc]
    exact conj_pow
  have hmain : K * letterCountNot t v ≤ 2 * letterCountNot t c + K * letterCountNot t X := by
    calc K * letterCountNot t v
        = letterCountNot t (v ^ K) :=
          (letterCountNot_pow_of_isCyclicallyReduced t hcyc K).symm
      _ = letterCountNot t (c * X ^ K * c⁻¹) := by rw [hpow]
      _ ≤ letterCountNot t (c * X ^ K) + letterCountNot t c⁻¹ :=
          letterCountNot_mul_le t (c * X ^ K) c⁻¹
      _ = letterCountNot t (c * X ^ K) + letterCountNot t c := by rw [letterCountNot_inv]
      _ ≤ (letterCountNot t c + letterCountNot t (X ^ K)) + letterCountNot t c :=
          Nat.add_le_add_right (letterCountNot_mul_le t c (X ^ K)) _
      _ ≤ (letterCountNot t c + K * letterCountNot t X) + letterCountNot t c :=
          Nat.add_le_add_right
            (Nat.add_le_add_left (letterCountNot_pow_le t X K) _) _
      _ = 2 * letterCountNot t c + K * letterCountNot t X := by ring
  have hfin : K * (letterCountNot t X + 1) ≤ 2 * letterCountNot t c + K * letterCountNot t X :=
    le_trans (Nat.mul_le_mul_left K (Nat.succ_le_of_lt hcon)) hmain
  rw [Nat.mul_succ] at hfin
  omega

end Work.OROneRel
