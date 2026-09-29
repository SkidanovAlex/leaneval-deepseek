import Mathlib
import Submission.Work.TMC14Core.Weyl
import Submission.Work.TMC14Core.CntSucc
import Submission.Work.TMC14Core.InvCountSucc
import Submission.Work.TMC14Core.WUPowWV

/-!
# TMC14Core: the explicit normal form of a word in the two Weyl letters `U`, `V`

For the clock-and-shift Weyl pair of `Weyl.lean`, let `U = wU q k` and `V = wV p q θ`.
They satisfy the Weyl relation `U V = om p q • (V U)` (`wU_mul_wV`).  Consequently any
word over `{U, V}` can be sorted to the canonical monomial `V^{#V} · U^{#U}`, at the
price of one factor `ω = om p q` for every pair `<U, V>` in the word (a `U` occurring
before a `V`).

This file makes that bookkeeping explicit: for a word `f : Fin n → Bool × Bool` whose
letters are only `U = (true,true)` and `V = (false,true)`,

`wordProd p q θ k n f = ω ^ invCount n f • (V ^ #V * U ^ #U)`,

where `invCount n f` counts the `<U, V>` pairs.  (This refines `WordNormalForm`, which
only tracks the scalar multiple up to an unspecified `u ≠ 0`.)

The proof is an induction on the length of the word that peels off the first letter and
uses the commutation `U · V ^ a = ω ^ a • (V ^ a · U)`.
-/

open Matrix

noncomputable section

namespace Work.TMC14Core

/-- **Explicit normal form of a `U`/`V` word.**  A word over the two Weyl letters
`U = (true,true)` and `V = (false,true)` equals `ω ^ invCount` times the canonical
monomial `V ^ #V * U ^ #U`, where `ω = om p q`. -/
theorem InterleaveWordNorm (p : ℤ) (q : ℕ) (θ k : ℝ) (n : ℕ) (f : Fin n → Bool × Bool)
    (h : ∀ i, f i = (true, true) ∨ f i = (false, true)) :
    wordProd p q θ k n f = (om p q) ^ (invCount n f) •
      ((wV p q θ) ^ ((Finset.univ.filter (fun i : Fin n => f i = (false, true))).card) *
       (wU q k) ^ ((Finset.univ.filter (fun i : Fin n => f i = (true, true))).card)) := by
  -- `cnt` is by definition the cardinality of the corresponding filter, so we may
  -- re-state the goal in that shorthand.
  show wordProd p q θ k n f = (om p q) ^ invCount n f •
      ((wV p q θ) ^ (cnt false true n f) * (wU q k) ^ (cnt true true n f))
  revert h f
  induction n with
  | zero =>
    intro f h
    simp only [wordProd, List.ofFn_zero, List.map_nil, List.prod_nil]
    simp [cnt, invCount]
  | succ n ih =>
    intro f h
    -- peel off the first letter
    have hwp : wordProd p q θ k (n + 1) f =
        letterOf p q θ k (f 0) * wordProd p q θ k n (fun i => f i.succ) := by
      simp only [wordProd, List.ofFn_succ, List.map_cons, List.prod_cons]
    rw [hwp, ih (fun i => f i.succ) (fun i => h i.succ)]
    -- split off the head letters in `invCount` and the two `cnt`s
    rw [CntSucc false true n f, CntSucc true true n f, InvCountSucc n f]
    rcases h 0 with h0 | h0
    · -- head is `U = (true,true)`
      rw [h0, show letterOf p q θ k (true, true) = wU q k from by simp [letterOf]]
      rw [Matrix.mul_smul,
        WUPowWV p q θ k (cnt false true n fun i => f i.succ)
          (wU q k ^ cnt true true n fun i => f i.succ),
        smul_smul, ← pow_add, ← pow_succ']
      simp only [Prod.mk.injEq, Bool.true_eq_false, and_true, if_true, if_false, Nat.add_zero]
    · -- head is `V = (false,true)`
      rw [h0, show letterOf p q θ k (false, true) = wV p q θ from by simp [letterOf]]
      rw [Matrix.mul_smul, ← mul_assoc, ← pow_succ']
      simp only [Prod.mk.injEq, Bool.false_eq_true, and_true, if_true, if_false, Nat.add_zero]

end Work.TMC14Core
