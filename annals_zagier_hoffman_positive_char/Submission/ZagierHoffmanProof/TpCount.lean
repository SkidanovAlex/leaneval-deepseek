import Submission.ZagierHoffmanProof.Carlitz
import Submission.ZagierHoffmanProof.Counting
import Submission.Commons.Combinatorics.TupleCount.tpW_card_small
import Submission.Commons.Combinatorics.TupleCount.tpW_rec_large

/-!
# The count of the `q ∤ s_i`-tuples: `|𝒯'_w| = d(w)`

Ngo Dac's Lemma 6.1(1): the set of tuples of weight `w ≤ 2q-2` all of whose entries are not
divisible by `q` has cardinality `d(w)`.  The counting itself is in the commons
(`tpW_card_small`, `tpW_rec_large`); here we match it with the recursion defining `d`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial RatFunc Finset
open scoped BigOperators

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The recursion of `d` -/

lemma d_of_zero : d F 0 = 1 := by
  rw [d]
  simp

lemma d_of_lt {w : ℕ} (hw1 : 1 ≤ w) (hwq : w < Nat.card F) :
    d F w = 2 ^ (w - 1) := by
  rw [d, if_neg (by omega : ¬ w = 0), if_pos (by omega : w ≤ Nat.card F - 1)]

lemma d_of_eq_card {w : ℕ} (hwq : w = Nat.card F) : d F w = 2 ^ (w - 1) - 1 := by
  subst hwq
  have hq : 2 ≤ Nat.card F := carlitz_card_ge_two F
  rw [d, if_neg (by omega : ¬ Nat.card F = 0),
    if_neg (by omega : ¬ Nat.card F ≤ Nat.card F - 1), if_pos rfl]

lemma d_of_gt {w : ℕ} (hwq : Nat.card F < w) :
    d F w = ∑ i ∈ Finset.range (Nat.card F), d F (w - (i + 1)) := by
  rw [d, if_neg (by omega : ¬ w = 0), if_neg (by omega : ¬ w ≤ Nat.card F - 1),
    if_neg (by omega : ¬ w = Nat.card F)]

lemma d_of_le {w : ℕ} (hw1 : 1 ≤ w) (hwq : w ≤ Nat.card F) :
    d F w = 2 ^ (w - 1) - (if w = Nat.card F then 1 else 0) := by
  have hq : 2 ≤ Nat.card F := carlitz_card_ge_two F
  by_cases hlt : w ≤ Nat.card F - 1
  · rw [d, if_neg (by omega : ¬ w = 0), if_pos hlt,
      if_neg (by omega : ¬ w = Nat.card F), Nat.sub_zero]
  · have heq : w = Nat.card F := by omega
    rw [d, if_neg (by omega : ¬ w = 0), if_neg hlt, if_pos heq, if_pos heq]

/-! ## §2. The type of `q ∤`-tuples -/

/-- The `q ∤ s_i`-tuples of weight `w` (entries `≥ 1`, `q ∤ s_i`, sum `= w`), in the exact shape
of the commons counting lemmas. -/
@[reducible] def TpType (w : ℕ) : Type :=
  {x : Σ r : Fin (2 * Nat.card F), Fin r → Fin (2 * Nat.card F) //
    (∀ j, 1 ≤ ((x.2 j : Fin (2 * Nat.card F)) : ℕ)) ∧
    (∀ j, ¬ (Nat.card F ∣ ((x.2 j : Fin (2 * Nat.card F)) : ℕ))) ∧
    (∑ j, ((x.2 j : Fin (2 * Nat.card F)) : ℕ)) = w}

theorem card_TpType (w : ℕ) (hw : 1 ≤ w) (hw2 : w ≤ 2 * Nat.card F - 2) :
    Nat.card (TpType F w) = d F w := by
  have hq : 2 ≤ Nat.card F := carlitz_card_ge_two F
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  rcases le_or_gt w (Nat.card F) with hwq | hwq
  · rw [d_of_le F hw hwq,
      Commons.Combinatorics.TupleCount.tpW_card_small (Nat.card F) w hq hw hwq]
  · have hrec : Nat.card (TpType F w)
        = ∑ i ∈ Finset.range (Nat.card F), Nat.card (TpType F (w - (i + 1))) := by
      rw [Commons.Combinatorics.TupleCount.tpW_rec_large (Nat.card F) w hq hwq hw2]
    rw [hrec, d_of_gt F hwq]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < Nat.card F := Finset.mem_range.mp hi
    have h1 : 1 ≤ w - (i + 1) := by omega
    have h2 : w - (i + 1) < w := by omega
    have h3 : w - (i + 1) ≤ 2 * Nat.card F - 2 := by omega
    exact ih _ h2 h1 h3

end ZagierHoffmanPositiveChar
