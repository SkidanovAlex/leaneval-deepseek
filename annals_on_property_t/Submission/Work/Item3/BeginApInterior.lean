import Submission.Work.Item3.RowInvariant
import Submission.Commons.GroupTheory.FreeGroup.reduce_append_invRev_right

open Submission.Nielsen
open FreeGroup
set_option autoImplicit false

/-!
# The interior subcase of the ACTIVE TARGET: pure reducedness (no run structure)

The active target's `beginAp` obstruction (post-state `i < p`, even word `q`
beginning with the balanced first half `A`): the second half of `q` is not a
suffix of `invRev A`.  At the boundary `|q| = 2|A|` this is the pure
reducedness fact `A ++ invRev A` is never reduced (`Item3/BeginApBoundary.lean`).
**The interior subcase `|q| < 2|A|` is ALSO pure reducedness** — this module
proves that no *reduced word at all* (no run structure needed) admits the
interior configuration.  Clean proof: with `m := |q|/2`, `P := q.take m`,
`S := q.drop m`, a reduced `q` of even length satisfies `q = P ++ S`
(`take_append_drop`); if `S` were a suffix of `invRev A`, then (as `S` has
length `m` and `q` begins with `A`, `m ≤ |A|`) `P = A.take m` and the
length-`m` suffix identity give `S = invRev (A.take m) = invRev P`, so
`q = P ++ invRev P` with `P ≠ []` — impossible for a reduced word (the
consecutive block `P ++ invRev P` fully cancels).  Machine: 0 reduced words
over 2/3 letters up to length 6 admit the configuration (`/tmp/fg2`) — the
interior claim holds for ALL reduced words, not only genuine-run post-words.

Main theorems:

    beginAp_interior_obstruction : IsReduced q → BeginsWithWord q A →
        q.length % 2 = 0 → q.length < 2 * A.length → A ≠ [] →
        ¬ EndsWithWord (invRev A) (secondHalf q)
    endInv_interior_obstruction  : IsReduced q → EndsWithWord q (invRev A) →
        q.length % 2 = 0 → q.length < 2 * A.length → A ≠ [] →
        ¬ BeginsWithWord A (firstHalf q)

(the mirror follows from the first by the reversal involution
`q ↦ invRev q`: `invRev q` begins with `A`, and the identity
`secondHalf (invRev q) = invRev (firstHalf q)` transports the suffix
obstruction to the prefix obstruction).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ### list helpers -/

/-- A word of even length is twice its half-length. -/
lemma even_length_eq_two_mul {α : Type*} (W : List α) (h : W.length % 2 = 0) :
    W.length = 2 * (W.length / 2) := by
  have hdiv := Nat.div_add_mod W.length 2
  rw [h] at hdiv
  omega

/-- `invRev` is length preserving. -/
lemma invRev_length' {α : Type*} (L : List (α × Bool)) :
    (FreeGroup.invRev L).length = L.length :=
  FreeGroup.invRev_length

/-- `invRev` of a reduced word is reduced. -/
lemma reduced_invRev_reduced {α : Type*} [DecidableEq α] (L : List (α × Bool))
    (hL : FreeGroup.IsReduced L) : FreeGroup.IsReduced (FreeGroup.invRev L) := by
  rw [FreeGroup.isReduced_iff_reduce_eq]
  rw [FreeGroup.reduce_invRev]
  rw [FreeGroup.isReduced_iff_reduce_eq.mp hL]

/-- A suffix of `invRev A` of length `≤ |A|` is the inverse-reversal of the
corresponding prefix of `A`. -/
lemma suffix_of_invRev {α : Type*} (A S : List (α × Bool))
    (hS : EndsWithWord (FreeGroup.invRev A) S) (hle : S.length ≤ A.length) :
    S = FreeGroup.invRev (A.take S.length) := by
  rcases hS with ⟨U, hUA⟩
  have hUlen : U.length = A.length - S.length := by
    have hlen : (U ++ S).length = A.length := by
      rw [← hUA, FreeGroup.invRev_length]
    rw [List.length_append] at hlen
    omega
  have hdec : FreeGroup.invRev A =
      FreeGroup.invRev (A.drop S.length) ++ FreeGroup.invRev (A.take S.length) := by
    have hc := congrArg FreeGroup.invRev (List.take_append_drop S.length A)
    rw [FreeGroup.invRev_append] at hc
    exact hc.symm
  have hEq : U ++ S =
      FreeGroup.invRev (A.drop S.length) ++ FreeGroup.invRev (A.take S.length) :=
    hUA.symm.trans hdec
  have hdrop := congrArg (fun W : List (α × Bool) => W.drop (A.length - S.length)) hEq
  have hd1 : (U ++ S).drop (A.length - S.length) = S := by
    rw [hUlen.symm]
    rw [List.drop_append_of_le_length (l₁ := U) (l₂ := S) (i := U.length) (by rfl)]
    simp
  have hd2 : (FreeGroup.invRev (A.drop S.length) ++ FreeGroup.invRev (A.take S.length)).drop
        (A.length - S.length) = FreeGroup.invRev (A.take S.length) := by
    have hlen1 : (FreeGroup.invRev (A.drop S.length)).length = A.length - S.length := by
      rw [FreeGroup.invRev_length]
      rw [List.length_drop]
    rw [hlen1.symm]
    rw [List.drop_append_of_le_length
      (l₁ := FreeGroup.invRev (A.drop S.length))
      (l₂ := FreeGroup.invRev (A.take S.length))
      (i := (FreeGroup.invRev (A.drop S.length)).length) (by rfl)]
    simp
  rw [hd1, hd2] at hdrop
  exact hdrop

/-- A word that begins with `F` has its inverse-reversal ending with the
inverse-reversal of `F`: `BeginsWithWord A F → EndsWithWord (invRev A)
(invRev F)`. -/
lemma begins_imp_invRev_ends {α : Type*} (A F : List (α × Bool))
    (hB : BeginsWithWord A F) : EndsWithWord (FreeGroup.invRev A) (FreeGroup.invRev F) := by
  rcases hB with ⟨Z, hAZ⟩
  refine ⟨FreeGroup.invRev Z, ?_⟩
  calc
    FreeGroup.invRev A = FreeGroup.invRev (F ++ Z) := by rw [hAZ]
    _ = FreeGroup.invRev Z ++ FreeGroup.invRev F := by rw [FreeGroup.invRev_append]

/-- `secondHalf (invRev W) = invRev (firstHalf W)` for an even word `W`. -/
lemma secondHalf_invRev_of_even {α : Type*} (W : List (α × Bool))
    (h : W.length % 2 = 0) :
    secondHalf (FreeGroup.invRev W) = FreeGroup.invRev (firstHalf W) := by
  have hE2 : W.length = 2 * (W.length / 2) := even_length_eq_two_mul W h
  have hslen : (secondHalf W).length = W.length / 2 := by
    unfold secondHalf
    rw [List.length_drop]
    omega
  have hInv : FreeGroup.invRev W =
      FreeGroup.invRev (secondHalf W) ++ FreeGroup.invRev (firstHalf W) := by
    have hc := congrArg FreeGroup.invRev (firstHalf_append_secondHalf W)
    rw [FreeGroup.invRev_append] at hc
    exact hc.symm
  unfold secondHalf
  rw [FreeGroup.invRev_length]
  rw [hInv]
  have hle : W.length / 2 ≤ (FreeGroup.invRev (secondHalf W)).length := by
    rw [FreeGroup.invRev_length]
    omega
  rw [List.drop_append_of_le_length (l₁ := FreeGroup.invRev (secondHalf W))
    (l₂ := FreeGroup.invRev (firstHalf W)) (i := W.length / 2) (by exact hle)]
  have hd : (FreeGroup.invRev (secondHalf W)).drop (W.length / 2) = [] := by
    rw [List.drop_eq_nil_of_le]
    rw [FreeGroup.invRev_length]
    omega
  simp [hd]

/-! ### the interior obstructions -/

/-- **The `beginAp` interior obstruction.**  No reduced word `q` of even
length beginning with `A` and shorter than `2|A|` has its second half equal
to a suffix of `invRev A`: with `m := |q|/2`, `P := q.take m` and
`S := q.drop m`, the word decomposes as `q = P ++ S`, while `S` a suffix of
`invRev A` forces `S = invRev P`, so `q = P ++ invRev P` with `P ≠ []` —
impossible for a reduced word. -/
theorem beginAp_interior_obstruction {α : Type*} [DecidableEq α]
    (A q : List (α × Bool)) (hA : A ≠ []) (hred : FreeGroup.IsReduced q)
    (hbeg : BeginsWithWord q A) (heven : q.length % 2 = 0)
    (hint : q.length < 2 * A.length) :
    ¬ EndsWithWord (FreeGroup.invRev A) (secondHalf q) := by
  classical
  let m : ℕ := q.length / 2
  let P : List (α × Bool) := q.take m
  let S : List (α × Bool) := q.drop m
  intro hS0
  have hSdef : secondHalf q = S := by
    dsimp [S, secondHalf, m]
  have hS : EndsWithWord (FreeGroup.invRev A) S := by
    simpa [hSdef] using hS0
  rcases hbeg with ⟨X, hqA⟩
  have hE2 : q.length = 2 * m := by
    dsimp [m]
    exact even_length_eq_two_mul q heven
  have hSlen : S.length = m := by
    dsimp [S, m]
    rw [List.length_drop]
    omega
  have hmA : m ≤ A.length := by
    dsimp [m]
    have : 2 * (q.length / 2) < 2 * A.length := by
      rw [← even_length_eq_two_mul q heven]
      exact hint
    omega
  have hqpos : 0 < q.length := by
    rw [hqA]
    cases A with
    | nil => exfalso; exact hA rfl
    | cons a t => simp
  have hm1 : 1 ≤ m := by
    dsimp [m]
    have : 2 ≤ q.length := by omega
    omega
  have hPlen : P.length = m := by
    dsimp [P, m]
    rw [List.length_take]
    have hle : q.length / 2 ≤ q.length := by omega
    exact min_eq_left hle
  have hSinv : S = FreeGroup.invRev (A.take S.length) := by
    apply suffix_of_invRev A S hS
    omega
  have hP : P = A.take m := by
    dsimp [P, m]
    rw [hqA]
    have hle : (A ++ X).length / 2 ≤ A.length := by
      have heven' : (A ++ X).length % 2 = 0 := by simpa [hqA] using heven
      have hint' : (A ++ X).length < 2 * A.length := by simpa [hqA] using hint
      have hE := even_length_eq_two_mul (A ++ X) heven'
      omega
    rw [List.take_append_of_le_length (l₁ := A) (l₂ := X) (i := (A ++ X).length / 2) hle]
  have hSinvP : S = FreeGroup.invRev P := by
    have htake : A.take S.length = A.take m := by
      exact congrArg (fun n : ℕ => A.take n) (by omega)
    calc
      S = FreeGroup.invRev (A.take S.length) := hSinv
      _ = FreeGroup.invRev (A.take m) := by rw [htake]
      _ = FreeGroup.invRev P := by rw [hP]
  have hqP : q = P ++ FreeGroup.invRev P := by
    calc
      q = q.take m ++ q.drop m := (List.take_append_drop m q).symm
      _ = P ++ S := by
            dsimp [P, S]
      _ = P ++ FreeGroup.invRev P := by rw [hSinvP]
  have hPne : P ≠ [] := by
    intro hP0
    have : m = 0 := by
      rw [← hPlen, hP0]
      rfl
    omega
  have hredP : FreeGroup.IsReduced (P ++ FreeGroup.invRev P) := by
    simpa [hqP] using hred
  have hrv : FreeGroup.reduce (P ++ FreeGroup.invRev P) = P ++ FreeGroup.invRev P :=
    FreeGroup.isReduced_iff_reduce_eq.mp hredP
  have hc : FreeGroup.reduce (P ++ FreeGroup.invRev P) = [] :=
    Commons.GroupTheory.FreeGroup.reduce_append_invRev_right P
  have hne : P ++ FreeGroup.invRev P ≠ [] := by
    intro hz
    have hzlen : (P ++ FreeGroup.invRev P).length = 0 := by rw [hz]; rfl
    have hlen : (P ++ FreeGroup.invRev P).length = P.length + P.length := by
      rw [List.length_append, FreeGroup.invRev_length]
    have hPpos : 1 ≤ P.length := by
      rw [hPlen]
      exact hm1
    omega
  exact hne (hrv.symm.trans hc)

/-- **The `endInv` interior obstruction (mirror).**  No reduced word `q` of
even length ending with `invRev A` and shorter than `2|A|` has its first
half equal to a prefix of `A`: apply the `beginAp` obstruction to the
reversal `invRev q` (which begins with `A`) and transport the suffix
obstruction through `secondHalf (invRev q) = invRev (firstHalf q)`. -/
theorem endInv_interior_obstruction {α : Type*} [DecidableEq α]
    (A q : List (α × Bool)) (hA : A ≠ []) (hred : FreeGroup.IsReduced q)
    (hend : EndsWithWord q (FreeGroup.invRev A)) (heven : q.length % 2 = 0)
    (hint : q.length < 2 * A.length) :
    ¬ BeginsWithWord A (firstHalf q) := by
  intro hB
  -- invRev q begins with A
  have hbeg : BeginsWithWord (FreeGroup.invRev q) A := by
    rcases hend with ⟨Y, hqY⟩
    refine ⟨FreeGroup.invRev Y, ?_⟩
    calc
      FreeGroup.invRev q = FreeGroup.invRev (Y ++ FreeGroup.invRev A) := by rw [hqY]
      _ = FreeGroup.invRev (FreeGroup.invRev A) ++ FreeGroup.invRev Y := by
            rw [FreeGroup.invRev_append]
      _ = A ++ FreeGroup.invRev Y := by rw [FreeGroup.invRev_invRev]
  have hred' : FreeGroup.IsReduced (FreeGroup.invRev q) :=
    reduced_invRev_reduced q hred
  have hEv : (FreeGroup.invRev q).length % 2 = 0 := by
    rw [FreeGroup.invRev_length]
    exact heven
  have hInt : (FreeGroup.invRev q).length < 2 * A.length := by
    rw [FreeGroup.invRev_length]
    exact hint
  have hobs := beginAp_interior_obstruction A (FreeGroup.invRev q) hA hred' hbeg hEv hInt
  -- hobs : ¬ EndsWithWord (invRev A) (secondHalf (invRev q))
  apply hobs
  rw [secondHalf_invRev_of_even q heven]
  exact begins_imp_invRev_ends A (firstHalf q) hB

end Submission.Nielsen
