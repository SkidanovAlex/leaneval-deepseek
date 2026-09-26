import Submission.Work.T3BalancedReduce

open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# T3 (tuple level): the classical combination moves and their `N`-effect

The classical rebalancing of a balanced system element `α_p = A_p·B_p`
(`|A_p| = |B_p|`, halves) replaces a further element `α_q` by a combination
with `α_p` whenever `α_q`'s reduced word *ends with* `B_p` (then
`α_q ↦ α_q · α_p⁻¹`, so the suffix `B_p` gives way to `A_p⁻¹`) or *begins
with* `B_p⁻¹` (then `α_q ↦ α_p · α_q`, so the prefix `B_p⁻¹` gives way to
`A_p`).  This module records those moves at the level of an automorphism `α`
with basis images `w_i := α(a_i)`: each move is right composition by a single
elementary generator (`rhoNeg q p`, respectively `lam q p`), so it stays in
`closure(AutGen n)`; the word of the changed coordinate is described exactly;
and the total length `N` does not increase (`|A_p| = |B_p|` keeps the count
in balance).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

variable {n : ℕ}

/-! ## Group-level replacement bounds (pure word facts over `FreeGroup (Fin n)`) -/

/-- **Ends-with-`B` replacement is length non-increasing.**  If `x`'s word
ends with `B` and `y`'s word splits as `A ++ B` with `|A| = |B|`, then the
word of `x · y⁻¹` is `reduce (Y ++ invRev A)` — the `B`-suffix is replaced by
`invRev A` — and its length does not exceed that of `x`. -/
lemma norm_mul_inv_end_le (x y : FreeGroup (Fin n)) (A B Y : List (Fin n × Bool))
    (hAB : A.length = B.length)
    (hx : x.toWord = Y ++ B) (hy : y.toWord = A ++ B) :
    FreeGroup.norm (x * y⁻¹) ≤ FreeGroup.norm x := by
  calc
    FreeGroup.norm (x * y⁻¹) = (x * y⁻¹).toWord.length := rfl
    _ = (FreeGroup.reduce (x.toWord ++ y⁻¹.toWord)).length := by
        rw [FreeGroup.toWord_mul]
    _ = (FreeGroup.reduce (x.toWord ++ FreeGroup.invRev y.toWord)).length := by
        rw [FreeGroup.toWord_inv]
    _ = (FreeGroup.reduce ((Y ++ B) ++ FreeGroup.invRev (A ++ B))).length := by
        rw [hx, hy]
    _ = (FreeGroup.reduce ((Y ++ B) ++ (FreeGroup.invRev B ++ FreeGroup.invRev A))).length := by
        rw [FreeGroup.invRev_append]
    _ = (FreeGroup.reduce (Y ++ FreeGroup.invRev A)).length := by
        rw [rebalance_join_reduce (A := A) (B := B) (y := Y)]
    _ ≤ (Y ++ FreeGroup.invRev A).length := reduce_length_le _
    _ = Y.length + A.length := by rw [List.length_append, FreeGroup.invRev_length]
    _ = Y.length + B.length := by rw [hAB]
    _ = (Y ++ B).length := by rw [List.length_append]
    _ = x.toWord.length := by rw [hx]
    _ = FreeGroup.norm x := rfl

/-- **Begins-with-`B⁻¹` replacement is length non-increasing.**  If `x`'s word
begins with `invRev B` and `y`'s word splits as `A ++ B` with `|A| = |B|`,
then the word of `y · x` is `reduce (A ++ Y)` — the prefix `invRev B` is
replaced by `A` — and its length does not exceed that of `x`. -/
lemma norm_mul_begin_le (x y : FreeGroup (Fin n)) (A B Y : List (Fin n × Bool))
    (hAB : A.length = B.length)
    (hx : x.toWord = FreeGroup.invRev B ++ Y) (hy : y.toWord = A ++ B) :
    FreeGroup.norm (y * x) ≤ FreeGroup.norm x := by
  calc
    FreeGroup.norm (y * x) = (y * x).toWord.length := rfl
    _ = (FreeGroup.reduce (y.toWord ++ x.toWord)).length := by
        rw [FreeGroup.toWord_mul]
    _ = (FreeGroup.reduce ((A ++ B) ++ (FreeGroup.invRev B ++ Y))).length := by
        rw [hy, hx]
    _ = (FreeGroup.reduce (A ++ ((B ++ FreeGroup.invRev B) ++ Y))).length := by
        rw [show (A ++ B) ++ (FreeGroup.invRev B ++ Y) =
            A ++ ((B ++ FreeGroup.invRev B) ++ Y) by simp [List.append_assoc]]
    _ = (FreeGroup.reduce (A ++ Y)).length := by
        rw [reduce_middle_empty (X := A) (M := B ++ FreeGroup.invRev B) (Z := Y)
          (reduce_append_invRev_self B)]
    _ ≤ (A ++ Y).length := reduce_length_le _
    _ = A.length + Y.length := by rw [List.length_append]
    _ = B.length + Y.length := by rw [hAB]
    _ = (FreeGroup.invRev B ++ Y).length := by rw [List.length_append, FreeGroup.invRev_length]
    _ = x.toWord.length := by rw [hx]
    _ = FreeGroup.norm x := rfl

/-! ## The tuple moves realised as right composition with an elementary move -/

/-- **Ends-with-`B` move, image word.**  If the word of the `q`-th image ends
with `B` and the word of the `p`-th image splits as `A ++ B`, then after right
composition by `rhoNeg q p` the `q`-th image has word `reduce (Y ++ invRev A)`:
the `B`-suffix is replaced by `invRev A` ("`A_p⁻¹` tritt an die Stelle"). -/
lemma rebalance_image_word (α : MulAut (FreeGroup (Fin n)))
    {p q : Fin n} (hqp : q ≠ p) (A B Y : List (Fin n × Bool))
    (hq : (α (FreeGroup.of q)).toWord = Y ++ B)
    (hp : (α (FreeGroup.of p)).toWord = A ++ B) :
    ((α * rhoNeg q p hqp) (FreeGroup.of q)).toWord =
      FreeGroup.reduce (Y ++ FreeGroup.invRev A) := by
  have hw : (α * rhoNeg q p hqp) (FreeGroup.of q) =
      (α (FreeGroup.of q)) * (α (FreeGroup.of p))⁻¹ := by
    simpa using (mul_rhoNeg_apply_self α q p hqp)
  rw [hw]
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_inv]
  rw [hq, hp]
  rw [FreeGroup.invRev_append]
  exact rebalance_join_reduce (A := A) (B := B) (y := Y)

/-- **Begins-with-`B⁻¹` move, image word.**  If the word of the `q`-th image
begins with `invRev B` and the word of the `p`-th image splits as `A ++ B`,
then after right composition by `lam q p` the `q`-th image has word
`reduce (A ++ Y)`: the prefix `invRev B` is replaced by `A` ("`A_p` tritt an
die Stelle"). -/
lemma rebalance_image_word_left (α : MulAut (FreeGroup (Fin n)))
    {p q : Fin n} (hqp : q ≠ p) (A B Y : List (Fin n × Bool))
    (hq : (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y)
    (hp : (α (FreeGroup.of p)).toWord = A ++ B) :
    ((α * lam q p hqp) (FreeGroup.of q)).toWord =
      FreeGroup.reduce (A ++ Y) := by
  have hw : (α * lam q p hqp) (FreeGroup.of q) =
      (α (FreeGroup.of p)) * (α (FreeGroup.of q)) := by
    simpa using (mul_lam_apply_self α q p hqp)
  rw [hw]
  rw [FreeGroup.toWord_mul]
  rw [hp, hq]
  rw [show (A ++ B) ++ (FreeGroup.invRev B ++ Y) =
      A ++ ((B ++ FreeGroup.invRev B) ++ Y) by simp [List.append_assoc]]
  rw [reduce_middle_empty (X := A) (M := B ++ FreeGroup.invRev B) (Z := Y)
    (reduce_append_invRev_self B)]

/-! ## `N`-effects of the moves -/

/-- The total length `N` never increases under the ends-with-`B` rebalancing
move `w_q ↦ w_q · w_p⁻¹` (right composition by `rhoNeg q p`). -/
theorem rebalance_move_N_le (α : MulAut (FreeGroup (Fin n)))
    {p q : Fin n} (hqp : q ≠ p) (A B Y : List (Fin n × Bool))
    (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = Y ++ B)
    (hp : (α (FreeGroup.of p)).toWord = A ++ B) :
    N (α * rhoNeg q p hqp) ≤ N α := by
  have hN := N_mul_rhoNeg α q p hqp
  have hL := norm_mul_inv_end_le (x := α (FreeGroup.of q)) (y := α (FreeGroup.of p))
    A B Y hAB hq hp
  have hqN : FreeGroup.norm (α (FreeGroup.of q)) ≤ N α := by
    rw [N_eq_sum]
    have hs : (∑ k : Fin n, FreeGroup.norm (α (FreeGroup.of k))) =
        (∑ k ∈ (Finset.univ.erase q : Finset (Fin n)),
          FreeGroup.norm (α (FreeGroup.of k)))
          + FreeGroup.norm (α (FreeGroup.of q)) := by
      exact (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
        (fun k : Fin n => FreeGroup.norm (α (FreeGroup.of k))) (Finset.mem_univ q)).symm
    rw [hs]
    omega
  rw [hN]
  omega

/-- The total length `N` never increases under the begins-with-`B⁻¹`
rebalancing move `w_q ↦ w_p · w_q` (right composition by `lam q p`). -/
theorem rebalance_move_N_le_left (α : MulAut (FreeGroup (Fin n)))
    {p q : Fin n} (hqp : q ≠ p) (A B Y : List (Fin n × Bool))
    (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y)
    (hp : (α (FreeGroup.of p)).toWord = A ++ B) :
    N (α * lam q p hqp) ≤ N α := by
  have hN := N_mul_lam α q p hqp
  have hL := norm_mul_begin_le (x := α (FreeGroup.of q)) (y := α (FreeGroup.of p))
    A B Y hAB hq hp
  have hqN : FreeGroup.norm (α (FreeGroup.of q)) ≤ N α := by
    rw [N_eq_sum]
    have hs : (∑ k : Fin n, FreeGroup.norm (α (FreeGroup.of k))) =
        (∑ k ∈ (Finset.univ.erase q : Finset (Fin n)),
          FreeGroup.norm (α (FreeGroup.of k)))
          + FreeGroup.norm (α (FreeGroup.of q)) := by
      exact (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
        (fun k : Fin n => FreeGroup.norm (α (FreeGroup.of k))) (Finset.mem_univ q)).symm
    rw [hs]
    omega
  rw [hN]
  omega

/-! ## Strict variants: boundary cancellation makes the move shorten -/

/-- The word of `x · y⁻¹` under the ends-with-`B` hypothesis is exactly
`reduce (Y ++ invRev A)`. -/
lemma mul_inv_end_toWord (x y : FreeGroup (Fin n)) (A B Y : List (Fin n × Bool))
    (hx : x.toWord = Y ++ B) (hy : y.toWord = A ++ B) :
    (x * y⁻¹).toWord = FreeGroup.reduce (Y ++ FreeGroup.invRev A) := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_inv, hx, hy]
  rw [FreeGroup.invRev_append]
  exact rebalance_join_reduce (A := A) (B := B) (y := Y)

/-- The word of `y · x` under the begins-with-`B⁻¹` hypothesis is exactly
`reduce (A ++ Y)`. -/
lemma mul_begin_toWord (x y : FreeGroup (Fin n)) (A B Y : List (Fin n × Bool))
    (hx : x.toWord = FreeGroup.invRev B ++ Y) (hy : y.toWord = A ++ B) :
    (y * x).toWord = FreeGroup.reduce (A ++ Y) := by
  rw [FreeGroup.toWord_mul, hy, hx]
  rw [show (A ++ B) ++ (FreeGroup.invRev B ++ Y) =
      A ++ ((B ++ FreeGroup.invRev B) ++ Y) by simp [List.append_assoc]]
  rw [reduce_middle_empty (X := A) (M := B ++ FreeGroup.invRev B) (Z := Y)
    (reduce_append_invRev_self B)]

/-- If a boundary cancellation occurs (`align Y (invRev A) > 0`), the
ends-with-`B` replacement is *strictly* shortening: `x · y⁻¹` is shorter than
`x`. -/
lemma norm_mul_inv_end_lt (x y : FreeGroup (Fin n)) (A B Y : List (Fin n × Bool))
    (hAB : A.length = B.length)
    (hx : x.toWord = Y ++ B) (hy : y.toWord = A ++ B)
    (hYred : FreeGroup.IsReduced Y) (hAred : FreeGroup.IsReduced A)
    (hgr : 0 < align Y (FreeGroup.invRev A)) :
    FreeGroup.norm (x * y⁻¹) < FreeGroup.norm x := by
  have hw := mul_inv_end_toWord x y A B Y hx hy
  have hIAred : FreeGroup.IsReduced (FreeGroup.invRev A) := by
    exact FreeGroup.IsReduced.of_reduce_eq (by
      rw [FreeGroup.reduce_invRev, (FreeGroup.isReduced_iff_reduce_eq.mp hAred)])
  have hgr' : 2 * align Y (FreeGroup.invRev A) ≤ Y.length + A.length := by
    have h1 := align_le_length_left Y (FreeGroup.invRev A)
    have h2 := align_le_length_right Y (FreeGroup.invRev A)
    have hL : (FreeGroup.invRev A).length = A.length := FreeGroup.invRev_length
    omega
  calc
    FreeGroup.norm (x * y⁻¹) = (x * y⁻¹).toWord.length := rfl
    _ = (FreeGroup.reduce (Y ++ FreeGroup.invRev A)).length := by rw [hw]
    _ = Y.length + A.length - 2 * align Y (FreeGroup.invRev A) := by
        rw [reduce_append_align Y (FreeGroup.invRev A) hYred hIAred]
        rw [FreeGroup.invRev_length]
    _ < Y.length + B.length := by
      rw [hAB]
      have hYpos : 0 < Y.length := by
        have h := align_le_length_left Y (FreeGroup.invRev A)
        omega
      omega
    _ = (Y ++ B).length := by rw [List.length_append]
    _ = x.toWord.length := by rw [hx]
    _ = FreeGroup.norm x := rfl

/-- Mirror: if a boundary cancellation occurs (`align A Y > 0`), the
begins-with-`B⁻¹` replacement is strictly shortening. -/
lemma norm_mul_begin_lt (x y : FreeGroup (Fin n)) (A B Y : List (Fin n × Bool))
    (hAB : A.length = B.length)
    (hx : x.toWord = FreeGroup.invRev B ++ Y) (hy : y.toWord = A ++ B)
    (hAred : FreeGroup.IsReduced A) (hYred : FreeGroup.IsReduced Y)
    (hgr : 0 < align A Y) :
    FreeGroup.norm (y * x) < FreeGroup.norm x := by
  have hw := mul_begin_toWord x y A B Y hx hy
  have hgr' : 2 * align A Y ≤ A.length + Y.length := by
    have h1 := align_le_length_left A Y
    have h2 := align_le_length_right A Y
    omega
  calc
    FreeGroup.norm (y * x) = (y * x).toWord.length := rfl
    _ = (FreeGroup.reduce (A ++ Y)).length := by rw [hw]
    _ = A.length + Y.length - 2 * align A Y := reduce_append_align A Y hAred hYred
    _ < B.length + Y.length := by
      rw [hAB]
      have hApos : 0 < A.length := by
        have h := align_le_length_left A Y
        omega
      omega
    _ = (FreeGroup.invRev B ++ Y).length := by rw [List.length_append, FreeGroup.invRev_length]
    _ = x.toWord.length := by rw [hx]
    _ = FreeGroup.norm x := rfl

/-- **Strict rebalancing, ends-with-`B`:** if the replacement word is strictly
shorter, the total length strictly decreases. -/
theorem rebalance_move_N_lt (α : MulAut (FreeGroup (Fin n)))
    {p q : Fin n} (hqp : q ≠ p)
    (hshort : FreeGroup.norm ((α (FreeGroup.of q)) * (α (FreeGroup.of p))⁻¹)
      < FreeGroup.norm (α (FreeGroup.of q))) :
    N (α * rhoNeg q p hqp) < N α := by
  have hN := N_mul_rhoNeg α q p hqp
  have hqN : FreeGroup.norm (α (FreeGroup.of q)) ≤ N α := by
    rw [N_eq_sum]
    have hs : (∑ k : Fin n, FreeGroup.norm (α (FreeGroup.of k))) =
        (∑ k ∈ (Finset.univ.erase q : Finset (Fin n)),
          FreeGroup.norm (α (FreeGroup.of k)))
          + FreeGroup.norm (α (FreeGroup.of q)) := by
      exact (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
        (fun k : Fin n => FreeGroup.norm (α (FreeGroup.of k))) (Finset.mem_univ q)).symm
    rw [hs]
    omega
  rw [hN]
  omega

/-- **Strict rebalancing from a boundary cancellation, ends-with-`B`:** an
`align Y (invRev A) > 0` occurrence means more of `w_q`'s word is replaced
than preserved, so `N` strictly decreases. -/
theorem rebalance_move_N_lt_of_align (α : MulAut (FreeGroup (Fin n)))
    {p q : Fin n} (hqp : q ≠ p) (A B Y : List (Fin n × Bool))
    (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = Y ++ B)
    (hp : (α (FreeGroup.of p)).toWord = A ++ B)
    (hYred : FreeGroup.IsReduced Y) (hAred : FreeGroup.IsReduced A)
    (hgr : 0 < align Y (FreeGroup.invRev A)) :
    N (α * rhoNeg q p hqp) < N α := by
  have hshort := norm_mul_inv_end_lt (x := α (FreeGroup.of q)) (y := α (FreeGroup.of p))
    A B Y hAB hq hp hYred hAred hgr
  exact rebalance_move_N_lt α hqp hshort

end Submission.Nielsen
