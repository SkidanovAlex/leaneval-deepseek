import Mathlib.GroupTheory.FreeGroup.Reduce
import Submission.Commons.GroupTheory.FreeGroup.reduce_append_no_junction

set_option autoImplicit false

/-!
# Alignment of two reduced words (cancellation count)

When two reduced words are multiplied, cancellation can only occur across the
seam `toWord u ++ toWord v`: the last letters of `toWord u` cancel against the
first letters of `toWord v` while they are letter-inverses.  This file defines
the *alignment length*

    align L M := commonPrefixLen (letterInv ∘ reverse L) M

i.e. the number of seam-letter pairs that cancel when concatenating the reduced
words `L` and `M`.  Quantitative identity aimed at (statement to prove next):

    length (FreeGroup.reduce (L ++ M)) = L.length + M.length − 2·align L M

so that for basis images `u, v` (`L := toWord u`, `M := toWord v`),
`|u·v| < |u|` iff strictly more than half of `v` cancels
(`2·align L M > M.length`).  This is the quantitative ingredient of the
residual ("no end cancellation") analysis of `double_coset_shortens`; see
`NielsenReductionBlueprint.lean`.  Proved here (unconditional, Commons-grade:
Mathlib-only, namespace `Commons.GroupTheory.FreeGroup`): the elementary facts
about `align` (nil/bounds), the recursion lemma `commonPrefixLen_cons`, the
`cons`-recurrence of alignment `align_cons_of_append`, and the one-step
cancellation lemma `reduce_append_step_cancel` (via `Red.Step.not`).  The
**ALL PROVED, kernel-checked**: the quantitative identity
`reduce_append_align` — `length (reduce (L ++ M)) = |L| + |M| − 2·align L M`
for reduced `L`, `M` (induction on `M`; matching case
`reduce_append_align_cons_match`, non-matching case
`reduce_append_align_cons_nomatch`, via `reduce_append_no_junction`,
`reduce_append_step_cancel`, `align_cons_of_append`, `getLast?_append_singleton`,
and `List.IsChain.take`/`drop` for the reduced prefix/tail premises) — and its
consequence the **shortening criterion** `norm_mul_lt_iff`:

    |u·v| < |u|  ⟺  2·align (toWord u) (toWord v) > (toWord v).length

i.e. multiplying `v` onto `u` shortens `u` iff strictly more than half of `v`
cancels against the tail of `u`.  Axioms `[propext, Classical.choice,
Quot.sound]`.
-/

namespace Commons.GroupTheory.FreeGroup

/-- Letter-inverse: the inverse of the letter `(a, b)` is `(a, !b)`. -/
def letterInv {α : Type*} (l : α × Bool) : α × Bool := (l.1, !l.2)

/-- Letter inversion is an involution. -/
lemma letterInv_self {α : Type*} (l : α × Bool) : letterInv (letterInv l) = l := by
  cases l with
  | mk a b => cases b <;> simp [letterInv]

/-- The common prefix length of two lists. -/
def commonPrefixLen {α : Type*} [DecidableEq α] : List α → List α → ℕ
  | a :: t, b :: u => if a = b then commonPrefixLen t u + 1 else 0
  | _, _ => 0

/-- The common prefix length is bounded by the length of either argument. -/
lemma commonPrefixLen_le_right {α : Type*} [DecidableEq α] (X Y : List α) :
    commonPrefixLen X Y ≤ Y.length := by
  induction Y generalizing X with
  | nil => simp [commonPrefixLen]
  | cons a t ih =>
      cases X with
      | nil => simp [commonPrefixLen]
      | cons b s =>
          by_cases h : b = a
          · simp [commonPrefixLen, h]
            have hrec := ih s
            omega
          · simp [commonPrefixLen, h]

/-- The common prefix length is bounded by the length of either argument. -/
lemma commonPrefixLen_le_left {α : Type*} [DecidableEq α] (X Y : List α) :
    commonPrefixLen X Y ≤ X.length := by
  induction X generalizing Y with
  | nil => simp [commonPrefixLen]
  | cons b s ih =>
      cases Y with
      | nil => simp [commonPrefixLen]
      | cons a t =>
          by_cases h : b = a
          · simp [commonPrefixLen, h]
            have hrec := ih t
            omega
          · simp [commonPrefixLen, h]

/-- Alignment of a reduced word `M` against the tail of a reduced word `L`:
the number `k` of consecutive pairs `(L[|L|-1-t], M[t])` that are
letter-inverses, `t = 0, …, k-1` — exactly the letters that cancel in
`L ++ M`. -/
def align {α : Type*} [DecidableEq α] (L M : List (α × Bool)) : ℕ :=
  commonPrefixLen (L.reverse.map letterInv) M

/-- Aligning against the empty word is trivial. -/
lemma align_nil_right {α : Type*} [DecidableEq α] (L : List (α × Bool)) :
    align L [] = 0 := by
  unfold align commonPrefixLen
  cases L.reverse.map letterInv with
  | nil => rfl
  | cons a t => rfl

/-- Aligning the empty word is trivial. -/
lemma align_nil_left {α : Type*} [DecidableEq α] (M : List (α × Bool)) :
    align [] M = 0 := by
  unfold align
  simp [commonPrefixLen]

/-- Alignment is bounded by the length of the second word. -/
lemma align_le_length_right {α : Type*} [DecidableEq α] (L M : List (α × Bool)) :
    align L M ≤ M.length := by
  unfold align
  exact commonPrefixLen_le_right (L.reverse.map letterInv) M

/-- Alignment is bounded by the length of the first word. -/
lemma align_le_length_left {α : Type*} [DecidableEq α] (L M : List (α × Bool)) :
    align L M ≤ L.length := by
  unfold align
  have hle := commonPrefixLen_le_left (L.reverse.map letterInv) M
  calc
    commonPrefixLen (L.reverse.map letterInv) M ≤ (L.reverse.map letterInv).length := hle
    _ = L.length := by simp

lemma commonPrefixLen_cons {α : Type*} [DecidableEq α] (a b : α) (X Y : List α) :
    commonPrefixLen (a :: X) (b :: Y) =
      if a = b then commonPrefixLen X Y + 1 else 0 := by
  rfl

/-- Alignment after a `cons` on the second word, expressed on the first word
decomposed as `L₀ ++ [x]`: if the head `w` of the second word cancels the last
letter `x` of the first, alignment continues on the tails plus one; otherwise
it is zero. -/
lemma align_cons_of_append {α : Type*} [DecidableEq α] (L0 : List (α × Bool))
    (x w : α × Bool) (M0 : List (α × Bool)) :
    align (L0 ++ [x]) (w :: M0) =
      if letterInv x = w then align L0 M0 + 1 else 0 := by
  unfold align
  rw [List.reverse_append, List.reverse_singleton]
  rw [List.map_append, List.map_singleton]
  simp only [List.cons_append, List.nil_append]
  rw [commonPrefixLen_cons]

/-- One-step cancellation: if the head `letterInv x` of the second word cancels
the last letter `x` of the first word, reducing the concatenation removes
exactly that pair. -/
lemma reduce_append_step_cancel {α : Type*} [DecidableEq α]
    (L0 : List (α × Bool)) (x : α × Bool) (M0 : List (α × Bool)) :
    FreeGroup.reduce ((L0 ++ [x]) ++ (letterInv x :: M0)) =
      FreeGroup.reduce (L0 ++ M0) := by
  have hred : FreeGroup.Red ((L0 ++ [x]) ++ (letterInv x :: M0)) (L0 ++ M0) := by
    have hstep : FreeGroup.Red.Step ((L0 ++ [x]) ++ (letterInv x :: M0)) (L0 ++ M0) := by
      rcases x with ⟨a, b⟩
      have hx : letterInv (a, b) = (a, !b) := by simp [letterInv]
      rw [hx]
      rw [List.append_assoc]
      exact (FreeGroup.Red.Step.not (L₁ := L0) (L₂ := M0) (x := a) (b := b))
    exact hstep.to_red
  exact FreeGroup.reduce.eq_of_red hred
/-- **Matching case of the alignment identity (standalone).**  If the head `w`
of the second word cancels the last letter `x` of the first (`letterInv x = w`),
then the one-step cancellation `reduce_append_step_cancel` gives the identity
for the concatenation in terms of the tails. -/
theorem reduce_append_align_cons_match {α : Type*} [DecidableEq α]
    (L0 : List (α × Bool)) (x w : α × Bool) (M0 : List (α × Bool))
    (hm : letterInv x = w)
    (ih : (FreeGroup.reduce (L0 ++ M0)).length =
        L0.length + M0.length - 2 * align L0 M0) :
    (FreeGroup.reduce ((L0 ++ [x]) ++ (w :: M0))).length =
      (L0 ++ [x]).length + (w :: M0).length - 2 * align (L0 ++ [x]) (w :: M0) := by
  have hred : FreeGroup.reduce ((L0 ++ [x]) ++ (w :: M0)) = FreeGroup.reduce (L0 ++ M0) := by
    rw [← hm]
    exact reduce_append_step_cancel L0 x M0
  rw [hred]
  rw [ih]
  rw [align_cons_of_append]
  rw [hm]
  simp
  have hkL := align_le_length_left L0 M0
  have hkM := align_le_length_right L0 M0
  omega

/-- The last element of `L₀ ++ [x]` is `x`. -/
lemma getLast?_append_singleton {α : Type*} (L0 : List α) (x : α) :
    (L0 ++ [x]).getLast? = some x := by
  induction L0 with
  | nil => simp
  | cons a t ih =>
      rw [List.cons_append]
      cases t with
      | nil => simp
      | cons b u =>
          change (a :: b :: (u ++ [x])).getLast? = some x
          rw [List.getLast?_cons_cons]
          exact ih

/-- **Non-matching case of the alignment identity (standalone).**  If the head
`w` of the second word does **not** cancel the last letter `x` of the first
(`letterInv x ≠ w`), then the concatenation of the two reduced words is itself
reduced, so no letters cancel and the identity holds with `align = 0`. -/
theorem reduce_append_align_cons_nomatch {α : Type*} [DecidableEq α]
    (L0 : List (α × Bool)) (x w : α × Bool) (M0 : List (α × Bool))
    (hxred : FreeGroup.IsReduced (L0 ++ [x]))
    (hwred : FreeGroup.IsReduced (w :: M0))
    (hnm : letterInv x ≠ w) :
    (FreeGroup.reduce ((L0 ++ [x]) ++ (w :: M0))).length =
      (L0 ++ [x]).length + (w :: M0).length - 2 * align (L0 ++ [x]) (w :: M0) := by
  have hred : FreeGroup.reduce ((L0 ++ [x]) ++ (w :: M0)) = (L0 ++ [x]) ++ (w :: M0) := by
    refine reduce_append_no_junction (X := L0 ++ [x]) (Y := w :: M0) hxred hwred ?_
    intro a b hlast hhead
    have hx : x = (a, b) := by
      have h1 := getLast?_append_singleton L0 x
      rw [h1] at hlast
      exact Option.some.inj hlast
    have hw : w = (a, !b) := by
      simpa using hhead
    apply hnm
    rw [hx, hw]
    simp [letterInv]
  rw [hred]
  rw [align_cons_of_append]
  rw [if_neg hnm]
  simp
  omega

/-- **The quantitative alignment identity.**  For reduced words `L`, `M`, the
concatenation `L ++ M` reduces by removing exactly the `align L M` seam-letter
pairs:

    length (reduce (L ++ M)) = |L| + |M| − 2·align L M
-/
theorem reduce_append_align {α : Type*} [DecidableEq α] (L M : List (α × Bool))
    (hL : FreeGroup.IsReduced L) (hM : FreeGroup.IsReduced M) :
    (FreeGroup.reduce (L ++ M)).length = L.length + M.length - 2 * align L M := by
  induction M generalizing L with
  | nil =>
      have hred : FreeGroup.reduce (L ++ []) = L := by
        simpa using (FreeGroup.IsReduced.reduce_eq hL)
      rw [hred]
      rw [align_nil_right L]
      simp
  | cons w M0 ih =>
      by_cases hLe : L = []
      · subst L
        have hred : FreeGroup.reduce ([] ++ (w :: M0)) = w :: M0 :=
          FreeGroup.IsReduced.reduce_eq hM
        rw [hred]
        rw [align_nil_left (w :: M0)]
        simp
      · set x : α × Bool := L.getLast hLe with hxdef
        have hlast : L.getLast? = some x := by
          rw [hxdef]
          exact List.getLast?_eq_getLast_of_ne_nil hLe
        have hmem : x ∈ L.getLast? := by
          rw [hlast]
          simp
        have hdec : L.dropLast ++ [x] = L := by
          exact List.dropLast_append_getLast? x hmem
        have hxL : FreeGroup.IsReduced (L.dropLast ++ [x]) := by
          simpa [hdec] using hL
        have hM0red : FreeGroup.IsReduced M0 := by
          change List.IsChain (fun a b : α × Bool => a.1 = b.1 → a.2 = b.2) M0
          unfold FreeGroup.IsReduced at hM
          have hd := List.IsChain.drop hM 1
          simpa using hd
        by_cases hm : letterInv x = w
        · have hL0red : FreeGroup.IsReduced L.dropLast := by
            -- L.dropLast = (L.dropLast ++ [x]).take L.dropLast.length
            have hEq : L.dropLast = (L.dropLast ++ [x]).take L.dropLast.length := by
              simp [List.take_append]
            change List.IsChain (fun a b : α × Bool => a.1 = b.1 → a.2 = b.2) L.dropLast
            rw [hEq]
            change List.IsChain (fun a b : α × Bool => a.1 = b.1 → a.2 = b.2)
              ((L.dropLast ++ [x]).take L.dropLast.length)
            unfold FreeGroup.IsReduced at hxL
            exact List.IsChain.take hxL L.dropLast.length
          have ihfull : (FreeGroup.reduce (L.dropLast ++ M0)).length =
              L.dropLast.length + M0.length - 2 * align L.dropLast M0 :=
            ih L.dropLast hL0red hM0red
          have hmm := reduce_append_align_cons_match L.dropLast x w M0 hm ihfull
          rw [← hdec]
          exact hmm
        · have hnm := reduce_append_align_cons_nomatch L.dropLast x w M0 hxL hM hm
          rw [← hdec]
          exact hnm

/-- **The shortening criterion.**  For elements `u`, `v` of the free group,
multiplying `v` onto `u` shortens `u` if and only if strictly more than half of
`v` cancels against the tail of `u`:

    |u·v| < |u|  ⟺  2·align (toWord u) (toWord v) > (toWord v).length
-/
theorem norm_mul_lt_iff {α : Type*} [DecidableEq α] (u v : FreeGroup α) :
    FreeGroup.norm (u * v) < FreeGroup.norm u ↔
      2 * align (FreeGroup.toWord u) (FreeGroup.toWord v) >
        (FreeGroup.toWord v).length := by
  have h1 : FreeGroup.norm (u * v) =
      (FreeGroup.reduce (FreeGroup.toWord u ++ FreeGroup.toWord v)).length := by
    unfold FreeGroup.norm
    rw [FreeGroup.toWord_mul]
  have h2 : FreeGroup.norm u = (FreeGroup.toWord u).length := rfl
  have hid := reduce_append_align (FreeGroup.toWord u) (FreeGroup.toWord v)
    (FreeGroup.isReduced_toWord) (FreeGroup.isReduced_toWord)
  have hkM := align_le_length_right (FreeGroup.toWord u) (FreeGroup.toWord v)
  have hkL := align_le_length_left (FreeGroup.toWord u) (FreeGroup.toWord v)
  rw [h1, h2, hid]
  omega

end Commons.GroupTheory.FreeGroup
