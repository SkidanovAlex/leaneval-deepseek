/-
# The length of the reduction of `W⁻¹ Z`

For reduced words `W` and `Z` in a free group, the reduced form of the concatenation
`invRev W ++ Z` (that is, of the word `W⁻¹ Z`) is obtained by cancelling precisely the
`lcpLen W Z` pairs of letters coming from the common prefix of `W` and `Z`:

`reduce (invRev W ++ Z) = invRev (W.drop k) ++ Z.drop k`, where `k = lcpLen W Z`.

Taking lengths gives the stated identity
`(reduce (invRev W ++ Z)).length + 2 * lcpLen W Z = W.length + Z.length`.

The two ingredients are the combinatorial shape of `reduce` on a concatenation across which
nothing cancels (`FreeGroup.IsReduced.append_overlap`), and the fact that a cancelling pair
`(a, !b)` at the junction disappears in one reduction step (`FreeGroup.Red.Step.not`).
-/
import Mathlib
import Submission.Work.ORLyndon.fgdDefs

set_option autoImplicit false

namespace Work.ORLyndon

/-! ## Elementary helper facts -/

/-- The `invRev` of a reduced word is reduced: `invRev` reverses the word (which preserves
reducedness) and flips every sign (which is a bijection on signs).  Formulated through `reduce`
to avoid a separate induction. -/
private lemma isReduced_invRev_of {α : Type*} [DecidableEq α] {L : List (α × Bool)}
    (h : FreeGroup.IsReduced L) : FreeGroup.IsReduced (FreeGroup.invRev L) := by
  refine FreeGroup.IsReduced.of_reduce_eq ?_
  rw [FreeGroup.reduce_invRev, FreeGroup.IsReduced.reduce_eq h]

/-- The tail of a reduced word is reduced. -/
private lemma isReduced_tail {α : Type*} {a : α × Bool} {L : List (α × Bool)}
    (h : FreeGroup.IsReduced (a :: L)) : FreeGroup.IsReduced L := by
  cases L with
  | nil => exact FreeGroup.IsReduced.nil
  | cons c L => exact (FreeGroup.isReduced_cons_cons.mp h).2

/-- The two-element list `Bool` fact underlying the sign bookkeeping: for booleans, being
different is the same as being the negation of the other. -/
private lemma not_eq_iff_eq_not {a b : Bool} : (a ≠ b) ↔ (!a) = b := by
  cases a <;> cases b <;> simp

/-- If the heads `a` and `b` of two reduced words do not cancel (i.e. the pair
`(a⁻¹, b)` is not a cancelling pair), then `invRev (a :: W') ++ (b :: Z')` is reduced.

Indeed `invRev (a :: W') = invRev W' ++ [invSym a]`, the junction `invSym a | b` does not
cancel, and `append_overlap` glues the three reduced pieces. -/
private lemma isReduced_invRev_cons_append {α : Type*} [DecidableEq α] {a b : α × Bool}
    {W' Z' : List (α × Bool)} (hW : FreeGroup.IsReduced (a :: W'))
    (hZ : FreeGroup.IsReduced (b :: Z')) (hab : a ≠ b) :
    FreeGroup.IsReduced (FreeGroup.invRev (a :: W') ++ (b :: Z')) := by
  have hinv : FreeGroup.invRev [a] = [(a.1, !a.2)] := rfl
  rw [FreeGroup.invRev_cons]
  refine FreeGroup.IsReduced.append_overlap (L₂ := FreeGroup.invRev [a]) ?_ ?_ ?_
  · rw [← FreeGroup.invRev_cons]
    exact isReduced_invRev_of hW
  · rw [hinv, List.singleton_append, FreeGroup.isReduced_cons_cons]
    refine ⟨?_, hZ⟩
    show a.1 = b.1 → (!a.2) = b.2
    intro h1
    exact not_eq_iff_eq_not.mp (fun h2 => hab (Prod.ext h1 h2))
  · rw [hinv]; simp

/-! ## The structure of the reduced word `W⁻¹ Z` -/

/-- For reduced `W` and `Z`, the maximal reduction of `invRev W ++ Z` is the concatenation of
the reverse-inverse of the part of `W` after the common prefix with the part of `Z` after the
common prefix. -/
private theorem reduce_invRev_append_eq {α : Type*} [DecidableEq α] (W : List (α × Bool)) :
    ∀ (Z : List (α × Bool)), FreeGroup.IsReduced W → FreeGroup.IsReduced Z →
      FreeGroup.reduce (FreeGroup.invRev W ++ Z)
        = FreeGroup.invRev (W.drop (lcpLen W Z)) ++ Z.drop (lcpLen W Z) := by
  induction W with
  | nil =>
      intro Z _ hZ
      simp only [FreeGroup.invRev_empty, List.nil_append, lcpLen_nil_left, List.drop_zero,
        FreeGroup.IsReduced.reduce_eq hZ]
  | cons a W' ih =>
      intro Z hW hZ
      cases Z with
      | nil =>
          rw [List.append_nil, lcpLen_nil_right, List.drop_zero, List.drop_zero, List.append_nil]
          exact FreeGroup.IsReduced.reduce_eq (isReduced_invRev_of hW)
      | cons b Z' =>
          have hW' : FreeGroup.IsReduced W' := isReduced_tail hW
          have hZ' : FreeGroup.IsReduced Z' := isReduced_tail hZ
          by_cases hab : a = b
          · -- `a = b`: the two letters at the junction cancel, and we recurse on the tails.
            rw [lcpLen_cons_cons, if_pos hab]
            have hstep : FreeGroup.reduce (FreeGroup.invRev (a :: W') ++ (b :: Z'))
                = FreeGroup.reduce (FreeGroup.invRev W' ++ Z') := by
              apply FreeGroup.reduce.eq_of_red
              have hs : FreeGroup.Red (FreeGroup.invRev W' ++ [(a.1, !a.2)] ++ (b :: Z'))
                  (FreeGroup.invRev W' ++ Z') := by
                have h := (FreeGroup.Red.Step.not (L₁ := FreeGroup.invRev W') (L₂ := Z')
                  (x := a.1) (b := !a.2)).to_red
                rw [hab] at h ⊢
                simpa using h
              simpa [FreeGroup.invRev_cons, FreeGroup.invRev, List.append_assoc] using hs
            rw [hstep, ih Z' hW' hZ']
            have h1 : (a :: W').drop (1 + lcpLen W' Z') = W'.drop (lcpLen W' Z') := by
              rw [Nat.add_comm 1, List.drop_succ_cons]
            have h2 : (b :: Z').drop (1 + lcpLen W' Z') = Z'.drop (lcpLen W' Z') := by
              rw [Nat.add_comm 1, List.drop_succ_cons]
            rw [h1, h2]
          · -- `a ≠ b`: nothing cancels, the long word is already reduced.
            rw [lcpLen_cons_cons, if_neg hab, List.drop_zero, List.drop_zero]
            exact FreeGroup.IsReduced.reduce_eq (isReduced_invRev_cons_append hW hZ hab)

/-! ## Lengths -/

/-- The longest common prefix of two lists is no longer than either list. -/
private lemma lcpLen_le_left {β : Type*} [DecidableEq β] (W Z : List β) :
    lcpLen W Z ≤ W.length := by
  induction W generalizing Z with
  | nil => simp
  | cons a as ih =>
      cases Z with
      | nil => simp
      | cons b bs =>
          rw [lcpLen_cons_cons]
          split_ifs with h
          · have := ih bs; simp only [List.length_cons]; omega
          · exact Nat.zero_le _

/-- The longest common prefix of two lists is no longer than either list. -/
private lemma lcpLen_le_right {β : Type*} [DecidableEq β] (W Z : List β) :
    lcpLen W Z ≤ Z.length := by
  induction W generalizing Z with
  | nil => simp
  | cons a as ih =>
      cases Z with
      | nil => simp
      | cons b bs =>
          rw [lcpLen_cons_cons]
          split_ifs with h
          · have := ih bs; simp only [List.length_cons]; omega
          · exact Nat.zero_le _

theorem reduce_invRev_append_length {α : Type*} [DecidableEq α] {W Z : List (α × Bool)}
    (hW : FreeGroup.IsReduced W) (hZ : FreeGroup.IsReduced Z) :
    (FreeGroup.reduce (FreeGroup.invRev W ++ Z)).length + 2 * lcpLen W Z
      = W.length + Z.length := by
  rw [reduce_invRev_append_eq W Z hW hZ, List.length_append, FreeGroup.invRev_length,
    List.length_drop, List.length_drop]
  have h1 : lcpLen W Z ≤ W.length := lcpLen_le_left W Z
  have h2 : lcpLen W Z ≤ Z.length := lcpLen_le_right W Z
  omega

end Work.ORLyndon
