/-
# The product splitting of a level-`(m+1)` tuple along a binary word

For a binary word `w : Word (m+1)` (which of the `m+1` covariant derivative directions is applied
to the first factor of the product of two packed operators of arities `K₁`, `K₂`), the level-`(m+1)`
tuple `φ : Fin (K₁+K₂+(m+1)) → ℝ` splits as the product over the `A`-tuple of `w` (`K₁ + wCntT w`
entries, at the positions `wPosA K₁ K₂ m w r`, `r < K₁ + wCntT w`) times the product over its
`B`-tuple (`K₂ + wCntF w` entries, at the positions `wPosB K₁ K₂ m w q`, `q < K₂ + wCntF w`):

  `prodSplitWPos`.

This is the multiplicative form of the shuffle splitting, i.e. the combinatorial content of the
Leibniz rule for the *product* `mulOp A B` of two packed operators: the entries of the level-`(m+1)`
tuple are split between the two factors without repetition or omission.

The proof is an application of the generic splitting lemma `wProd_split` of
`Submission.Work.Diff.EXT.evolX.mulOpJetsPos` once the position maps are known to be injective and
disjoint:

* `wPA K₁ K₂ (m+1) w = fun r => wPosA K₁ K₂ m w r.val` is injective — this is
  `wTupUpdateA_wPosA_inj` (`Submission.Work.Diff.EXT.evolX.wTupUpdateA`), the strict monotonicity of
  the position map `wPosA` in its index;
* `wPB K₁ K₂ (m+1) w = fun q => wPosB K₁ K₂ m w q.val` is injective — proved here from the strict
  monotonicity of `wPosB` (`wPosB_val_lt` below), which is the exact analogue of the `A`-case and is
  proved by the same recursion;
* the two position maps take disjoint values — this is `wPosA_ne_wPosB_of_lt`
  (`Submission.Work.Diff.EXT.evolX.wTupUntouchedA`).

Consequently the two blocks cover the whole of `Fin (K₁+K₂+(m+1))` (their cardinalities add up to
the cardinality of the whole by `wCntT_add_wCntF`), which is what the product splitting expresses.
-/
import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs
import Submission.Work.Diff.EXT.evolX.mulOpJetsPos
import Submission.Work.Diff.EXT.evolX.wTupUntouchedA
import Submission.Work.Diff.EXT.evolX.wTupUpdateA

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

/-! ## The `B`-position map is strictly increasing, hence injective -/

private theorem wCntF_word_zero (u : Word 0) : wCntF u = 0 := by
  cases u with
  | nil => rfl

/-- Level `0`, word `cons true u` (the unique direction is routed to `A`): the `B`-slots start after
the `A`-slot, and increase with the index. -/
private theorem wPosB_zero_cons_true_val (K₁ K₂ : ℕ) (u : Word 0) (r : ℕ) :
    (wPosB K₁ K₂ 0 (Word.cons true u) r).val = min (K₁ + 1 + r) (K₁ + K₂) := by
  rw [wPosB_zero_cons_true]

/-- Level `0`, word `cons false u`, index `0`: the newest direction is routed to `B`, so it occupies
position `0`. -/
private theorem wPosB_zero_cons_false_val_zero (K₁ K₂ : ℕ) (u : Word 0) :
    (wPosB K₁ K₂ 0 (Word.cons false u) 0).val = 0 := by
  rw [wPosB_cons_false_zero]

/-- Level `0`, word `cons false u`, positive index: the `B`-slot sits at `K₁ + r`. -/
private theorem wPosB_zero_cons_false_val_succ (K₁ K₂ : ℕ) (u : Word 0) (r : ℕ) :
    (wPosB K₁ K₂ 0 (Word.cons false u) (r + 1)).val = min (K₁ + (r + 1)) (K₁ + K₂) := by
  rw [wPosB_zero_cons_false]
  rw [if_neg (by omega : ¬ (r + 1 = 0))]

/-- **The `B`-position map is strictly increasing** on its range: the `r`-th `B`-entry of the
level-`(n+1)` tuple sits strictly below the `s`-th one whenever `r < s`.  Proved by the recursion
defining `wPosB`; this is the exact `B`-analogue of `wTupUpdateA_wPosA_val_lt`. -/
private theorem wPosB_val_lt : ∀ (n : ℕ) (w : Word (n + 1)) (K₁ K₂ r s : ℕ),
    r < s → s < K₂ + wCntF w → (wPosB K₁ K₂ n w r).val < (wPosB K₁ K₂ n w s).val
  | 0, Word.cons true u, K₁, K₂, r, s, hrs, hs => by
      rw [wCntF_cons_true, wCntF_word_zero, Nat.add_zero] at hs
      rw [wPosB_zero_cons_true_val K₁ K₂ u r, wPosB_zero_cons_true_val K₁ K₂ u s]
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
      omega
  | 0, Word.cons false u, K₁, K₂, r, s, hrs, hs => by
      rw [wCntF_cons_false, wCntF_word_zero] at hs
      rcases r with _ | r'
      · rcases s with _ | s'
        · omega
        · rw [wPosB_zero_cons_false_val_zero K₁ K₂ u,
            wPosB_zero_cons_false_val_succ K₁ K₂ u s']
          rw [Nat.min_eq_left (by omega)]
          omega
      · rcases s with _ | s'
        · omega
        · rw [wPosB_zero_cons_false_val_succ K₁ K₂ u r',
            wPosB_zero_cons_false_val_succ K₁ K₂ u s']
          rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
          omega
  | n + 1, Word.cons true u, K₁, K₂, r, s, hrs, hs => by
      rw [wCntF_cons_true] at hs
      rw [wPosB_cons_true, wPosB_cons_true]
      simp only [Fin.val_succ]
      have h := wPosB_val_lt n u K₁ K₂ r s hrs hs
      omega
  | n + 1, Word.cons false u, K₁, K₂, r, s, hrs, hs => by
      rw [wCntF_cons_false] at hs
      rcases r with _ | r'
      · rw [wPosB_cons_false_zero]
        rcases s with _ | s'
        · omega
        · rw [wPosB_cons_false_succ]
          simp only [Fin.val_succ]
          omega
      · rcases s with _ | s'
        · omega
        · rw [wPosB_cons_false_succ, wPosB_cons_false_succ]
          simp only [Fin.val_succ]
          have h := wPosB_val_lt n u K₁ K₂ r' s' (by omega) (by omega)
          omega

/-- **Injectivity of the `B`-position map** on its range, in the form used below. -/
private theorem wPosB_inj (K₁ K₂ : ℕ) : ∀ (n : ℕ) (w : Word (n + 1)),
    Function.Injective (fun r : Fin (K₂ + wCntF w) => wPosB K₁ K₂ n w r.val) := by
  intro n w r s h
  have h' : wPosB K₁ K₂ n w r.val = wPosB K₁ K₂ n w s.val := h
  apply Fin.ext
  rcases lt_trichotomy r.val s.val with hlt | heq | hgt
  · have hh := wPosB_val_lt n w K₁ K₂ r.val s.val hlt s.isLt
    rw [h'] at hh
    exact absurd hh (lt_irrefl _)
  · exact heq
  · have hh := wPosB_val_lt n w K₁ K₂ s.val r.val hgt r.isLt
    rw [h'] at hh
    exact absurd hh (lt_irrefl _)

/-! ## The product splitting -/

theorem prodSplitWPos (K₁ K₂ m : ℕ) (w : Work.Diff.EXT.evolX.Word (m + 1))
    (φ : Fin (K₁ + K₂ + (m + 1)) → ℝ) :
    Finset.prod Finset.univ (fun r : Fin (K₁ + Work.Diff.EXT.evolX.wCntT w) =>
        φ (Work.Diff.EXT.evolX.wPosA K₁ K₂ m w r.val))
      * Finset.prod Finset.univ (fun r : Fin (K₂ + Work.Diff.EXT.evolX.wCntF w) =>
        φ (Work.Diff.EXT.evolX.wPosB K₁ K₂ m w r.val))
      = Finset.prod Finset.univ (fun r : Fin (K₁ + K₂ + (m + 1)) => φ r) := by
  -- the `A`-positions are injective on their range
  have hA : Function.Injective (wPA K₁ K₂ (m + 1) w) := by
    intro r s hrs
    exact Fin.ext (wTupUpdateA_wPosA_inj m w K₁ K₂ r.isLt s.isLt hrs)
  -- the `B`-positions are injective on their range
  have hB : Function.Injective (wPB K₁ K₂ (m + 1) w) := wPosB_inj K₁ K₂ m w
  -- and the two blocks are disjoint
  have hd : ∀ r q, wPA K₁ K₂ (m + 1) w r ≠ wPB K₁ K₂ (m + 1) w q := by
    intro r q
    exact wPosA_ne_wPosB_of_lt K₁ K₂ m w r.val q.val r.isLt q.isLt
  exact (wProd_split (K₁ := K₁) (K₂ := K₂) (j := m + 1) w φ hA hB hd).symm

end Work.Diff.EXT.evolX
