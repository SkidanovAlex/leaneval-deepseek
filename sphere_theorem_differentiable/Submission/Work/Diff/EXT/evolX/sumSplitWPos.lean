/-
# The sum over the full tuple splits according to the word

This module proves `Work.Diff.EXT.evolX.sumSplitWPos`: the sum of a function `Φ` over the full
level-`(m+1)` index set `Fin (K₁ + K₂ + (m + 1))` equals the sum over the `A`-part (indexed by
`Fin (K₁ + wCntT w)`, positions `wPosA`) plus the sum over the `B`-part (indexed by
`Fin (K₂ + wCntF w)`, positions `wPosB`).

The positions `wPosA`/`wPosB` are defined by recursion on the word (peeling the newest direction),
so the proof is an induction on `m`, peeling the constructor `Word.cons b w'` of the word:

* `Word.cons true w'` — the newest direction goes to the `A`-tuple (as its *first* entry), so the
  `A`-sum acquires `Φ 0` as an extra first term and the `B`-sum is shifted by `Fin.succ`;
* `Word.cons false w'` — symmetrically, the `B`-sum acquires the extra term.

The base case `m = 0` (words of length `1`) is the only place where the raw index set
`Fin (K₁ + K₂ + 1)` has to be decomposed into the derivative direction plus the `K₁ + K₂` tensor
slots; there the sums are split with `Fin.sum_univ_succ` and `Fin.sum_univ_add` and the summands
are matched by `Fin.ext`.

Note: the four recursion lemmas `…_cons_true/false` are stated at level `n+1` for a word
`Word.cons b w` with `w : Word (n+1)`; the equations relating the positions across the peeling
hold *definitionally* (the definitions of `wPosA`/`wPosB` pattern match on the word), which is why
the `show`-based statements below are closed by `rw`/`rfl`.
-/
import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

variable {A : Type*} [AddCommMonoid A]

/-! ## Peeling the newest direction (level `n+1`, word `Word.cons b w`, `w : Word (n+1)`) -/

/-- `A`-sum for `Word.cons true w`: the new direction is the first entry of the `A`-tuple. -/
theorem sumSplitWPos_wPosA_cons_true (K₁ K₂ n : ℕ) (w : Word (n+1))
    (Φ : Fin (K₁+K₂+(n+2)) → A) :
    (∑ r : Fin (K₁ + wCntT (Word.cons true w)), Φ (wPosA K₁ K₂ (n+1) (Word.cons true w) r.val))
      = Φ (wPosA K₁ K₂ (n+1) (Word.cons true w) 0)
        + ∑ r : Fin (K₁ + wCntT w), Φ ((wPosA K₁ K₂ n w r.val).succ) := by
  show (∑ r : Fin ((K₁ + wCntT w) + 1), Φ (wPosA K₁ K₂ (n+1) (Word.cons true w) r.val))
      = Φ (wPosA K₁ K₂ (n+1) (Word.cons true w) 0)
        + ∑ r : Fin (K₁ + wCntT w), Φ ((wPosA K₁ K₂ n w r.val).succ)
  rw [Fin.sum_univ_succ]
  rfl

/-- `A`-sum for `Word.cons false w`: the `A`-tuple is shifted by one. -/
theorem sumSplitWPos_wPosA_cons_false (K₁ K₂ n : ℕ) (w : Word (n+1))
    (Φ : Fin (K₁+K₂+(n+2)) → A) :
    (∑ r : Fin (K₁ + wCntT (Word.cons false w)), Φ (wPosA K₁ K₂ (n+1) (Word.cons false w) r.val))
      = ∑ r : Fin (K₁ + wCntT w), Φ ((wPosA K₁ K₂ n w r.val).succ) := by
  show (∑ r : Fin (K₁ + wCntT w), Φ (wPosA K₁ K₂ (n+1) (Word.cons false w) r.val))
      = ∑ r : Fin (K₁ + wCntT w), Φ ((wPosA K₁ K₂ n w r.val).succ)
  rfl

/-- `B`-sum for `Word.cons true w`: the `B`-tuple is shifted by one. -/
theorem sumSplitWPos_wPosB_cons_true (K₁ K₂ n : ℕ) (w : Word (n+1))
    (Φ : Fin (K₁+K₂+(n+2)) → A) :
    (∑ r : Fin (K₂ + wCntF (Word.cons true w)), Φ (wPosB K₁ K₂ (n+1) (Word.cons true w) r.val))
      = ∑ r : Fin (K₂ + wCntF w), Φ ((wPosB K₁ K₂ n w r.val).succ) := by
  show (∑ r : Fin (K₂ + wCntF w), Φ (wPosB K₁ K₂ (n+1) (Word.cons true w) r.val))
      = ∑ r : Fin (K₂ + wCntF w), Φ ((wPosB K₁ K₂ n w r.val).succ)
  rfl

/-- `B`-sum for `Word.cons false w`: the new direction is the first entry of the `B`-tuple. -/
theorem sumSplitWPos_wPosB_cons_false (K₁ K₂ n : ℕ) (w : Word (n+1))
    (Φ : Fin (K₁+K₂+(n+2)) → A) :
    (∑ r : Fin (K₂ + wCntF (Word.cons false w)), Φ (wPosB K₁ K₂ (n+1) (Word.cons false w) r.val))
      = Φ (wPosB K₁ K₂ (n+1) (Word.cons false w) 0)
        + ∑ r : Fin (K₂ + wCntF w), Φ ((wPosB K₁ K₂ n w r.val).succ) := by
  show (∑ r : Fin ((K₂ + wCntF w) + 1), Φ (wPosB K₁ K₂ (n+1) (Word.cons false w) r.val))
      = Φ (wPosB K₁ K₂ (n+1) (Word.cons false w) 0)
        + ∑ r : Fin (K₂ + wCntF w), Φ ((wPosB K₁ K₂ n w r.val).succ)
  rw [Fin.sum_univ_succ]
  rfl

/-! ## The base case: words of length one

Here the level is `0`, the full index set is `Fin (K₁+K₂+1)`, and the positions are the explicit
ones of the clauses `wPosA K₁ K₂ 0 (Word.cons b _)` / `wPosB K₁ K₂ 0 (Word.cons b _)`. -/

/-- The base case `m = 0` for `Word.cons true Word.nil`. -/
theorem sumSplitWPos_level_zero_true (K₁ K₂ : ℕ) (Φ : Fin (K₁+K₂+1) → A) :
    (∑ σ : Fin (K₁+K₂+1), Φ σ)
      = (∑ r : Fin (K₁ + wCntT (Word.cons true (Word.nil : Word 0))),
            Φ (wPosA K₁ K₂ 0 (Word.cons true Word.nil) r.val))
        + ∑ r : Fin (K₂ + wCntF (Word.cons true (Word.nil : Word 0))),
            Φ (wPosB K₁ K₂ 0 (Word.cons true Word.nil) r.val) := by
  show (∑ σ : Fin (K₁+K₂+1), Φ σ)
      = (∑ r : Fin (K₁+1), Φ (wPosA K₁ K₂ 0 (Word.cons true Word.nil) r.val))
        + ∑ r : Fin K₂, Φ (wPosB K₁ K₂ 0 (Word.cons true Word.nil) r.val)
  have hL : (∑ σ : Fin (K₁+K₂+1), Φ σ) = Φ 0 + ∑ σ : Fin (K₁+K₂), Φ σ.succ := by
    rw [Fin.sum_univ_succ]
  have hII : (∑ σ : Fin (K₁+K₂), Φ σ.succ)
      = (∑ i : Fin K₁, Φ (Fin.castAdd K₂ i).succ) + ∑ j : Fin K₂, Φ (Fin.natAdd K₁ j).succ := by
    rw [Fin.sum_univ_add]
  have hA : (∑ r : Fin (K₁+1), Φ (wPosA K₁ K₂ 0 (Word.cons true Word.nil) r.val))
      = Φ 0 + ∑ i : Fin K₁, Φ (wPosA K₁ K₂ 0 (Word.cons true Word.nil) (Fin.succ i).val) := by
    rw [Fin.sum_univ_succ]
    rfl
  have hA' : (∑ i : Fin K₁, Φ (wPosA K₁ K₂ 0 (Word.cons true Word.nil) (Fin.succ i).val))
      = ∑ i : Fin K₁, Φ (Fin.castAdd K₂ i).succ := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    apply Fin.ext
    show min ((i:ℕ) + 1) (K₁ + K₂) = (i:ℕ) + 1
    rw [Nat.min_eq_left (by omega : (i:ℕ) + 1 ≤ K₁ + K₂)]
  have hB : (∑ r : Fin K₂, Φ (wPosB K₁ K₂ 0 (Word.cons true Word.nil) r.val))
      = ∑ j : Fin K₂, Φ (Fin.natAdd K₁ j).succ := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    apply Fin.ext
    show min (K₁ + 1 + (j:ℕ)) (K₁ + K₂) = K₁ + (j:ℕ) + 1
    rw [Nat.min_eq_left (by omega : K₁ + 1 + (j:ℕ) ≤ K₁ + K₂)]
    omega
  rw [hL, hII, hA, hA', hB]
  abel

/-- The base case `m = 0` for `Word.cons false Word.nil`. -/
theorem sumSplitWPos_level_zero_false (K₁ K₂ : ℕ) (Φ : Fin (K₁+K₂+1) → A) :
    (∑ σ : Fin (K₁+K₂+1), Φ σ)
      = (∑ r : Fin (K₁ + wCntT (Word.cons false (Word.nil : Word 0))),
            Φ (wPosA K₁ K₂ 0 (Word.cons false Word.nil) r.val))
        + ∑ r : Fin (K₂ + wCntF (Word.cons false (Word.nil : Word 0))),
            Φ (wPosB K₁ K₂ 0 (Word.cons false Word.nil) r.val) := by
  show (∑ σ : Fin (K₁+K₂+1), Φ σ)
      = (∑ r : Fin K₁, Φ (wPosA K₁ K₂ 0 (Word.cons false Word.nil) r.val))
        + ∑ r : Fin (K₂+1), Φ (wPosB K₁ K₂ 0 (Word.cons false Word.nil) r.val)
  have hL : (∑ σ : Fin (K₁+K₂+1), Φ σ) = Φ 0 + ∑ σ : Fin (K₁+K₂), Φ σ.succ := by
    rw [Fin.sum_univ_succ]
  have hII : (∑ σ : Fin (K₁+K₂), Φ σ.succ)
      = (∑ i : Fin K₁, Φ (Fin.castAdd K₂ i).succ) + ∑ j : Fin K₂, Φ (Fin.natAdd K₁ j).succ := by
    rw [Fin.sum_univ_add]
  have hA : (∑ r : Fin K₁, Φ (wPosA K₁ K₂ 0 (Word.cons false Word.nil) r.val))
      = ∑ i : Fin K₁, Φ (Fin.castAdd K₂ i).succ := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    apply Fin.ext
    show min ((i:ℕ) + 1) (K₁ + K₂) = (i:ℕ) + 1
    rw [Nat.min_eq_left (by omega : (i:ℕ) + 1 ≤ K₁ + K₂)]
  have hB1 : (∑ r : Fin (K₂+1), Φ (wPosB K₁ K₂ 0 (Word.cons false Word.nil) r.val))
      = Φ 0 + ∑ j : Fin K₂, Φ (wPosB K₁ K₂ 0 (Word.cons false Word.nil) (Fin.succ j).val) := by
    rw [Fin.sum_univ_succ]
    rfl
  have hB2 : (∑ j : Fin K₂, Φ (wPosB K₁ K₂ 0 (Word.cons false Word.nil) (Fin.succ j).val))
      = ∑ j : Fin K₂, Φ (Fin.natAdd K₁ j).succ := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    apply Fin.ext
    show min (K₁ + ((j:ℕ) + 1)) (K₁ + K₂) = K₁ + (j:ℕ) + 1
    rw [Nat.min_eq_left (by omega : K₁ + ((j:ℕ) + 1) ≤ K₁ + K₂)]
    omega
  rw [hL, hII, hA, hB1, hB2]
  abel

/-! ## The target -/

theorem sumSplitWPos {A : Type*} [AddCommMonoid A] (K₁ K₂ m : ℕ)
    (w : Work.Diff.EXT.evolX.Word (m + 1)) (Φ : Fin (K₁ + K₂ + (m + 1)) → A) :
    Finset.sum Finset.univ (fun σ : Fin (K₁ + K₂ + (m + 1)) => Φ σ)
      = Finset.sum Finset.univ (fun r : Fin (K₁ + Work.Diff.EXT.evolX.wCntT w) =>
            Φ (Work.Diff.EXT.evolX.wPosA K₁ K₂ m w r.val))
        + Finset.sum Finset.univ (fun r : Fin (K₂ + Work.Diff.EXT.evolX.wCntF w) =>
            Φ (Work.Diff.EXT.evolX.wPosB K₁ K₂ m w r.val)) := by
  revert w Φ
  induction m with
  | zero =>
    intro w Φ
    cases w with
    | cons b w₀ =>
      cases w₀ with
      | nil =>
        cases b with
        | true => exact sumSplitWPos_level_zero_true K₁ K₂ Φ
        | false => exact sumSplitWPos_level_zero_false K₁ K₂ Φ
  | succ m ih =>
    intro w Φ
    cases w with
    | cons b w' =>
      cases b with
      | true =>
        have hL : (∑ σ : Fin (K₁+K₂+(m+1+1)), Φ σ)
            = Φ (wPosA K₁ K₂ (m+1) (Word.cons true w') 0)
              + ∑ σ : Fin (K₁+K₂+(m+1)), Φ σ.succ := by
          show (∑ σ : Fin ((K₁+K₂+(m+1)) + 1), Φ σ)
              = Φ (wPosA K₁ K₂ (m+1) (Word.cons true w') 0)
                + ∑ σ : Fin (K₁+K₂+(m+1)), Φ σ.succ
          rw [Fin.sum_univ_succ]
          rfl
        have hIH : (∑ σ : Fin (K₁+K₂+(m+1)), Φ σ.succ)
            = (∑ r : Fin (K₁ + wCntT w'), Φ ((wPosA K₁ K₂ m w' r.val).succ))
              + ∑ r : Fin (K₂ + wCntF w'), Φ ((wPosB K₁ K₂ m w' r.val).succ) :=
          ih w' (fun σ => Φ σ.succ)
        have hA := sumSplitWPos_wPosA_cons_true K₁ K₂ m w' Φ
        have hB := sumSplitWPos_wPosB_cons_true K₁ K₂ m w' Φ
        rw [hL, hIH, hA, hB]
        abel
      | false =>
        have hL : (∑ σ : Fin (K₁+K₂+(m+1+1)), Φ σ)
            = Φ (wPosB K₁ K₂ (m+1) (Word.cons false w') 0)
              + ∑ σ : Fin (K₁+K₂+(m+1)), Φ σ.succ := by
          show (∑ σ : Fin ((K₁+K₂+(m+1)) + 1), Φ σ)
              = Φ (wPosB K₁ K₂ (m+1) (Word.cons false w') 0)
                + ∑ σ : Fin (K₁+K₂+(m+1)), Φ σ.succ
          rw [Fin.sum_univ_succ]
          rfl
        have hIH : (∑ σ : Fin (K₁+K₂+(m+1)), Φ σ.succ)
            = (∑ r : Fin (K₁ + wCntT w'), Φ ((wPosA K₁ K₂ m w' r.val).succ))
              + ∑ r : Fin (K₂ + wCntF w'), Φ ((wPosB K₁ K₂ m w' r.val).succ) :=
          ih w' (fun σ => Φ σ.succ)
        have hA := sumSplitWPos_wPosA_cons_false K₁ K₂ m w' Φ
        have hB := sumSplitWPos_wPosB_cons_false K₁ K₂ m w' Φ
        rw [hL, hIH, hA, hB]
        abel

end Work.Diff.EXT.evolX
