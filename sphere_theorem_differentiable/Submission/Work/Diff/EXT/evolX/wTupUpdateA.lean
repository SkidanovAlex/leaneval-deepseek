import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

/-!
# Updating one entry of a tuple commutes with taking the `A`-sub-tuple

`wTupUpdateA` is, at heart, the statement that the positions
`wPosA K₁ K₂ m w r`, `r < K₁ + wCntT w`, at which the entries of the `A`-sub-tuple of a word
`w : Word (m+1)` sit in the level-`(m+1)` tuple are **pairwise distinct**: replacing the entry of
`F` at the position `wPosA K₁ K₂ m w ρ.val` and then extracting the `A`-sub-tuple is the same as
extracting the `A`-sub-tuple and then replacing its `ρ`-th entry.

The position map is proved strictly increasing in `r` by the very recursion that defines it.  At
level `0` the `r`-th `A`-entry sits at position `r` (word `… true`) resp. `r + 1` (word
`… false`); at level `n + 1` a direction routed to `A` (a `cons true`) occupies the new position `0`
and pushes everything else up by one (`Fin.succ`), while a direction routed to `B` (a `cons false`)
only pushes up.
-/

/-- `wCntT` of the empty word: the level-`0` base cases of the position recursions are stated with a
word of length one, so only this value of `wCntT` is needed there. -/
theorem wTupUpdateA_wCntT_word_zero (u : Word 0) : wCntT u = 0 := by
  cases u with
  | nil => rfl

/-- At level `0` and with the (unique) length-one word `cons true u`, the `r`-th `A`-entry sits at
position `r`, for `r` in the range `[0, K₁ + wCntT (cons true u))` (i.e. `r ≤ K₁`). -/
theorem wTupUpdateA_wPosA_zero_cons_true (K₁ K₂ : ℕ) (u : Word 0) (r : ℕ)
    (hr : r < K₁ + wCntT (Word.cons true u)) :
    wPosA K₁ K₂ 0 (Word.cons true u) r =
      ⟨r, by rw [wCntT_cons_true, wTupUpdateA_wCntT_word_zero] at hr; omega⟩ := by
  rw [wPosA_zero_cons_true]
  split_ifs with h
  · subst h; rfl
  · congr 1
    rw [wCntT_cons_true, wTupUpdateA_wCntT_word_zero] at hr
    exact Nat.min_eq_left (by omega)

/-- At level `0` and with the word `cons false u`, the `r`-th `A`-entry sits at position `r + 1`
(the newest direction is routed to `B`, so the `A`-slots are shifted by one). -/
theorem wTupUpdateA_wPosA_zero_cons_false (K₁ K₂ : ℕ) (u : Word 0) (r : ℕ)
    (hr : r < K₁ + wCntT (Word.cons false u)) :
    wPosA K₁ K₂ 0 (Word.cons false u) r =
      ⟨r + 1, by rw [wCntT_cons_false, wTupUpdateA_wCntT_word_zero] at hr; omega⟩ := by
  rw [wPosA_zero_cons_false]
  congr 1
  rw [wCntT_cons_false, wTupUpdateA_wCntT_word_zero, Nat.add_zero] at hr
  exact Nat.min_eq_left (by omega)

/-- The `Nat.succ` form of the recursion step for a direction routed to `A` (the library lemma
`wPosA_cons_true_succ` is stated with `r + 1`, which does not match a `Nat.succ`-recursion). -/
theorem wTupUpdateA_wPosA_cons_true_succ (K₁ K₂ n : ℕ) (w : Word (n + 1)) (r : ℕ) :
    wPosA K₁ K₂ (n + 1) (Word.cons true w) (Nat.succ r) = (wPosA K₁ K₂ n w r).succ := by
  rw [wPosA]; simp

/-- **The position map `wPosA` is strictly increasing** on its range: the `r`-th `A`-entry of the
level-`(n+1)` tuple sits strictly below the `s`-th one whenever `r < s`.  Proved by the recursion
defining `wPosA`. -/
theorem wTupUpdateA_wPosA_val_lt : ∀ (n : ℕ) (w : Word (n + 1)) (K₁ K₂ r s : ℕ),
    r < s → s < K₁ + wCntT w → (wPosA K₁ K₂ n w r).val < (wPosA K₁ K₂ n w s).val
  | 0, Word.cons true u, K₁, K₂, r, s, hrs, hs => by
      have hr : r < K₁ + wCntT (Word.cons true u) := by omega
      rw [wTupUpdateA_wPosA_zero_cons_true K₁ K₂ u r hr,
        wTupUpdateA_wPosA_zero_cons_true K₁ K₂ u s hs]
      exact hrs
  | 0, Word.cons false u, K₁, K₂, r, s, hrs, hs => by
      have hr : r < K₁ + wCntT (Word.cons false u) := by omega
      rw [wTupUpdateA_wPosA_zero_cons_false K₁ K₂ u r hr,
        wTupUpdateA_wPosA_zero_cons_false K₁ K₂ u s hs]
      show r + 1 < s + 1
      omega
  | n + 1, Word.cons true u, K₁, K₂, r, s, hrs, hs => by
      rw [wCntT_cons_true] at hs
      rcases r with _ | r'
      · rcases s with _ | s'
        · omega
        · rw [wPosA_cons_true_zero, wTupUpdateA_wPosA_cons_true_succ]
          simp only [Fin.val_succ]
          omega
      · rcases s with _ | s'
        · omega
        · rw [wTupUpdateA_wPosA_cons_true_succ, wTupUpdateA_wPosA_cons_true_succ]
          simp only [Fin.val_succ]
          have h := wTupUpdateA_wPosA_val_lt n u K₁ K₂ r' s' (by omega) (by omega)
          omega
  | n + 1, Word.cons false u, K₁, K₂, r, s, hrs, hs => by
      rw [wCntT_cons_false] at hs
      rw [wPosA_cons_false, wPosA_cons_false]
      simp only [Fin.val_succ]
      have h := wTupUpdateA_wPosA_val_lt n u K₁ K₂ r s hrs hs
      omega

/-- **Injectivity of the position map** on its range, the form in which it is used below. -/
theorem wTupUpdateA_wPosA_inj (n : ℕ) (w : Word (n + 1)) (K₁ K₂ : ℕ) {r s : ℕ}
    (hr : r < K₁ + wCntT w) (hs : s < K₁ + wCntT w)
    (heq : wPosA K₁ K₂ n w r = wPosA K₁ K₂ n w s) : r = s := by
  rcases lt_trichotomy r s with h | h | h
  · have := wTupUpdateA_wPosA_val_lt n w K₁ K₂ r s h hs
    rw [heq] at this
    exact absurd this (lt_irrefl _)
  · exact h
  · have := wTupUpdateA_wPosA_val_lt n w K₁ K₂ s r h hr
    rw [heq] at this
    exact absurd this (lt_irrefl _)

theorem wTupUpdateA
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (K₁ K₂ m : ℕ) (w : Work.Diff.EXT.evolX.Word (m + 1))
    (F : Fin (K₁ + K₂ + (m + 1)) → Work.Diff.EXT.TField (I := I) (M := M))
    (v : Work.Diff.EXT.TField (I := I) (M := M))
    (ρ : Fin (K₁ + Work.Diff.EXT.evolX.wCntT w)) :
    Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ (m + 1) w
        (Function.update F (Work.Diff.EXT.evolX.wPosA K₁ K₂ m w ρ.val) v)
      = Function.update (Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ (m + 1) w F) ρ v := by
  rw [wTupA.eq_2]
  funext i
  by_cases h : i = ρ
  · subst h
    rw [Function.update_self, Function.update_self]
  · have hp : wPosA K₁ K₂ m w i.val ≠ wPosA K₁ K₂ m w ρ.val := by
      intro heq
      exact h (Fin.ext (wTupUpdateA_wPosA_inj m w K₁ K₂ i.isLt ρ.isLt heq))
    rw [Function.update_of_ne hp, Function.update_of_ne h]
    rfl

end Work.Diff.EXT.evolX
