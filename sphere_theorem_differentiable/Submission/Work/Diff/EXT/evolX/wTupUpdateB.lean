/-
# The shuffle calculus: updating a `B`-position updates the `B`-sub-tuple

This module proves `Work.Diff.EXT.evolX.wTupUpdateB`: writing a new value `v` into the level-`(m+1)`
tuple `F` at the `B`-position of the `ρ`-th entry of the `B`-sub-tuple of the word `w` amounts to
writing `v` into the `ρ`-th entry of the `B`-sub-tuple.

The content is purely combinatorial.  At level `m+1` the `B`-sub-tuple is the composition of the
tuple with the position map `wPosB K₁ K₂ m w` (`wTupB.eq_2`), so the statement is the elementary
fact that `Function.update` commutes with precomposition by an *injective* index map.  The
injectivity of the `B`-position map,

  `(wPosB K₁ K₂ m w r).val ≠ (wPosB K₁ K₂ m w s).val`  for `r ≠ s` inside the range,

is the only real input; it is proved here by induction on the word (`wTupUpdateB_wPosB_ne_val`),
together with the value formulas for the four recursion clauses of `wPosB`
(`wTupUpdateB_wPosB_val_*`).
-/
import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

set_option maxHeartbeats 800000

/-! ## The value of the `B`-position map, clause by clause

`wPosB K₁ K₂ n w r` is a `Fin (K₁ + K₂ + (n+1))`; these lemmas record its `.val` in the four
clauses of its recursion, so that the arithmetic below can be done by `omega` on natural numbers.
-/

/-- The `B`-position of the `r`-th entry in the base case of a `true` head (level `0`, `r < K₂`). -/
theorem wTupUpdateB_wPosB_val_zero_cons_true (K₁ K₂ r : ℕ) (hr : r < K₂) :
    (wPosB K₁ K₂ 0 (Word.cons true (Word.nil : Word 0)) r).val = K₁ + 1 + r := by
  rw [wPosB_zero_cons_true]
  exact Nat.min_eq_left (by omega)

/-- The `B`-position of the `r`-th entry in the base case of a `false` head (level `0`,
`1 ≤ r ≤ K₂`), the case `r = 0` being `wPosB_cons_false_zero`. -/
theorem wTupUpdateB_wPosB_val_zero_cons_false (K₁ K₂ r : ℕ) (hr0 : r ≠ 0) (hr : r ≤ K₂) :
    (wPosB K₁ K₂ 0 (Word.cons false (Word.nil : Word 0)) r).val = K₁ + r := by
  rw [wPosB_zero_cons_false]
  split_ifs with h
  · exact absurd h hr0
  · exact Nat.min_eq_left (by omega)

/-- A `false` head at a positive level sends `r = 0` to the position `0`. -/
theorem wTupUpdateB_wPosB_val_cons_false_zero (K₁ K₂ n : ℕ) (w : Word n) :
    (wPosB K₁ K₂ n (Word.cons false w) 0).val = 0 := by
  rw [wPosB_cons_false_zero, Fin.val_mk]

/-- A `true` head shifts the `B`-positions of the shortened word by `Fin.succ`. -/
theorem wTupUpdateB_wPosB_val_cons_true (K₁ K₂ n : ℕ) (w : Word (n + 1)) (r : ℕ) :
    (wPosB K₁ K₂ (n + 1) (Word.cons true w) r).val = (wPosB K₁ K₂ n w r).val + 1 := by
  rw [wPosB_cons_true, Fin.val_succ]

/-- A `false` head shifts the `B`-positions of the shortened word by `Fin.succ` as well (with the
argument decreased by one, `r = 0` being the separate case `wTupUpdateB_wPosB_val_cons_false_zero`). -/
theorem wTupUpdateB_wPosB_val_cons_false_succ (K₁ K₂ n : ℕ) (w : Word (n + 1)) (r : ℕ) :
    (wPosB K₁ K₂ (n + 1) (Word.cons false w) (r + 1)).val =
      (wPosB K₁ K₂ n w r).val + 1 := by
  rw [wPosB_cons_false_succ, Fin.val_succ]

/-! ## Injectivity of the `B`-position map -/

/-- The length-`1` words have `wCntF` equal to `0` (head `true`) resp. `1` (head `false`). -/
theorem wTupUpdateB_wCntF_cons_true_nil : wCntF (Word.cons true (Word.nil : Word 0)) = 0 := rfl

theorem wTupUpdateB_wCntF_cons_false_nil : wCntF (Word.cons false (Word.nil : Word 0)) = 1 := rfl

/-- **The `B`-position map is injective on its range**: two distinct indices in
`[0, K₂ + wCntF w)` receive distinct positions. -/
theorem wTupUpdateB_wPosB_ne_val (K₁ K₂ : ℕ) : ∀ (n : ℕ) (w : Word (n + 1)) (r s : ℕ),
    r < K₂ + wCntF w → s < K₂ + wCntF w → r ≠ s →
    (wPosB K₁ K₂ n w r).val ≠ (wPosB K₁ K₂ n w s).val := by
  intro n
  induction n with
  | zero =>
    intro w r s hr hs hrs
    cases w with
    | cons b w0 =>
      cases w0
      cases b
      · -- word `cons false nil`
        rw [wTupUpdateB_wCntF_cons_false_nil] at hr hs
        have hr' : r ≤ K₂ := by omega
        have hs' : s ≤ K₂ := by omega
        rcases Nat.eq_zero_or_pos r with h0 | hpos
        · subst h0
          rw [wTupUpdateB_wPosB_val_cons_false_zero, wTupUpdateB_wPosB_val_zero_cons_false K₁ K₂ s (by omega) hs']
          omega
        · rcases Nat.eq_zero_or_pos s with h0 | hpos2
          · subst h0
            rw [wTupUpdateB_wPosB_val_cons_false_zero, wTupUpdateB_wPosB_val_zero_cons_false K₁ K₂ r (by omega) hr']
            omega
          · rw [wTupUpdateB_wPosB_val_zero_cons_false K₁ K₂ r (by omega) hr',
                wTupUpdateB_wPosB_val_zero_cons_false K₁ K₂ s (by omega) hs']
            omega
      · -- word `cons true nil`
        rw [wTupUpdateB_wCntF_cons_true_nil] at hr hs
        have hr' : r < K₂ := by omega
        have hs' : s < K₂ := by omega
        rw [wTupUpdateB_wPosB_val_zero_cons_true K₁ K₂ r hr', wTupUpdateB_wPosB_val_zero_cons_true K₁ K₂ s hs']
        omega
  | succ n ih =>
    intro w r s hr hs hrs
    cases w with
    | cons b w' =>
      cases b
      · -- head `false`
        rw [wCntF_cons_false] at hr hs
        have hr2 : r < K₂ + wCntF w' + 1 := by omega
        have hs2 : s < K₂ + wCntF w' + 1 := by omega
        rcases Nat.eq_zero_or_pos r with h0 | hpos
        · subst h0
          rw [wTupUpdateB_wPosB_val_cons_false_zero]
          rcases Nat.eq_zero_or_pos s with h0' | hpos'
          · omega
          · obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
            rw [wTupUpdateB_wPosB_val_cons_false_succ]
            omega
        · obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
          rw [wTupUpdateB_wPosB_val_cons_false_succ]
          rcases Nat.eq_zero_or_pos s with h0 | hpos
          · subst h0
            rw [wTupUpdateB_wPosB_val_cons_false_zero]
            omega
          · obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
            rw [wTupUpdateB_wPosB_val_cons_false_succ]
            exact fun h => ih w' r' s' (by omega) (by omega) (by omega) (by omega)
      · -- head `true`
        rw [wCntF_cons_true] at hr hs
        rw [wTupUpdateB_wPosB_val_cons_true, wTupUpdateB_wPosB_val_cons_true]
        exact fun h => ih w' r s hr hs hrs (by omega)

/-! ## The update lemma -/

theorem wTupUpdateB
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (K₁ K₂ m : ℕ) (w : Work.Diff.EXT.evolX.Word (m + 1))
    (F : Fin (K₁ + K₂ + (m + 1)) → Work.Diff.EXT.TField (I := I) (M := M))
    (v : Work.Diff.EXT.TField (I := I) (M := M))
    (ρ : Fin (K₂ + Work.Diff.EXT.evolX.wCntF w)) :
    Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ (m + 1) w
        (Function.update F (Work.Diff.EXT.evolX.wPosB K₁ K₂ m w ρ.val) v)
      = Function.update (Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ (m + 1) w F) ρ v := by
  funext i
  simp only [wTupB]
  by_cases hi : i = ρ
  · subst hi
    rw [Function.update_self, Function.update_self]
  · have hne : wPosB K₁ K₂ m w i.val ≠ wPosB K₁ K₂ m w ρ.val := by
      intro h
      exact wTupUpdateB_wPosB_ne_val K₁ K₂ m w ρ.val i.val ρ.isLt i.isLt
        (fun hval => hi (Fin.ext hval.symm)) (congrArg Fin.val h.symm)
    rw [Function.update_of_ne hi, Function.update_of_ne hne]

end Work.Diff.EXT.evolX
