import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.EXT.evolX

/-! ## The `B`-tuple of a word beginning with `false`

The word `Word.cons false w` routes the newest covariant derivative direction to the second factor,
so the `B`-tuple of the level-`(n+1)` tuple is the first entry `F 0` (the newest direction, at
position `0` of the tuple) followed by the `B`-tuple of the level-`n` tuple `t ↦ F t.succ` for the
tail word `w`.  This is the recursion that lets one peel the word letters off one at a time.

The two cases `w = nil` (level `1`) and `w = cons b w'` (level `≥ 2`) are proved separately: the
underlying `wPosB` recursion has a genuine `n = 0` base case. -/

/-- The base case of the recursion: for the one-letter word `false :: nil`, the `B`-tuple starts
with the newest direction `F 0` followed by the `B`-tuple of the empty word. -/
theorem wTupB_cons_false_nil
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (K₁ K₂ : ℕ)
    (F : Fin (K₁ + K₂ + (0 + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ (0 + 1)
        (Word.cons false Word.nil) F
      = (Fin.cons (F 0) (Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ 0 Word.nil
            (fun t : Fin (K₁ + K₂ + 0) => F t.succ))
          : (Fin (K₂ + wCntF (Word.nil : Word 0) + 1) →
              Work.Diff.EXT.TField (I := I) (M := M))) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [wTupB, Fin.cons_zero]
    show F (Work.Diff.EXT.evolX.wPosB K₁ K₂ 0 (Word.cons false Word.nil) 0) = F 0
    rw [wPosB_cons_false_zero]
    rfl
  · have hj : j.val < K₂ := j.isLt
    simp only [wTupB, Fin.cons_succ]
    rw [Fin.val_succ, wPosB_zero_cons_false, ite_eq_right (by omega)]
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    rw [Nat.min_eq_left (by omega)]
    omega

/-- The inductive step of the recursion: for `false :: b :: w` the newest direction again goes to
the `B`-tuple as its first entry, and the remaining entries are those of the `B`-tuple of
`b :: w`, evaluated at the level-`(n+1)` tuple `t ↦ F t.succ`. -/
theorem wTupB_cons_false_cons
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (K₁ K₂ m : ℕ) (b : Bool) (w : Word m)
    (F : Fin (K₁ + K₂ + (m + 1 + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ (m + 1 + 1)
        (Word.cons false (Word.cons b w)) F
      = (Fin.cons (F 0) (Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ (m + 1)
            (Word.cons b w) (fun t : Fin (K₁ + K₂ + (m + 1)) => F t.succ))
          : (Fin (K₂ + wCntF (Word.cons b w) + 1) →
              Work.Diff.EXT.TField (I := I) (M := M))) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [wTupB, Fin.cons_zero]
    congr 1
  · simp only [wTupB, Fin.cons_succ]
    rw [Fin.val_succ, wPosB_cons_false_succ]

theorem wTupBConsFalse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (K₁ K₂ n : ℕ) (w : Work.Diff.EXT.evolX.Word n)
    (F : Fin (K₁ + K₂ + (n + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ (n + 1)
        (Work.Diff.EXT.evolX.Word.cons false w) F
      = (Fin.cons (F 0) (Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ n w
            (fun t : Fin (K₁ + K₂ + n) => F t.succ))
          : (Fin (K₂ + Work.Diff.EXT.evolX.wCntF w + 1) →
              Work.Diff.EXT.TField (I := I) (M := M))) := by
  cases w with
  | nil => exact wTupB_cons_false_nil (I := I) (M := M) K₁ K₂ F
  | cons b w => exact wTupB_cons_false_cons (I := I) (M := M) K₁ K₂ _ b w F

end Work.Diff.EXT.evolX
