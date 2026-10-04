import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

theorem wTupConsFalse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (K₁ K₂ n : ℕ) (w : Work.Diff.EXT.evolX.Word n)
    (F : Fin (K₁ + K₂ + (n + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ (n + 1)
        (Work.Diff.EXT.evolX.Word.cons false w) F
      = Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ n w
          (fun t : Fin (K₁ + K₂ + n) => F t.succ) := by
  cases n with
  | zero =>
    -- The word is empty, so the `false` entry is the newest one: it is dropped from the
    -- `A`-tuple and the tuple is shifted by one (`Fin.succ`).
    cases w
    rw [wTupA.eq_2, wTupA.eq_1]
    funext i
    rw [wPosA_zero_cons_false]
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    have h := i.isLt
    simp only [wCntT_cons_false, wCntT] at h
    rw [Nat.min_eq_left (by omega)]
  | succ m =>
    rw [wTupA.eq_2, wTupA.eq_2]
    funext i
    rw [wPosA_cons_false]

end Work.Diff.EXT.evolX
