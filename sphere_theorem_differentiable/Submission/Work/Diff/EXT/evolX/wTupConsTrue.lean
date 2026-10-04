import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

theorem wTupConsTrue
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (K₁ K₂ n : ℕ) (w : Work.Diff.EXT.evolX.Word n)
    (F : Fin (K₁ + K₂ + (n + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ (n + 1)
        (Work.Diff.EXT.evolX.Word.cons true w) F
      = (Fin.cons (F 0) (Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ n w
            (fun t : Fin (K₁ + K₂ + n) => F t.succ))
          : (Fin (K₁ + Work.Diff.EXT.evolX.wCntT w + 1) →
              Work.Diff.EXT.TField (I := I) (M := M))) := by
  rw [wTupA.eq_2]
  funext i
  induction i using Fin.cases with
  | zero =>
    simp only [Fin.val_zero, wPosA_cons_true_zero, Fin.cons_zero]
    congr 1
  | succ j =>
    cases n with
    | zero =>
      cases w
      simp only [Fin.val_succ]
      rw [wPosA_zero_cons_true]
      rw [Fin.cons_succ]
      rw [wTupA.eq_1]
      simp only
      rw [ite_eq_right (by omega : ¬ ((↑j : ℕ) + 1 = 0))]
      congr 1
      exact Fin.ext (Nat.min_eq_left (by
        have h : (↑j : ℕ) < K₁ + 0 := j.isLt
        omega))
    | succ m =>
      simp only [Fin.val_succ]
      rw [wPosA_cons_true_succ K₁ K₂ m w ↑j]
      rw [Fin.cons_succ]
      rw [wTupA.eq_2]

end Work.Diff.EXT.evolX
