import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shuffle calculus: a `true` letter does not touch the `B`-sub-tuple

This is the `B`-half of the structural recursion of the binary-word split `wTupA`/`wTupB` from
`mulOpJetsDefs`: if the newest derivative direction of the word is routed to the first factor
(`Word.cons true w`), the `B`-sub-tuple of the level-`(n+1)` tuple is unchanged — it is the
`B`-sub-tuple of the shortened word `w` applied to the shifted tuple `F ∘ Fin.succ`.

The content is entirely combinatorial: at level `n+1` the `B`-positions of `cons true w` are the
successors of the `B`-positions of `w` (`wPosB_cons_true`), because the new direction occupies
position `0` of the tuple and everything else is shifted by one.
-/

namespace Work.Diff.EXT.evolX

theorem wTupBConsTrue
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (K₁ K₂ n : ℕ) (w : Work.Diff.EXT.evolX.Word n)
    (F : Fin (K₁ + K₂ + (n + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ (n + 1)
        (Work.Diff.EXT.evolX.Word.cons true w) F
      = Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ n w
          (fun t : Fin (K₁ + K₂ + n) => F t.succ) := by
  cases n with
  | zero =>
    cases w with
    | nil =>
      -- level `1`, word `cons true nil`: the single direction goes to `A`, so the `B`-tuple of
      -- length `K₂` sits at the positions `K₁ + 1 + r`, shifted by the successor against the
      -- base case of `wTupB` (which places the `B`-tuple of `nil` at `K₁ + r`).
      simp only [wTupB]
      funext i
      congr 1
      apply Fin.ext
      rw [wPosB_zero_cons_true, Fin.succ_mk]
      dsimp only
      have h : (i : ℕ) < K₂ := i.isLt
      omega
  | succ n =>
    -- level `n + 2`, word `cons true w`: `wPosB (cons true w) r = (wPosB w r).succ` is
    -- definitional, so the two sides agree with the shift `F ∘ Fin.succ` of the tuple.
    simp only [wTupB]
    funext i
    rfl

end Work.Diff.EXT.evolX
