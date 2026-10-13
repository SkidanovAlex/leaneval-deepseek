import Mathlib
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.IterDirAux
import Submission.Work.WilG4c.iterDir_swap

open scoped Topology

namespace Work.WilG4c

open Work.WilkG4c

/-- The iterated directional derivative `iterDir L G` (defined in
`Submission/Work/WilG4c/Engine.lean` as the iterated `fderiv` along the list `L`, head =
outermost derivative) is invariant under permuting the list, for `C^{|L|}` functions: the mixed
partial derivatives commute. -/
theorem iterDir_perm {m : ℕ} (G : (Fin m → ℝ) → ℝ) {L L' : List (Fin m)} (h : L.Perm L')
    (z : Fin m → ℝ) (hG : ContDiffAt ℝ L.length G z) : iterDir L G z = iterDir L' G z := by
  -- We induct on the derivation of `L.Perm L'`.  The only non-trivial steps are the adjacent
  -- transposition (`iterDir_swap`, i.e. Clairaut/Schwarz for the outermost two derivatives)
  -- and the `cons` step, where the induction hypothesis is upgraded from a pointwise equality
  -- to an eventual equality so that it survives taking `fderiv`.
  have key : ∀ (L L' : List (Fin m)), L.Perm L' → ∀ z, ContDiffAt ℝ L.length G z →
      iterDir L G z = iterDir L' G z := by
    intro L L' h
    induction h with
    | nil => intro z _; rfl
    | cons x _ ih =>
      intro z hG
      simp only [iterDir_cons]
      congr 1
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hG.eventually (by simp)] with y hy
      exact ih y (hy.of_le (by simp [List.length_cons]))
    | swap x y l =>
      intro z hG
      -- `hG` is stated at level `|y :: x :: l| = l.length + 2`, which is definitionally but
      -- not syntactically the level expected by `iterDir_swap`.
      have he : (↑((y :: x :: l).length) : WithTop ℕ∞) = ↑l.length + 2 := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring
      exact iterDir_swap G y x l z (he ▸ hG)
    | trans h₁ _ ih₁ ih₂ =>
      intro z hG
      exact (ih₁ z hG).trans (ih₂ z (by rwa [← h₁.length_eq]))
  exact key L L' h z hG

end Work.WilG4c
