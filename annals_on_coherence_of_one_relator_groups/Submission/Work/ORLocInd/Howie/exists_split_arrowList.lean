import Mathlib
import Submission.Work.ORLocInd.Howie.Relator

namespace Work.ORLocInd.Howie

/-- If the arrow `g` occurs in the arrow list of a path `p : a → b`, then `p` splits at `g`:
there are `q₁ : a → g.left` and `q₂ : g.right → b` with `p = q₁.comp (g.hom.toPath.comp q₂)`,
and correspondingly the arrow list of `p` is `arrowList q₁ ++ [g] ++ arrowList q₂`. -/
theorem exists_split_arrowList {V : Type*} [Quiver V] {a b : V} (p : Quiver.Path a b)
    (g : Quiver.Total V) (hg : g ∈ Quiver.Path.arrowList p) :
    ∃ (q₁ : Quiver.Path a g.left) (q₂ : Quiver.Path g.right b),
      p = q₁.comp (g.hom.toPath.comp q₂) ∧
      Quiver.Path.arrowList p = Quiver.Path.arrowList q₁ ++ [g] ++ Quiver.Path.arrowList q₂ := by
  induction p with
  | nil => simp at hg
  | cons p e ih =>
    rw [Quiver.Path.arrowList_cons] at hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨q₁, q₂, hp, hal⟩ := ih hg
      refine ⟨q₁, q₂.cons e, ?_, ?_⟩
      · rw [hp, Quiver.Path.comp_cons, Quiver.Path.comp_cons]
      · rw [Quiver.Path.arrowList_cons, hal, Quiver.Path.arrowList_cons]
        simp [List.append_assoc]
    · rw [List.mem_singleton] at hg
      subst hg
      exact ⟨p, Quiver.Path.nil, by simp,
        by rw [Quiver.Path.arrowList_cons]; simp⟩

end Work.ORLocInd.Howie
