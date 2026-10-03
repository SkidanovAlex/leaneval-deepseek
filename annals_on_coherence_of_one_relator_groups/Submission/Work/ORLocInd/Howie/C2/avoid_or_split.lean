import Mathlib
import Submission.Work.ORLocInd.Howie.DelReach

namespace Work.ORLocInd.Howie.C2

theorem avoid_or_split {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (e : Quiver.Total V) {a b : V}
    (p : Quiver.Path a b) :
    Work.ORLocInd.Howie.Avoids P e p ∨
      ∃ (g : Quiver.Total V) (α : Quiver.Path a g.left) (β : Quiver.Path g.right b),
        Work.ORLocInd.Howie.Avoids P e α ∧ P.edgeOf g = P.edgeOf e ∧
        p = α.comp (g.hom.toPath.comp β) := by
  /- The first arrow of `p` carrying the code of `e` (if any) splits `p` into a prefix avoiding
  `e`, that arrow, and an arbitrary tail.  Induction on the path. -/
  induction p with
  | nil => exact Or.inl (Work.ORLocInd.Howie.avoids_nil P e)
  | cons q f ih =>
      by_cases hq : Work.ORLocInd.Howie.Avoids P e q
      · by_cases hf : P.edgeOf (Quiver.Total.mk _ _ f) = P.edgeOf e
        · -- the last arrow is the first one carrying the code of `e`
          refine Or.inr ⟨Quiver.Total.mk _ _ f, q, Quiver.Path.nil, hq, hf, ?_⟩
          simp only [Quiver.Path.comp_nil]
          rw [Quiver.Hom.toPath, Quiver.Path.comp_cons, Quiver.Path.comp_nil]
        · -- the last arrow avoids `e` as well
          exact Or.inl ((Work.ORLocInd.Howie.avoids_cons_iff P e q f).mpr ⟨hq, hf⟩)
      · -- the split already occurs inside `q`
        rcases ih with h | ⟨g, α, β, hα, hg, hqeq⟩
        · exact absurd h hq
        · exact Or.inr ⟨g, α, β.cons f, hα, hg, by
            rw [hqeq]
            simp only [Quiver.Path.comp_cons]⟩

end Work.ORLocInd.Howie.C2
