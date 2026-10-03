import Mathlib
import Submission.Work.ORLocInd.Howie.Span

universe u

namespace Work.ORLocInd.Howie

/-- A path of `Γ` whose vertices are visited by the datum and whose arrows occur in the datum,
viewed as a path of the span, has the same arrows as the original path: the arrow list of the span
path, projected back to the total space of `Γ`, is the arrow list of the original path.

This is stated with the initial vertex `a` and the proof `ha` fixed, and with the endpoint `b` and
the memberships `hb`, `hp` universally quantified, so that the induction on `p` may be carried out
directly (the recursive call of `pathToSpan` uses the same `a`, `ha`). -/
theorem pathToSpan_arrowList_aux {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    [DecidableEq V] {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) {a : V} (ha : a ∈ D.visitedList) :
    ∀ {b : V} (p : Quiver.Path a b) (hb : b ∈ D.visitedList) (hp : InSpan D p),
      (pathToSpan D a ha p hb hp).arrowList.map (fun f => f.hom.1) = p.arrowList := by
  intro b p
  induction p with
  | nil =>
      intro hb hp
      simp only [pathToSpan]
      rfl
  | cons q e ih =>
      intro hb hp
      simp only [pathToSpan]
      rw [Quiver.Path.arrowList_cons, Quiver.Path.arrowList_cons, List.map_append, ih]
      rfl

theorem pathToSpan_arrowList {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    [DecidableEq V] {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) {a b : V} (p : Quiver.Path a b)
    (ha : a ∈ D.visitedList) (hb : b ∈ D.visitedList)
    (hp : Work.ORLocInd.Howie.InSpan D p) :
    (Work.ORLocInd.Howie.pathToSpan D a ha p hb hp).arrowList.map (fun f => f.hom.1) =
      p.arrowList :=
  pathToSpan_arrowList_aux D ha p hb hp

end Work.ORLocInd.Howie
