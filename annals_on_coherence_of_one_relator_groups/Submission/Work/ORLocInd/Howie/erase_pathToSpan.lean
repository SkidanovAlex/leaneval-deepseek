import Mathlib
import Submission.Work.ORLocInd.Howie.Span

universe u

namespace Work.ORLocInd.Howie

/-- The erasure of the span path underlying a path of the ambient graph is that path itself.

This is stated with the initial vertex `a` and the proof `ha` fixed, and with the endpoint `b` and
the memberships `hb`, `hp` universally quantified, so that the induction on `p` may be carried out
directly (the recursive call of `pathToSpan` uses the same `a`, `ha`). -/
theorem erase_pathToSpan_aux {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    [DecidableEq V] {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) {a : V} (ha : a ∈ D.visitedList) :
    ∀ {b : V} (p : Quiver.Path a b) (hb : b ∈ D.visitedList) (hp : InSpan D p),
      erase D ⟨a, ha⟩ (pathToSpan D a ha p hb hp) = p := by
  intro b p
  induction p with
  | nil =>
      intro hb hp
      simp only [pathToSpan]
      rfl
  | cons q e ih =>
      intro hb hp
      simp only [pathToSpan, erase]
      rw [ih]
      rfl

theorem erase_pathToSpan {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    [DecidableEq V] {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) {a b : V} (p : Quiver.Path a b)
    (ha : a ∈ D.visitedList) (hb : b ∈ D.visitedList)
    (hp : Work.ORLocInd.Howie.InSpan D p) :
    Work.ORLocInd.Howie.erase D ⟨a, ha⟩
      (Work.ORLocInd.Howie.pathToSpan D a ha p hb hp) = p :=
  erase_pathToSpan_aux D ha p hb hp

end Work.ORLocInd.Howie
