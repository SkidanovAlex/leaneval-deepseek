import Mathlib
import Submission.Work.OROneRel.delWordWalkDefs

namespace Work.OROneRel

universe u

theorem coverTgt_eq_coverSrc_of_coverEdge_eq {α : Type u} (c : α → ℤ) {p q : (α × ℤ) × Bool}
    (h1 : Work.OROneRel.coverEdge p = Work.OROneRel.coverEdge q) (h2 : p.2 ≠ q.2) :
    Work.OROneRel.coverTgt c p = Work.OROneRel.coverSrc c q := by
  obtain ⟨⟨x, i⟩, b⟩ := p
  obtain ⟨⟨x', i'⟩, b'⟩ := q
  simp only [coverEdge] at h1
  injection h1 with h1 h1'
  cases b <;> cases b' <;> simp_all [coverTgt, coverSrc]

end Work.OROneRel
