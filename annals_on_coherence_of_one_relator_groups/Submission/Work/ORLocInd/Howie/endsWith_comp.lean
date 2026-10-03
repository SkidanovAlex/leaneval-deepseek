import Mathlib
import Submission.Work.ORLocInd.Howie.PathReduced

universe u

namespace Work.ORLocInd.Howie

/-- Definitions used here live in `Submission.Work.ORLocInd.Howie.PathReduced`:
`Quiver.Path.EndsWith p e := ∃ p', p = p'.cons e`.
(`q.length ≠ 0` is the well-typed way of saying `q` is not the empty path.) -/
theorem endsWith_comp {V : Type u} [Quiver V] {a b c x : V} {p : Quiver.Path a b}
    {q : Quiver.Path b c} (hq : q.length ≠ 0) (e : x ⟶ c) :
    Quiver.Path.EndsWith (p.comp q) e ↔ Quiver.Path.EndsWith q e := by
  constructor
  · rintro ⟨r', hr⟩
    cases q with
    | nil => simp [Quiver.Path.length_nil] at hq
    | cons q' f =>
      rw [Quiver.Path.comp_cons] at hr
      obtain ⟨hb, -, hfe⟩ := Quiver.Path.cons.inj hr
      subst hb
      exact ⟨q', by rw [eq_of_heq hfe]⟩
  · rintro ⟨q', rfl⟩
    exact ⟨p.comp q', Quiver.Path.comp_cons p q' e⟩

end Work.ORLocInd.Howie
