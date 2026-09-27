import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

namespace Work.Endgame

/-- A homeomorphism `e : X ≃ₜ Y` restricts to a homeomorphism between the complements of
corresponding points: `{p}ᶜ ≃ₜ {e p}ᶜ`. This is `Homeomorph.sets` applied to the fact that
`e` maps `{p}ᶜ` onto `{e p}ᶜ` (equivalently `e ⁻¹' {e p}ᶜ = {p}ᶜ`). -/
theorem nonempty_homeomorph_compl_singleton {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (p : X) :
    Nonempty (({p}ᶜ : Set X) ≃ₜ ({e p}ᶜ : Set Y)) :=
  ⟨e.sets (by ext x; simp [Set.mem_compl_iff])⟩

end Work.Endgame
