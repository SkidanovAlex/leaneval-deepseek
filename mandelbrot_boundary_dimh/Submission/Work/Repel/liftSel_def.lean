import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic

/-!
# `liftSel`: choosing the point of `U'` with a prescribed `π`-image

In Shishikura §6 the "Moreover" clause of (4.2.3) is used with `U'` a set on which the projection
`π = MandelDim.piExp` is injective.  Then for every `w` such that `π (R^[m] w) ∈ π '' U'` there is a
*unique* point of `U'` with that `π`-image.  `liftSel R m U' w` is such a point (chosen by
`Classical.choose`; junk value `0` when no witness exists).  This file provides the definition and
its (trivial) specification; its holomorphy is `Work.Repel.liftSel_differentiableOn`.
-/

namespace Work.Repel

/-- The point of `U'` whose `π`-image equals that of `R^[m] w`, when such a point exists; junk
value `0` otherwise. -/
noncomputable def liftSel (R : ℂ → ℂ) (m : ℕ) (U' : Set ℂ) : ℂ → ℂ :=
  fun w => by
    classical
    exact if h : ∃ w' ∈ U', MandelDim.piExp w' = MandelDim.piExp (R^[m] w) then h.choose else 0

/-- `liftSel` picks a point of `U'` with the required `π`-image whenever one exists. -/
theorem liftSel_spec {R : ℂ → ℂ} {m : ℕ} {U' : Set ℂ} {w : ℂ}
    (h : ∃ w' ∈ U', MandelDim.piExp w' = MandelDim.piExp (R^[m] w)) :
    liftSel R m U' w ∈ U' ∧ MandelDim.piExp (liftSel R m U' w) = MandelDim.piExp (R^[m] w) := by
  have hval : liftSel R m U' w = h.choose := by
    unfold liftSel
    exact dif_pos h
  rw [hval]
  exact ⟨h.choose_spec.1, h.choose_spec.2⟩

end Work.Repel
