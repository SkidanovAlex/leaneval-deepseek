/-
  WilC1 — the dictionary between the flexible notion `REx` of this area and the frozen
  `WilkiesDesign.RExpExist`.

  `REx (Fin n) X` and `Work.WilC0.RExpExistI X` are the same proposition: both say that `X` is
  the projection of the zero set of one rexp-polynomial along a block of witnesses indexed by an
  arbitrary *finite type* `γ`.  (`REx` writes the set-builder out, `RExpExistI` names it
  `RExZero`; `Work.WilC1.rexpEval` and `Work.WilC0.rexpEval` are the same definition.)  So the
  only content is the bridge `Work.WilC0.rexExistI_iff_rexExist`, which passes from an arbitrary
  finite witness type `γ` to the concrete witnesses `Fin m` by renaming `γ ≃ Fin (card γ)` and
  `Fin n ⊕ Fin m ≃ Fin (n + m)`.
-/
import Mathlib
import Submission.Work.WilC1.Defs
import Submission.Work.WilC0.Bridge

namespace Work.WilC1

/-- On `Fin n`-indexed ambient variables, the flexible notion `REx` of this area agrees with the
frozen `WilkiesDesign.RExpExist`. -/
theorem REx_iff_RExpExist {n : ℕ} (X : Set (Fin n → ℝ)) :
    REx (Fin n) X ↔ WilkiesDesign.RExpExist X := by
  rw [← Work.WilC0.rexExistI_iff_rexExist]
  exact Iff.rfl

end Work.WilC1
