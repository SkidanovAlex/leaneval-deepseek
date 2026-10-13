/-
  WilC6 — C6: model completeness of `T_e = Th(ℝ_exp)` implies that the complement of an
  existentially definable (`ExpExist`) set is again existentially definable.

  The proof: write `X` as the projection of the zero set of an exp-polynomial `P`; the formula
  `complFormula P` (a `∀`-formula) describes `Xᶜ`; `exists_isEF_iff_of_modelComplete` replaces it,
  over every model of `TE`, by an existential formula `Ψ`; over the standard model `ℝ` the two
  describe the same set, and `IsEF.expExist` flattens `Ψ` back to the `ExpExist` shape.
-/
import Submission.Work.WilC6.Base
import Submission.Work.WilC6.Formula
import Submission.Work.WilC6.Main
import Submission.Work.WilC6.Flatten.expExist

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC6

theorem C6_compl_of_modelComplete_proved (hMC : ModelComplete TE) {n : ℕ}
    (X : Set (Fin n → ℝ)) (h : ExpExist X) : ExpExist Xᶜ := by
  obtain ⟨m, P, hX⟩ := h
  obtain ⟨Ψ, hΨ, h1, h2⟩ := exists_isEF_iff_of_modelComplete hMC (complFormula P)
  have hiff : realizeSet Ψ = realizeSet (complFormula P) := by
    ext x
    simp only [realizeSet, Set.mem_ofPred_eq]
    exact ⟨fun hx => h2 ℝ x hx, fun hx => h1 ℝ x hx⟩
  rw [← realizeSet_complFormula P hX, ← hiff]
  exact Flatten.expExist Ψ hΨ

/-- Complement closure of `ExpExist`, in the shape in which it is consumed as the hypothesis
`hW` by area B (`WilKiesDesign.B_syntax`) and by the top-level wiring. -/
theorem expExist_compl (hMC : ModelComplete TE) (n : ℕ) (X : Set (Fin n → ℝ))
    (h : ExpExist X) : ExpExist Xᶜ :=
  C6_compl_of_modelComplete_proved hMC X h

end Work.WilC6

namespace WilkiesDesign.CG

/-- `C6_compl_of_modelComplete`, proved.  The statement is identical to the frozen hole in
`Submission/Work/Wilkies/CG/Spec.lean`. -/
theorem C6_compl_of_modelComplete_proved (hMC : ModelComplete TE) {n : ℕ}
    (X : Set (Fin n → ℝ)) (h : ExpExist X) : ExpExist Xᶜ :=
  Work.WilC6.C6_compl_of_modelComplete_proved hMC X h

end WilkiesDesign.CG
