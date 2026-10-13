import Mathlib
import Submission.Work.WilC1.Defs

/-!
# Existential closure of quantifier-free formulas

A formula `φ` with free variables `α ⊕ γ`, where `γ` is finite, becomes a formula with free
variables `α` after existentially quantifying all the `γ`-variables (`Formula.iExs`).  The content
of this file is that this operation sends quantifier-free formulas to existential ones: `iExs`
is implemented as a relabelling followed by `BoundedFormula.exs`, and `exs` is a finite nest of
existential quantifiers, which `IsExistential` explicitly allows.
-/

namespace FirstOrder.Language.BoundedFormula

/-- Existential closure of every bound variable (`BoundedFormula.exs`) preserves the class of
existential formulas.  This is immediate from the definition of `exs` as an iterated `ex`, since
`IsExistential` is closed under existential quantification. -/
theorem IsExistential.exs {L : Language} {α : Type*} :
    ∀ {n : ℕ} {ψ : L.BoundedFormula α n},
      ψ.IsExistential → (ψ.exs : L.Formula α).IsExistential
  | 0, _, h => h
  | _n + 1, _, h => (h.ex).exs

end FirstOrder.Language.BoundedFormula

namespace Work.WilC1

theorem IsQF_isExistential_iExs {L : FirstOrder.Language} {α γ : Type*} [Finite γ]
    {φ : FirstOrder.Language.Formula (L := L) (α ⊕ γ)}
    (h : FirstOrder.Language.BoundedFormula.IsQF φ) :
    FirstOrder.Language.BoundedFormula.IsExistential
      (FirstOrder.Language.Formula.iExs (L := L) γ φ) := by
  rw [FirstOrder.Language.Formula.iExs]
  exact (h.relabel _).isExistential.exs

end Work.WilC1
