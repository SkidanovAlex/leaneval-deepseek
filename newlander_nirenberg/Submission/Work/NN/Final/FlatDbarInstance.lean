/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The flat Poincaré interface is inhabited

`FlatOne` (the open `(0,1)`-level flat `∂̄`-Poincaré on nested polydiscs) and `FlatTwo` (its
`(0,2)`-analogue) are proved in this directory (`NN/Final/flatOne`, `NN/Final/flatTwo`); this
module combines them into an inhabitant of the pair `FlatDbar` used by the perturbation argument.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.flatOne
import Submission.Work.NN.Final.flatTwo

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

variable {n : ℕ}

/-- The `(0,1)`-level interface is inhabited. -/
theorem nonempty_flatOne {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hα0 : 0 < α) (hα1 : α < 1) : Nonempty (FlatOne n α ρ) :=
  flatOne hρ hα0 hα1

/-- The `(0,2)`-level interface is inhabited. -/
theorem nonempty_flatTwo {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hα0 : 0 < α) (hα1 : α < 1) : Nonempty (FlatTwo n α ρ) :=
  flatTwo hρ hα0 hα1

/-- **The pair of flat Poincaré operators exists.** -/
theorem nonempty_flatDbar {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hα0 : 0 < α) (hα1 : α < 1) : Nonempty (FlatDbar n α ρ) :=
  let F₁ := Classical.choice (nonempty_flatOne (n := n) hρ hα0 hα1)
  let F₂ := Classical.choice (nonempty_flatTwo (n := n) hρ hα0 hα1)
  ⟨⟨F₁, F₂⟩⟩

end Work.NN.Final
