/-
  WilG4c / `StepChoiceOut` — the abbreviated interface of the sliced choice lemma.

  `Work.WilkG4c.hmax_of_choice_lists` takes, as its two hypotheses, verbatim the `hchoice`
  block of the sliced choice lemma (`CurveFamAlphaListPureSliced`, restricted to a single list
  `L`) and the fibre-sup finiteness block (`BddSupFiniteNoI`).  Copying those blocks into every
  statement that mentions them is unreadable, so they are abbreviated here as `ChoiceOut`
  (per list), `ChoiceOutAt` (one list) and `FibreBdd`; all three are `abbrev`s, hence
  *definitionally equal* to the blocks they stand for and can be passed to
  `hmax_of_choice_lists` (and used in any statement about it) without change.
-/
import Mathlib
import Submission.Work.WilG4c.hmax_of_choice_lists

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The choice block for one list.**  `ChoiceOutAt f L γ` says that `γ x` is a
`2`-approximate maximiser of `|∂^L f|` on the fibre `{y ∈ openCube n}` at `x`, *whenever* such a
maximiser exists (the implication form is what makes the choice vacuous on fibres where the sup
is infinite or the locus is empty). -/
abbrev ChoiceOutAt {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    (γ : ℝ → (Fin n → ℝ)) : Prop :=
  ∀ x : ℝ,
    (∃ y : Fin n → ℝ, y ∈ WilkiesDesign.openCube n ∧
        ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f u)
          (Work.WilkG4c.pt x y) ∧
        ∀ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n →
          ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f u)
            (Work.WilkG4c.pt x y') →
          |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f u)
              (Work.WilkG4c.pt x y') (fun j => Pi.single (L.get j) 1)| ≤
            2 * |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f u)
              (Work.WilkG4c.pt x y) (fun j => Pi.single (L.get j) 1)|) →
      γ x ∈ WilkiesDesign.openCube n ∧
      ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f u)
        (Work.WilkG4c.pt x (γ x)) ∧
      ∀ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n →
        ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f u)
          (Work.WilkG4c.pt x y') →
        |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f u)
            (Work.WilkG4c.pt x y') (fun j => Pi.single (L.get j) 1)| ≤
          2 * |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f u)
            (Work.WilkG4c.pt x (γ x)) (fun j => Pi.single (L.get j) 1)|

/-- **The choice block.**  `ChoiceOut f r γs` says that for every list `L` of length `≤ r`,
`γs L` is the choice curve of `ChoiceOutAt`.  It is verbatim the `hchoice` hypothesis of
`Work.WilkG4c.hmax_of_choice_lists`. -/
abbrev ChoiceOut {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (r : ℕ)
    (γs : (L : List (Fin (n + 1))) → ℝ → (Fin n → ℝ)) : Prop :=
  ∀ (L : List (Fin (n + 1))), L.length ≤ r → ChoiceOutAt f L (γs L)

/-- **The fibre-sup finiteness block.**  `FibreBdd f r B` says that off the finite set `B` the
supremum, over the fibre `{y ∈ openCube n}` intersected with the `C^{|L|}`-locus, of `|∂^L f|`
is finite, for every list `L` of length `≤ r`.  It is verbatim the `hBdd` hypothesis of
`Work.WilkG4c.hmax_of_choice_lists`. -/
abbrev FibreBdd {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (r : ℕ) (B : Finset ℝ) : Prop :=
  ∀ (L : List (Fin (n + 1))), L.length ≤ r →
    ∀ x ∈ Work.WilkG4c.I, x ∉ (B : Set ℝ) →
      BddAbove ((fun y : Fin n → ℝ =>
          |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f u)
            (Work.WilkG4c.pt x y) (fun j => Pi.single (L.get j) 1)|) ''
        {y : Fin n → ℝ | y ∈ WilkiesDesign.openCube n ∧
          ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f u)
            (Work.WilkG4c.pt x y)})

end Work.WilkG4c
