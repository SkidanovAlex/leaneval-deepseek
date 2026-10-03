/-
# Howie's Case 1: the lifted presentation `⟨Γ̃ | R̃⟩`

Assembling the pieces (`coverPath`, `coverEdgeOf`, `coverPath_properties`,
`cover_code_and_noSelfLoop`, `cover_staggered`) this file defines the cyclic cover of a
presentation along a labelling which is zero on the relators.

The relators of the lifted presentation are the pairs `(i, n)` with `i : P.ι` and `n : ℤ` (ordered
lexicographically), and the relator with index `(i, n)` is `coverPath P L hrel i n`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverPresentation
import Submission.Work.ORLocInd.Howie.exists_tau
import Submission.Work.ORLocInd.Howie.coverPath_properties
import Submission.Work.ORLocInd.Howie.cover_code_and_noSelfLoop
import Submission.Work.ORLocInd.Howie.cover_staggered

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- **Howie's Case 1 (the construction).**  The *cyclic cover* of the presentation `P` along the
labelling `L` (which is zero on the relators, so that the relators lift to closed paths): its graph
is the cyclic cover `Γ̃` of `Γ`, its relators are the pairs `(i, n)` ordered lexicographically, and
the relator `(i,n)` is the lift `coverPath P L hrel i n`.  The code of an unoriented edge is
`coverEdgeOf P L τ`, where `τ` is a section of the level cocycle. -/
noncomputable def coverPresentation (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e) :
    Presentation (CoverVertex L) where
  α := CoverCode P
  linearOrder := coverCodeLinearOrder P
  edgeOf := coverEdgeOf P L τ
  edgeOf_reverse := (cover_code_and_noSelfLoop P L τ hτ).1
  noSelfLoop := (cover_code_and_noSelfLoop P L τ hτ).2
  ι := CoverRelator P
  linearOrder_ι := coverRelatorLinearOrder P
  base := fun i => (⟨P.base (ofLex i).1, (ofLex i).2⟩ : CoverVertex L)
  path := fun i => coverPath P L hrel (ofLex i).1 (ofLex i).2
  reduced := fun i => (coverPath_properties P L hrel ((cover_code_and_noSelfLoop P L τ hτ).2)
    (ofLex i).1 (ofLex i).2).1
  cyclicallyReduced := fun i =>
    (coverPath_properties P L hrel ((cover_code_and_noSelfLoop P L τ hτ).2)
      (ofLex i).1 (ofLex i).2).2.1
  notProperPower := fun i =>
    (coverPath_properties P L hrel ((cover_code_and_noSelfLoop P L τ hτ).2)
      (ofLex i).1 (ofLex i).2).2.2
  staggered := fun i j hij => cover_staggered P L hrel τ hτ (Prod.lex_def.mp hij)

@[simp] theorem coverPresentation_base (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    (i : (coverPresentation P L hrel τ hτ).ι) :
    (coverPresentation P L hrel τ hτ).base i =
      (⟨P.base (ofLex i).1, (ofLex i).2⟩ : CoverVertex L) := rfl

@[simp] theorem coverPresentation_path (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (hτ : ∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e)
    (i : (coverPresentation P L hrel τ hτ).ι) :
    (coverPresentation P L hrel τ hτ).path i = coverPath P L hrel (ofLex i).1 (ofLex i).2 := rfl

end Work.ORLocInd.Howie
