import Submission.Work.CoreTopology.EssentialLoop
import Submission.Work.SurgeryInvariance.Defs

/-!
# The concrete invariant `im(H₁(F ∩ U ; ℚ) → H₁(F ; ℚ))`

`Submission.Work.SurgeryInvariance.Defs` (built by the sibling subproject) defines, for a region
`U ⊆ ℝ³` and a parametrised torus `P`, the `ℚ`-subspace

  `Work.SurgeryInvariance.WindingSpan P U ≤ ℚ² = H₁(T² ; ℚ)`

spanned by the winding vectors of the closed curves of `F = P.carrier` lying in `U`; it vanishes
exactly when `U` contains no essential loop (`WindingSpan_eq_bot_iff`).  This is the curve-level
form of Pardon's invariant `im(H₁(F ∩ U ; ℚ) → H₁(F ; ℚ))`.

This file records that `WindingSpan` is an instance of `Work.CoreTopology.HomPieceData`, so that
Pardon's `doublebubble`/`spherefamily` lemma (`Work.CoreTopology.double_bubble_geometric`) applies
to it verbatim, the only remaining inputs being the `0 / all` dichotomy and the surgery bound.

*NOTE*: this module depends on the sibling subproject `Work.SurgeryInvariance`; the rest of
`Work.CoreTopology` does not (in particular `Work.CoreTopology.All` does not import it).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- The concrete `H₁(F ; ℚ)`-valued piece data attached to a parametrised torus: the `ℚ`-span of
the winding vectors of the closed curves of `F` lying in a region. -/
noncomputable def HomPieceData.ofWindingSpan (P : ParamTorus) : HomPieceData P (ℚ × ℚ) where
  hom := Work.SurgeryInvariance.WindingSpan P

@[simp] theorem HomPieceData.ofWindingSpan_hom (P : ParamTorus) :
    (HomPieceData.ofWindingSpan P).hom = Work.SurgeryInvariance.WindingSpan P := rfl

/-- The identification of the abstract predicate with the geometric one, for `WindingSpan`. -/
theorem HomPieceData.ofWindingSpan_hasEssentialLoop (P : ParamTorus) (U : Set R3) :
    (HomPieceData.ofWindingSpan P).HasEssentialLoop U ↔ P.ContainsEssentialLoop U :=
  Work.SurgeryInvariance.windingSpan_ne_bot_iff P U

/-- **Pardon's `doublebubble` with the concrete invariant `WindingSpan`.**

Let `Sint` be the interior of the original sphere, `H₁`, `H₂` the interiors of the two halves of
the double bubble and `W : ℝ → Submodule ℚ (ℚ × ℚ)` the invariant along the `2`-surgery family
(`W 0 = WindingSpan P Sint`, `W 1 = WindingSpan P H₁ ⊔ WindingSpan P H₂`).  Assume Pardon's
dichotomy for the pieces, the surgery dimension bounds, and that `F ∩ Sint` contains an essential
loop.  Then so does `F ∩ H_i` for `i = 1` or `i = 2`. -/
theorem double_bubble_windingSpan {P : ParamTorus}
    (W : ℝ → Submodule ℚ (ℚ × ℚ)) (Sint H₁ H₂ : Set R3)
    (hdich : ∀ U : Set R3, Work.SurgeryInvariance.WindingSpan P U = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan P U = ⊤)
    (hSess : P.ContainsEssentialLoop Sint)
    (hval : ∀ t : ℝ, W t = ⊥ ∨ W t = ⊤)
    (hstep : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Module.finrank ℚ ↥(W s) ≤ Module.finrank ℚ ↥(W t) + 1 ∧
      Module.finrank ℚ ↥(W t) ≤ Module.finrank ℚ ↥(W s) + 1)
    (hW0 : W 0 = Work.SurgeryInvariance.WindingSpan P Sint)
    (hdecomp : W 1 = Work.SurgeryInvariance.WindingSpan P H₁ ⊔
      Work.SurgeryInvariance.WindingSpan P H₂) :
    P.ContainsEssentialLoop H₁ ∨ P.ContainsEssentialLoop H₂ :=
  double_bubble_geometric (P := P) (A := ℚ × ℚ) (HomPieceData.ofWindingSpan P) W Sint H₁ H₂
    (HomPieceData.ofWindingSpan_hasEssentialLoop P) (by simp [Module.finrank_prod]) hdich hSess
    hval hstep hW0 hdecomp

end

end Work.CoreTopology
