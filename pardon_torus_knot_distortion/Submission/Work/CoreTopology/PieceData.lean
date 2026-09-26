import Submission.Work.CoreTopology.Disk

/-!
# Homological data of the pieces of a torus

Pardon's proof of the "sphere family" and "double bubble" lemmas is phrased in terms of the
subgroup

  `im(H₁(F ∩ int S_t ; ℚ) → H₁(F ; ℚ)) ≤ H₁(F ; ℚ)`

attached to the portion `F ∩ int(S_t)` of the surface `F` lying inside a family of spheres
`S_t`.  Two facts are used:

* a piece cut out by curves that are *inessential* in `F` has invariant either `0` or the
  whole of `H₁(F)` (Pardon's `dim = 0` or `2g` dichotomy);
* the invariant is unchanged while `S_t` varies without surgery, and each surgery changes it
  by at most `1`.

This file packages the first piece of vocabulary: an assignment of an abstract
`H₁(F ; ℚ)`-submodule to every region of `ℝ³` for a given parametrised torus `P`, together with
the predicates "contains an essential loop" and the dichotomy.  The algebraic-topology content
(the actual construction of the map on homology) enters only through these hypotheses, and the
identification with the geometric predicate `P.ContainsEssentialLoop` is the hypothesis
`hlink` of the double-bubble lemmas.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- Homological data for Pardon's argument on the parametrised torus `P`: `A` is `H₁(F ; ℚ)`,
and `hom U` is the image of `H₁(F ∩ U ; ℚ)` in `H₁(F ; ℚ)` for a region `U ⊆ ℝ³`. -/
structure HomPieceData (P : ParamTorus) (A : Type*) [AddCommGroup A] [Module ℚ A] where
  /-- The image of `H₁(F ∩ U ; ℚ) → H₁(F ; ℚ)`. -/
  hom : Set R3 → Submodule ℚ A

namespace HomPieceData

variable {P : ParamTorus} {A : Type*} [AddCommGroup A] [Module ℚ A]

/-- The region `U` **contains an essential loop of `F`**: the image of
`H₁(F ∩ U ; ℚ) → H₁(F ; ℚ)` is nonzero.  For a torus `F`, this is equivalent to `F ∩ U`
containing a loop of nonzero winding vector (equivalently, a loop that is not null-homotopic in
`F`), because a loop in `F ∩ U` mapping to `0` in `H₁(F ; ℚ)` has vanishing winding vector. -/
def HasEssentialLoop (H : HomPieceData P A) (U : Set R3) : Prop := H.hom U ≠ ⊥

/-- Pardon's dichotomy: for pieces cut out by curves inessential in `F`, the invariant is
either `0` (`⊥`) or the whole of `H₁(F ; ℚ)` (`⊤`); for a genus-`g` surface this is
`dim_ℚ im(H₁ → H₁(F)) = 0` or `2g`. -/
def Dichotomy (H : HomPieceData P A) : Prop := ∀ U : Set R3, H.hom U = ⊥ ∨ H.hom U = ⊤

theorem dichotomy_apply {H : HomPieceData P A} (h : H.Dichotomy) (U : Set R3) :
    H.hom U = ⊥ ∨ H.hom U = ⊤ := h U

theorem hasEssentialLoop_iff (H : HomPieceData P A) (U : Set R3) :
    H.HasEssentialLoop U ↔ H.hom U ≠ ⊥ := Iff.rfl

/-- A piece whose invariant is all of `H₁(F ; ℚ)` contains an essential loop (for
nontrivial `A`, as in the geometric situation where `A = H₁(F ; ℚ)` is nonzero). -/
theorem HasEssentialLoop.of_hom_eq_top [Nontrivial A] (H : HomPieceData P A)
    {U : Set R3} (h : H.hom U = ⊤) : H.HasEssentialLoop U := by
  rw [HasEssentialLoop, h]; exact top_ne_bot

end HomPieceData

end

end Work.CoreTopology
