import Mathlib
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.Place
import Submission.Work.CurveBasics.Order.finite_support_ord

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.SpecLin.Setup

/-- The complement of a nonempty open subset of a curve is finite.

`C.left` is irreducible and noetherian of topological Krull dimension at most one, so a proper
closed subset has dimension zero and is therefore finite.  (The affineness of `W` is not needed,
but it is the shape in which the caller uses it: the complement of the given affine chart is the
extra set of points that the auxiliary chart of the two-chart globalisation has to cover.) -/
theorem finite_compl_affineOpen {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W] :
    ((W : Set C.left)ᶜ).Finite := by
  classical
  obtain ⟨w⟩ := (inferInstance : Nonempty W)
  have hgen : genericPoint C.left ∈ (W : Set C.left) :=
    (genericPoint_spec C.left).mem_open_set_iff W.isOpen |>.mpr ⟨w.1, trivial, w.2⟩
  refine Work.CurveBasics.Order.finite_of_isClosed_of_genericPoint_notMem _
    W.isOpen.isClosed_compl ?_ (fun z => C.coheight_le_one z)
  exact Set.notMem_compl_iff.mpr hgen

end Work.SpecLin.Setup
