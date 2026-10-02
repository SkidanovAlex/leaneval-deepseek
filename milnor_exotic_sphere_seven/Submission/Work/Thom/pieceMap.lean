import Mathlib
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.exists_pieceMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The canonical map on the pieces of the total space over a subset of the base

`Work.Thom.punctMap` is the map of punctured total spaces; for an *arbitrary* subset `W ⊆ B` of the
base there is the same map on the pieces, `p ↦ (f p.1, p.2)`, whose existence is
`Work.Thom.exists_pieceMap`.  `Work.Thom.pieceMap` is its (unique, hence canonical) witness; it is
the map along which the chart local Thom data `Work.Thom.localThomOfChart` has to be natural
(G2b.1 of `README.md` ADDENDUM 21).
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {F : Type}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}

/-- **The canonical map of the pieces over `W' ⊆ B'` and `W ⊆ B`** with `f '' W' ⊆ W`: on the
underlying bundles it is `⟨f p.1, p.2⟩`. -/
noncomputable def pieceMap (Z : RealBundle B F ι) (f : C(B', B)) {W : Set B} {W' : Set B'}
    (hWf : ∀ x ∈ W', f x ∈ W) :
    C(↥((bundleComap Z f).proj ⁻¹' W'), ↥(Z.proj ⁻¹' W)) :=
  Classical.choose (exists_pieceMap Z f hWf)

/-- The defining equation of `Work.Thom.pieceMap`. -/
theorem pieceMap_apply (Z : RealBundle B F ι) (f : C(B', B)) {W : Set B} {W' : Set B'}
    (hWf : ∀ x ∈ W', f x ∈ W) (p : ↥((bundleComap Z f).proj ⁻¹' W')) :
    (pieceMap Z f hWf p : Z.TotalSpace) = (⟨f p.1.1, p.1.2⟩ : Z.TotalSpace) :=
  Classical.choose_spec (exists_pieceMap Z f hWf) p

end

end Work.Thom
