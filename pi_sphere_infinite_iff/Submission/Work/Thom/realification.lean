import Mathlib
import Submission.Work.Thom.exists_underlyingReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# The realification of a complex vector bundle (gluing-data model)

`Work.Thom.realification Z` is the **underlying real bundle** of a complex vector bundle `Z` given
by gluing data: the same base sets, index map and transition functions, the latter viewed as
`ℝ`-linear maps.  It is the first rung of the complexification layer
(`Submission/Work/Thom/README.md`, ADDENDUM 14) that leads to the Chern classes of a complex bundle
and then, via `p_i(E) = (-1)^i c_{2i}(E ⊗_ℝ ℂ)`, to the Pontryagin classes of a general real bundle.
-/

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {ι : Type}

/-- **The realification**: the underlying real vector bundle of a complex vector bundle given by
gluing data. -/
noncomputable def realification (Z : VectorBundleCore ℂ B F ι) : VectorBundleCore ℝ B F ι :=
  Classical.choose (exists_underlyingReal Z)

theorem realification_baseSet (Z : VectorBundleCore ℂ B F ι) :
    (realification Z).baseSet = Z.baseSet :=
  (Classical.choose_spec (exists_underlyingReal Z)).1

theorem realification_indexAt (Z : VectorBundleCore ℂ B F ι) :
    (realification Z).indexAt = Z.indexAt :=
  (Classical.choose_spec (exists_underlyingReal Z)).2.1

theorem realification_coordChange (Z : VectorBundleCore ℂ B F ι) (i j : ι) (b : B) :
    ⇑((realification Z).coordChange i j b) = ⇑(Z.coordChange i j b) :=
  (Classical.choose_spec (exists_underlyingReal Z)).2.2 i j b

end

end Work.Thom
