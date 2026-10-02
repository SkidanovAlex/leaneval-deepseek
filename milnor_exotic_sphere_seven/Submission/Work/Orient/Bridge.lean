import Mathlib
import Submission.Work.Orient.Closed
import Submission.Work.ThomBordism.Interface

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# ORIENT: the bridge to the notions of area THOM

This file shows that the notions of the ORIENT chapter are *literally* the fields of
`Work.ThomBordism.Man8` and `Work.ThomBordism.NullBordismFamily`:

* `Work.Orient.Man8.isFundClass` — the field `Work.ThomBordism.Man8.c_fund` is
  `Work.Orient.IsFundClass M 8 V.c`;
* `Work.Orient.Man8.ofOrientFamily` — conversely, a compact `C^∞` `8`-manifold with an orientation
  (a locally consistent family of local generators) is a `Man8`: existence of the fundamental class
  (`Work.Orient.exists_fundClass_of_isOrientFamily`);
* `Work.Orient.IsRelFundClass` is the property asserted by
  `Work.ThomBordism.NullBordismFamily.w_fund` — `Work.Orient.relPunct_eq_relChainsInclPunct` shows
  that the two maps defining it agree.

Nothing here is used by `Submission/Work/Orient/Closed.lean`; it is the interface that lets a
consumer replace a `Man8` by the ORIENT vocabulary (and conversely).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold ContDiff

namespace Work.Orient

noncomputable section

/-! ## `Man8.c_fund` is `IsFundClass` -/

/-- **The fundamental-class field of a `Man8` is `Work.Orient.IsFundClass`.** -/
theorem Man8.isFundClass (V : Work.ThomBordism.Man8) :
    IsFundClass (TopCat.of V.pt) 8 V.c :=
  V.c_fund

/-- **A compact `C^∞` `8`-manifold with an orientation is a `Man8`** (existence of the fundamental
class from a locally consistent family of local generators). -/
def Man8.ofOrientFamily (pt : Type) [TopologicalSpace pt]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) pt] [IsManifold (𝓡 8) ∞ pt] [CompactSpace pt]
    [T2Space pt] (γ : (x : pt) → LocH (TopCat.of pt) 8 x)
    (hγ : IsOrientFamily 8 (TopCat.of pt) γ) : Work.ThomBordism.Man8 where
  pt := pt
  c := Classical.choose (exists_fundClass_of_isOrientFamily 8 (by norm_num) (TopCat.of pt) γ hγ)
  c_fund := (Classical.choose_spec
    (exists_fundClass_of_isOrientFamily 8 (by norm_num) (TopCat.of pt) γ hγ)).2

/-! ## `w_fund` and the relative fundamental class -/

/-- **The two maps defining the relative fundamental class property agree**: the map used by
`Work.ThomBordism.NullBordismFamily.w_fund` and `Work.Orient.relPunct` are the same map of relative
chain complexes. -/
theorem relPunct_eq_relChainsInclPunct (W : TopCat) (B : Set W) (x : W) (hx : x ∉ B) :
    relPunct W B x hx = Work.ThomBordism.relChainsInclPunct W B x hx := by
  rfl

/-- **`NullBordismFamily.w_fund` is `Work.Orient.IsRelFundClass`.** -/
theorem NullBordismFamily.isRelFundClass {ι : Type} [Fintype ι]
    {F : ι → Work.ThomBordism.Man8} (W : Work.ThomBordism.NullBordismFamily ι F) :
    IsRelFundClass (TopCat.of W.W) 9 ((modelWithCornersEuclideanHalfSpace 9).boundary W.W) W.w := by
  intro x hx
  have h := W.w_fund x hx
  rw [show Submodule.span ℤ ({((HomologicalComplex.homologyMap
        (relPunct (TopCat.of W.W) ((modelWithCornersEuclideanHalfSpace 9).boundary W.W) x hx) 9) W.w)} :
        Set _)
      = Submodule.span ℤ ({((HomologicalComplex.homologyMap
          (Work.ThomBordism.relChainsInclPunct (TopCat.of W.W)
            ((modelWithCornersEuclideanHalfSpace 9).boundary W.W) x hx) 9) W.w)} : Set _)
      from by rw [relPunct_eq_relChainsInclPunct]]
  exact h

end

end Work.Orient
