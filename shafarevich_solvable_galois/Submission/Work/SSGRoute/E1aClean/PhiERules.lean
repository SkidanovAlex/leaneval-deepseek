import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.PT.PhiEgen_compat
import Submission.Work.SSGRoute.PT.e1aBetaCan_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Rules for the `PhiE`-generators of the canonical `E1c` dictionary

`Work.SSGRoute.PT.PhiEgen X Z : Ext⁰(kernel (freeCover X), Z) →+ Ext¹(X, Z)` is the `Ext`-side map
of the canonical `E1c` dictionary (the connecting class of the canonical presentation of `X`).  The
comparison square of the E1a node (`Work.SSGRoute.E1aClean.comparisonSquareFin`) compares the global
dictionary with the local one on these generators, and needs two rules:

* `PhiEgen_postcomp` — postcomposition with a coefficient map commutes with `PhiEgen`
  (a consequence of `Ext.comp_assoc_of_third_deg_zero`);
* `PhiEgen_res_compat` (`PT/PhiEgen_compat.lean`) — the group-change rule, already on disk.

Together they compute the image of the *localisation* of a `PhiE`-generator under the local
transport, which is the input of the comparison square.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

/-- **`PhiEgen` commutes with postcomposition in the coefficient.**  For a morphism of coefficient
representations `u : Z ⟶ Z'` and an `Ext⁰`-class `w` on the syzygy of `X`, the `PhiE`-generator of
`w` pushed along `u` is the `PhiE`-generator of `w` pushed along `u`. -/
theorem PhiEgen_postcomp {G : Type} [Group G] [Fintype G] (X Z Z' : Rep.{0} Coeff G) (u : Z ⟶ Z')
    (w : CategoryTheory.Abelian.Ext (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)) Z 0) :
    Work.SSGRoute.PT.PhiEgen X Z'
        (CategoryTheory.Abelian.Ext.comp w (CategoryTheory.Abelian.Ext.mk₀ u) (zero_add 0))
      = CategoryTheory.Abelian.Ext.comp (Work.SSGRoute.PT.PhiEgen X Z w)
          (CategoryTheory.Abelian.Ext.mk₀ u) (add_zero 1) := by
  rw [Work.SSGRoute.PT.PhiEgen_apply, Work.SSGRoute.PT.PhiEgen_apply]
  exact (CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero
    (Work.SSGRoute.freeCoverSES_shortExact X).extClass w
    (CategoryTheory.Abelian.Ext.mk₀ u) (by norm_num : 1 + 0 = 1)).symm

/-- The same rule in the form in which the comparison square consumes it: a `PhiE`-generator
postcomposed with a coefficient map is the `PhiE`-generator of the coeffient-changed element. -/
theorem PhiEgen_postcomp' {G : Type} [Group G] [Fintype G] (X Z Z' : Rep.{0} Coeff G) (u : Z ⟶ Z')
    (w : CategoryTheory.Abelian.Ext (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)) Z 0) :
    CategoryTheory.Abelian.Ext.comp (Work.SSGRoute.PT.PhiEgen X Z w)
        (CategoryTheory.Abelian.Ext.mk₀ u) (add_zero 1)
      = Work.SSGRoute.PT.PhiEgen X Z'
          (CategoryTheory.Abelian.Ext.comp w (CategoryTheory.Abelian.Ext.mk₀ u) (zero_add 0)) :=
  (PhiEgen_postcomp X Z Z' u w).symm

end Work.SSGRoute.E1aClean
