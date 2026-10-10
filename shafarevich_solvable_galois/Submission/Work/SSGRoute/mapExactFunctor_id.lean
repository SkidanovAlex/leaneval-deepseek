import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.ext_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

theorem mapExactFunctor_id {G : Type} [Group G] {X Y : Rep.{0} SSGRoute.PTExt.Coeff G} {n : ℕ}
    (x : CategoryTheory.Abelian.Ext X Y n) :
    x.mapExactFunctor (CategoryTheory.Functor.id (Rep.{0} SSGRoute.PTExt.Coeff G)) = x := by
  have h := ext_mapExactFunctor_naturality_aux (C := Rep.{0} SSGRoute.PTExt.Coeff G)
    (F := 𝟭 (Rep.{0} SSGRoute.PTExt.Coeff G))
    (θ := 𝟙 (𝟭 (Rep.{0} SSGRoute.PTExt.Coeff G))) n X Y x
  simpa using h

end Work.SSGRoute
