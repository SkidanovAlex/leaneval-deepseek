import Mathlib
import Submission.Work.SSS.singularFibration

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial
open scoped SSet.modelCategoryQuillen

/-- **The right lifting property of `Sing p` against a horn inclusion whiskered by any simplicial
set.**  If `p` is a Serre fibration, then `sSingP p : sSing E ⟶ sSing B` is a Kan fibration
(`Work.SSS.singularFibration`), so it has the right lifting property against every anodyne
extension; the whiskering `X ◁ Λ[n+1,i].ι` of a horn inclusion with a simplicial set `X` is
anodyne (`SSet.anodyneExtensions.horn_ι` and `SSet.anodyneExtensions.whiskerLeft`), and
`SSet.anodyneExtensions = (fibrations _).llp` by definition, so applying the latter to the former
gives the result. -/
theorem hasLiftingProperty_whisker_horn {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (X : SSet.{0}) {n : ℕ} (i : Fin (n + 2)) :
    HasLiftingProperty (X ◁ (SSet.horn (n + 1) i).ι) (Work.SSS.sSingP p) := by
  have hfil : HomotopicalAlgebra.Fibration (Work.SSS.sSingP p) :=
    Work.SSS.singularFibration p hfib
  exact (SSet.anodyneExtensions.whiskerLeft
      (SSet.anodyneExtensions.horn_ι (n := n + 1) i) X)
    (Work.SSS.sSingP p) hfil.mem

end Work.SSS
