import Mathlib
import Submission.Work.Serre.RatTower.Defs
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.Assembly.pullbackFst_serre
import Submission.Work.RatHurewicz.attachIncl_isOpenMap_range
import Submission.Work.RatHurewicz.AttachRange.AttachInclInj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.RatTower

noncomputable section

open Work.RatHurewicz

/-! ## The fibre of the base change, over `ℚ` -/

/-- **The fibre of the base change is the fibre of `p`.** -/
def fibrePullbackFstHomeo {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace Γ] (g : C(Γ, B)) (p : C(E, B)) (y : Γ) :
    Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y ≃ₜ Work.StemsB.fibre p (g y) where
  toFun x := ⟨x.1.1.2, by rw [← x.1.2]; exact congrArg g x.2⟩
  invFun e := ⟨⟨(y, e.1), e.2.symm⟩, rfl⟩
  left_inv x := by
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
    exact x.2.symm
  right_inv e := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem isZero_ratH_of_homeomorph {X Y : TopCat} (e : X ≃ₜ Y) (n : ℕ)
    (h : IsZero (ratH Y n)) : IsZero (ratH X n) := by
  haveI : IsIso (TopCat.isoOfHomeo e).hom := inferInstance
  haveI h1 : IsIso (Work.Cohomology.chainMap ℚ X Y (TopCat.isoOfHomeo e).hom) := inferInstance
  exact IsZero.of_iso h (HomologicalComplex.homologyMapIso
    (asIso (Work.Cohomology.chainMap ℚ X Y (TopCat.isoOfHomeo e).hom)) n)

theorem nonempty_ratH_zero_of_homeomorph {X Y : TopCat} (e : X ≃ₜ Y)
    (h : Nonempty (ratH Y 0 ≅ ModuleCat.of ℚ ℚ)) : Nonempty (ratH X 0 ≅ ModuleCat.of ℚ ℚ) := by
  haveI h1 : IsIso (Work.Cohomology.chainMap ℚ X Y (TopCat.isoOfHomeo e).hom) := inferInstance
  obtain ⟨e'⟩ := h
  exact ⟨HomologicalComplex.homologyMapIso
    (asIso (Work.Cohomology.chainMap ℚ X Y (TopCat.isoOfHomeo e).hom)) 0 ≪≫ e'⟩

end

end Work.Serre.RatTower
