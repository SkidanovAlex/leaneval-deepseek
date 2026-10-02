import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.ThomBordism.pdGeneral
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.Cohomology.pd_goodD_incl

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory

namespace Work.ThomBordism

theorem cohEightMan8 (V : Work.ThomBordism.Man8) [PathConnectedSpace V.pt] :
    Nonempty ((Work.Thom.Coh ℤ 8 V.X) ≅ ModuleCat.of ℤ ℤ) := by
  classical
  have hgood : Work.Cohomology.Good 8 V.c (Set.univ : Set V.X) isOpen_univ :=
    goodUniv_of_localGen (N := 8) (M := V.X) V.c (fun x => V.c_fund x) (by norm_num)
  have hbij : Function.Bijective (fun y : (Work.Cohomology.cochainC ℤ
        (TopCat.toSSet.obj V.X)).homology 8 =>
      (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj V.X) 8 0) y (Nat.add_zero 8 ▸ V.c)) :=
    Work.Cohomology.pd_capPair_of_good (N := 8) V.X V.c hgood 8 0 (Nat.add_zero 8)
  let F : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj V.X)).homology 8 →ₗ[ℤ]
      (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj V.X)).homology 0 :=
    { toFun := fun y => (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj V.X) 8 0) y (V.c)
      map_add' := by intro a b; simp
      map_smul' := by intro a b; simp }
  have hF : Function.Bijective ⇑F := by
    show Function.Bijective (fun y : (Work.Cohomology.cochainC ℤ
        (TopCat.toSSet.obj V.X)).homology 8 =>
      (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj V.X) 8 0) y (V.c))
    exact hbij
  exact ⟨LinearEquiv.toModuleIso (LinearEquiv.ofBijective F hF) ≪≫
    (asIso ((TopCat.toSSet.obj V.X).homology₀ε (ModuleCat.of ℤ ℤ)))⟩

end Work.ThomBordism
