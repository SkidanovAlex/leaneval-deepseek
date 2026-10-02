import Mathlib
import Submission.Work.Cohomology.pi0Projection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Limits Simplicial
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem pi0Proj_sgen_of_mem (T : TopCat) (c : SSet.π₀ (TopCat.toSSet.obj T))
    (s : (TopCat.toSSet.obj T).obj (Opposite.op (SimplexCategory.mk 0)))
    (hc : SSet.π₀.mk s = c) :
    Work.Cohomology.pi0Proj T c (Work.Cohomology.sgen ℤ T s) = 1 := by
  classical
  have key : SSet.ιChainComplex (TopCat.toSSet.obj T) (R := ModuleCat.of ℤ ℤ) s ≫
      pi0ProjMor T c = 𝟙 (ModuleCat.of ℤ ℤ) := by
    rw [show pi0ProjMor T c = SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj T)
        (ModuleCat.of ℤ ℤ) ≫
        Sigma.desc (fun d : SSet.π₀ (TopCat.toSSet.obj T) =>
          if d = c then 𝟙 (ModuleCat.of ℤ ℤ) else 0) from rfl]
    rw [← Category.assoc, SSet.π₀.comp_fromChainComplexXZero, Sigma.ι_desc, hc, if_pos rfl]
  have h := congrArg ModuleCat.Hom.hom key
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  have h1 := LinearMap.congr_fun h 1
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h1
  exact h1

end

end Work.Cohomology
