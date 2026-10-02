import Mathlib
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.uctDual_evaluation
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.CompactSupport

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

theorem kronH_isIso (X : TopCat)
    (hfree : ∀ n, Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ X).homology n)) (n : ℕ) :
    Function.Bijective (fun α : ↥((Work.Cohomology.singularCochainComplex ℤ X).homology n) =>
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n α) := by
  obtain ⟨e, he⟩ := Work.Cohomology.uctDual_evaluation (Work.Cohomology.singularChains ℤ X)
      (fun k => Work.Cohomology.projective_singularChains X k) hfree n
  simp only [Work.Cohomology.dval] at he
  have hkr : ∀ y : ↥((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homology n),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n y = e.hom.hom y := by
    intro y
    obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homologyπ n)).mp inferInstance y
    apply LinearMap.ext
    intro v
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homologyπ n)).mp inferInstance v
    have hα : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X)
        (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj X) n w) = 0 := by
      simp only [Work.Cohomology.cochainOfCycle]
      exact Work.Cohomology.cochainDiff_iCycles ℤ (TopCat.toSSet.obj X) n w
    have hcyc : Work.Cohomology.cocycleOf ℤ (TopCat.toSSet.obj X)
        (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj X) n w) hα = w := by
      apply Work.Cohomology.iCycles_injective ℤ (TopCat.toSSet.obj X) n
      rw [Work.Cohomology.iCycles_cocycleOf]
      simp only [Work.Cohomology.cochainOfCycle]
    have hcls : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homologyπ n w
        = Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj X)
            (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj X) n w) hα := by
      show (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homologyπ n w
        = (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homologyπ n
            (Work.Cohomology.cocycleOf ℤ (TopCat.toSSet.obj X)
              (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj X) n w) hα)
      rw [hcyc]
    have h1 : (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n
            ((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homologyπ n w))
          ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homologyπ n c)
        = (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj X) n w)
            ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).iCycles n c) := by
      rw [hcls, Work.Cohomology.kronH_apply ℤ (TopCat.toSSet.obj X)
            (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj X) n w) hα c]
    have h2 : e.hom.hom ((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homologyπ n w)
          ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homologyπ n c)
        = (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj X) n w)
            ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).iCycles n c) := he w c
    exact h1.trans h2.symm
  have hbij : Function.Bijective (fun α : ↥((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homology n) =>
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n α) := by
    rw [funext hkr]
    exact ConcreteCategory.bijective_of_isIso e.hom
  exact hbij

end

end Work.Cohomology
