import Mathlib
import Submission.Work.ThomBordism.eCohKernel
import Submission.Work.ThomBordism.relChainsFree
import Submission.Work.Cohomology.relCochainDual

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Integral relative homology from relative cohomology

If `Hⁿ(X,A;ℤ) ≅ ℤ`, `Hⁿ⁺¹(X,A;ℤ) = 0` and the relative homology of the pair `(X,A)` is finitely
generated in every degree, then `Hₙ(X,A) ≅ ℤ`.

The relative cochains are the duals of the relative chains (`Work.Cohomology.relCochainDual`), and
the universal coefficient comparison map `Hⁿ(Hom(C,ℤ)) ⟶ Hom(Hₙ(C),ℤ)` has torsion kernel
(`Work.ThomBordism.eCoh_ker_torsion`); vanishing of `Hⁿ⁺¹` makes `Hₙ` torsion free and the
finiteness hypothesis makes it free, after which a free `ℤ`-module with dual `ℤ` is `ℤ`
(`Work.ThomBordism.freeOfDualInt`).  All of this is assembled in
`Work.ThomBordism.homology_int_of_dual_int`.
-/

namespace Work.ThomBordism

open CategoryTheory CategoryTheory.Limits

theorem relHomologyIntOfCoh {X : TopCat} {A : Set X} {n : ℕ}
    (hfin : ∀ j, Module.Finite ℤ ↥((Work.Cohomology.relChains X A).homology j))
    (hC : Nonempty ((Work.Cohomology.relComplex ℤ X A).homology n ≅ ModuleCat.of ℤ ℤ))
    (hC0 : CategoryTheory.Limits.IsZero ((Work.Cohomology.relComplex ℤ X A).homology (n + 1))) :
    Nonempty ((Work.Cohomology.relChains X A).homology n ≅ ModuleCat.of ℤ ℤ) := by
  -- the relative cochains are the duals of the relative chains
  obtain ⟨e⟩ := Work.Cohomology.relCochainDual X A
  obtain ⟨f⟩ := hC
  have hC' : Nonempty
      ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).homology n
        ≅ ModuleCat.of ℤ ℤ) :=
    ⟨(HomologicalComplex.homologyMapIso e n).symm ≪≫ f⟩
  have hC0' : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).homology (n + 1)) :=
    CategoryTheory.Limits.IsZero.of_iso hC0 (HomologicalComplex.homologyMapIso e (n + 1)).symm
  exact homology_int_of_dual_int (Work.Cohomology.relChains X A)
    (Work.Cohomology.relChains_X_free X A) hfin n hC' hC0'

end Work.ThomBordism
