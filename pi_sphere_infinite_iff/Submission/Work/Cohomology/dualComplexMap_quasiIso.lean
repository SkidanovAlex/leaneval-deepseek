import Mathlib
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Cohomology.homotopyEquivDual
import Submission.Work.Cohomology.dualComplex_acyclic_of_acyclic
import Submission.Work.Cohomology.exists_homotopy_of_acyclic
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.RelMVDefs

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.Cohomology

/-- **The dual of a quasi-isomorphism between degreewise projective chain complexes of
`ℤ`-modules is a quasi-isomorphism.**

The point is that a quasi-isomorphism between chain complexes concentrated in non-negative
degrees whose terms are projective is a *homotopy equivalence*
(`ChainComplex.quasiIso_iff_of_projective`), and the `ℤ`-dual of a homotopy equivalence is a
homotopy equivalence (`Work.Cohomology.homotopyEquivDual`), whence a quasi-isomorphism. -/
theorem dualComplexMap_quasiIso {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D)
    (hC : ∀ n, Module.Projective ℤ ↥(C.X n)) (hD : ∀ n, Module.Projective ℤ ↥(D.X n))
    (h : ∀ n, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ n)) (n : ℕ) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap ℤ C D φ) n) := by
  haveI hprojC : ∀ n, CategoryTheory.Projective (C.X n) := fun n => by
    haveI := hC n; infer_instance
  haveI hprojD : ∀ n, CategoryTheory.Projective (D.X n) := fun n => by
    haveI := hD n; infer_instance
  -- `φ` is a quasi-isomorphism
  have hq : QuasiIso φ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact h i
  -- hence a homotopy equivalence, because both complexes consist of projectives
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective φ).mp hq
  -- the two composites used to dualise the homotopy equivalence
  have hcomp1 : (dualComplexMap ℤ C D φ) ≫ (dualComplexMap ℤ D C e.inv)
      = dualComplexMap ℤ D D (e.inv ≫ e.hom) := by
    rw [← he, ← dualComplexMap_comp (R := ℤ) (f := e.inv) (g := e.hom)]
  have hcomp2 : (dualComplexMap ℤ D C e.inv) ≫ (dualComplexMap ℤ C D φ)
      = dualComplexMap ℤ C C (e.hom ≫ e.inv) := by
    rw [← he, ← dualComplexMap_comp (R := ℤ) (f := e.hom) (g := e.inv)]
  -- dualising the homotopy equivalence
  let ee : HomotopyEquiv (dualComplex ℤ D) (dualComplex ℤ C) :=
    { hom := dualComplexMap ℤ C D φ
      inv := dualComplexMap ℤ D C e.inv
      homotopyHomInvId := by
        rw [hcomp1]
        simpa [dualComplexMap_id] using (dualHomotopy ℤ e.homotopyInvHomId).symm
      homotopyInvHomId := by
        rw [hcomp2]
        simpa [dualComplexMap_id] using (dualHomotopy ℤ e.homotopyHomInvId).symm }
  haveI : QuasiIso ee.hom := HomotopyEquiv.quasiIso_hom ee
  exact inferInstanceAs (CategoryTheory.IsIso (HomologicalComplex.homologyMap ee.hom n))

end Work.Cohomology
