import Mathlib
import Submission.Work.ThomBordism.Grassmann.Torsion.mvFiniteness
import Submission.Work.Cohomology.homotopyEquiv_prod_fst
import Submission.Work.ThomBordism.compactHomologyFinite

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-!
# Transfer of finite generation of homology

Small transport lemmas for `Module.Finite ℤ (H_n(·;ℤ))`:

* `moduleFinite_homology_of_homotopyEquivCM` — along a `ContinuousMap.HomotopyEquiv`;
* `moduleFinite_homology_of_homeomorphCM` — along a homeomorphism;
* `moduleFinite_homology_of_homotopyEquivCM_prod` — the product form.

These are thin wrappers around `Work.ThomBordism.Grassmann.Torsion.moduleFinite_homology_of_homotopyEquiv`
(`TopCat.Homotopy` is definitionally `ContinuousMap.Homotopy`).
-/

open CategoryTheory
open ContinuousMap

namespace Work.ThomBordism.Grassmann.Torsion

noncomputable section

/-- **Finite generation of homology transfers along a `ContinuousMap.HomotopyEquiv`.** -/
theorem moduleFinite_homology_of_homotopyEquivCM {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ)
    (hfin : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology n)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology n) :=
  moduleFinite_homology_of_homotopyEquiv (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    (Classical.choice e.left_inv) (Classical.choice e.right_inv) n hfin

/-- **Finite generation of homology transfers along a homeomorphism.** -/
theorem moduleFinite_homology_of_homeomorphCM {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ)
    (hfin : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology n)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology n) :=
  moduleFinite_homology_of_homotopyEquivCM (e.toHomotopyEquiv) n hfin

/-- `H_*(X × Y)` is finitely generated in every degree when `Y` is contractible and `H_*(Y)` is
finitely generated. -/
theorem homologyFinite_prod_contractible {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] (n : ℕ)
    (h : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology n)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of (X × Y))).homology n) := by
  obtain ⟨e⟩ := Work.Cohomology.homotopyEquiv_prod_fst Y X
  have hYX : Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Y × X))).homology n) :=
    moduleFinite_homology_of_homotopyEquivCM e.symm n h
  exact moduleFinite_homology_of_homeomorphCM (Homeomorph.prodComm Y X) n hYX

/-- The singular homology of the sphere `S^r` is finitely generated in every degree. -/
theorem sphereHomologyFinite (r n : ℕ) : Module.Finite ℤ
    ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (r + 1))) 1))).homology n) := by
  exact Work.ThomBordism.compactHomologyFinite (n := r) (k := n)
    (X := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (r + 1))) 1))

end

end Work.ThomBordism.Grassmann.Torsion
