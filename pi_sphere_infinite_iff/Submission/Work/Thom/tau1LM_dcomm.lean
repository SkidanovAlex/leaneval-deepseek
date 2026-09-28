import Mathlib
import Submission.Work.Thom.cupDeltaInfra
import Submission.Work.Thom.cupDescendMor_d_comm

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-!
# Commutation of the top component `tau1LM` of the transgression morphism with the differential

`Work.Thom.tau1LM X A U V n p t` is the `p`-th component of the descent, to the relative small
cochains `C^{U,V}(X,A)`, of the cup product with a relative cocycle `t` of degree `n`.  It is the
composite of the projection `C^{U,V}(X) ⟶ C^{U,V}(X,A)` (dualised) with the descended cup product
`cupDescend`.

The theorem `tau1LM_dcomm` shows that this is a map of complexes of degree `n`: cupping with a
*cocycle* commutes with the differentials.  The two ingredients are

* `cupDescend_d_comm` — the same identity for the descended cup map `cupDescend` on the small
  cochains of the cover, which is the Alexander–Whitney Leibniz rule
  `δ(ψ ⌣ t) = (δψ) ⌣ t` for a cocycle `t` (this is `cupDescendMor_d_comm`);
* the naturality of the dualised projection `dualComplexMap` (`HomologicalComplex.Hom.comm`).
-/

namespace Work.Thom

open CategoryTheory CategoryTheory.Limits Work.Cohomology

/-- The descended cup product `cupDescend` agrees with the version phrased through the
elementwise description `cupDescendMor`. -/
lemma cupDescend_apply (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n)
    (ψ : (dualComplex ℤ (smallChains U V)).X p) :
    ModuleCat.Hom.hom (cupDescend X A U V n p t ht) ψ
      = ModuleCat.Hom.hom (cupDescendMor X A U V n p t ht ψ) := rfl

/-- **The descended cup product with a relative cocycle commutes with the differentials.**  Both
sides are maps `C^{U,V}_p(X) ⟶ Hom(C^{U,V}_{(p+1)+n}(X,A), ℤ)`; the identity is the Leibniz rule
`δ(ψ ⌣ t) = (δψ) ⌣ t`, transported along the equality of degrees `(p+1)+n = p+n+1`. -/
lemma cupDescend_d_comm (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n)
    (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) :
    cupDescend X A U V n p t ht ≫ (dualComplex ℤ (relMVTopC X A U V)).d (p+n) ((p+1)+n)
      = (dualComplex ℤ (smallChains U V)).d p (p+1) ≫ cupDescend X A U V n (p+1) t ht := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [cupDescend_apply]
  rw [cupDescendMor_d_comm X A U V n p t ht hdt ψ]
  conv_lhs => rw [← HomologicalComplex.d_comp_XIsoOfEq_inv (dualComplex ℤ (relMVTopC X A U V))
      (by omega : (p+1)+n = p+n+1) (p+n)]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **The top component of the transgression morphism is a map of complexes of degree `n`.** -/
theorem tau1LM_dcomm (X : TopCat) (A U V : Set X) (n i : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (ht : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0) :
    CategoryTheory.CategoryStruct.comp (Work.Thom.tau1LM X A U V n i t)
        ((Work.Thom.Tsq.shK (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)) n).d i (i + 1))
      = CategoryTheory.CategoryStruct.comp
          ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X ∅ U V)).d i (i + 1))
          (Work.Thom.tau1LM X A U V n (i + 1) t) := by
  have key := cupDescend_d_comm X A U V n i t.1 t.2 ht
  have hq := HomologicalComplex.Hom.comm (dualComplexMap ℤ (smallChains U V)
      (relMVTopC X ∅ U V) (cokernel.π (smallInToSmall U V ∅))) i (i+1)
  simp only [Work.Thom.tau1LM, Work.Thom.Tsq.shK_d]
  rw [Category.assoc]
  rw [key]
  rw [← Category.assoc]
  rw [hq]
  rw [Category.assoc]

end Work.Thom
