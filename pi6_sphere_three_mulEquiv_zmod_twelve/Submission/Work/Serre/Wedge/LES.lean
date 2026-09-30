import Mathlib
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.homologyContractible

/-!
# Two extractions from the long exact sequence of a pair

Elementary consequences of the exactness of the long exact sequence of a pair of spaces
(`Work.Cohomology.hPair_exact₁/₂/₃`) used in the computation of the homology of the wedge of
spheres:

* `isIso_homologyMap_rel_of_isZero`: if `H_{q+1}(A)` and `H_q(A)` vanish, then the map
  `H_{q+1}(X) ⟶ H_{q+1}(X,A)` is an isomorphism;
* `isZero_homology_of_isZero_rel_of_isZero`: if `H_q(A)` and `H_q(X,A)` vanish, then `H_q(X) = 0`;
* `isZero_homology_singleton`: the homology of a point vanishes in positive degrees.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.Wedge

noncomputable section

/-- **If `H_{q+1}(A)` and `H_q(A)` vanish then `H_{q+1}(X) ⟶ H_{q+1}(X,A)` is an isomorphism.** -/
theorem isIso_homologyMap_rel_of_isZero (X : TopCat) (A : Set X) (q : ℕ)
    (h1 : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of A)).homology (q + 1)))
    (h2 : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of A)).homology q)) :
    IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains X A)) (q + 1)) := by
  have hf : (ShortComplex.mk
      (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) (q + 1))
      (HomologicalComplex.homologyMap (cokernel.π (Work.Cohomology.inclChains X A)) (q + 1))
      (by rw [← HomologicalComplex.homologyMap_comp, cokernel.condition,
        HomologicalComplex.homologyMap_zero])).f = 0 := h1.eq_of_src _ 0
  haveI hmono : Mono (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains X A)) (q + 1)) :=
    (ShortComplex.exact_iff_mono _ hf).1 (Work.Cohomology.hPair_exact₂ X A (q + 1))
  have hg : (ShortComplex.mk (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains X A)) (q + 1))
      (Work.Cohomology.hPairδ X A q) (Work.Cohomology.hPair_comp_δ X A q)).g = 0 :=
    h2.eq_of_tgt _ 0
  haveI hepi : Epi (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains X A)) (q + 1)) :=
    (ShortComplex.exact_iff_epi _ hg).1 (Work.Cohomology.hPair_exact₃ X A q)
  exact isIso_of_mono_of_epi _

/-- **If `H_q(A)` and `H_q(X,A)` vanish then `H_q(X) = 0`.** -/
theorem isZero_homology_of_isZero_rel_of_isZero (X : TopCat) (A : Set X) (q : ℕ)
    (h1 : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of A)).homology q))
    (h2 : IsZero ((Work.Cohomology.relChains X A).homology q)) :
    IsZero ((Work.Cohomology.singularChains ℤ X).homology q) := by
  have hf : (ShortComplex.mk
      (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) q)
      (HomologicalComplex.homologyMap (cokernel.π (Work.Cohomology.inclChains X A)) q)
      (by rw [← HomologicalComplex.homologyMap_comp, cokernel.condition,
        HomologicalComplex.homologyMap_zero])).f = 0 := h1.eq_of_src _ 0
  haveI hmono : Mono (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains X A)) q) :=
    (ShortComplex.exact_iff_mono _ hf).1 (Work.Cohomology.hPair_exact₂ X A q)
  have hg : HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains X A)) q = 0 := h2.eq_of_tgt _ 0
  rw [IsZero.iff_id_eq_zero]
  refine (cancel_mono (HomologicalComplex.homologyMap
    (cokernel.π (Work.Cohomology.inclChains X A)) q)).mp ?_
  rw [hg, Category.id_comp]
  simp

/-- **The homology of the one-point space vanishes in positive degrees.** -/
theorem isZero_homology_singleton (X : TopCat) (b : X) (k : ℕ) (hk : 1 ≤ k) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ({b} : Set X))).homology k) :=
  Work.Cohomology.homologyContractible k hk

end

end Work.Serre.Wedge
