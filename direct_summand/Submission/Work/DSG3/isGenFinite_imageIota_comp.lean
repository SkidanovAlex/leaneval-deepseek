import Mathlib
import Submission.Work.DSG3.Basic

namespace Work.DSG3

open CategoryTheory AlgebraicGeometry in
lemma isGenFinite_imageIota_comp (A : Type*) [CommRing A] [IsDomain A] (X : AlgebraicGeometry.Scheme)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [AlgebraicGeometry.IsProper f] (x : X)
    (hx : f x = DSMap.genericPointOfSpec A)
    (hmin : closure ({x} : Set X) ∩ f ⁻¹' {DSMap.genericPointOfSpec A} = {x}) :
    DSMap.IsGenFinite A ((X.fromSpecResidueField x).imageι ≫ f) := by
  -- `Z := image (Spec κ(x) ⟶ X) ⟶ Spec A` is proper, and by `hmin` its fibre over the
  -- generic point `η` of `Spec A` is a single point, hence finite. Stacks 02UP then
  -- spreads finiteness out to an open neighbourhood of `η`, which contains some `D(g)`.
  have hrange : Set.range (X.fromSpecResidueField x).imageι = closure ({x} : Set X) :=
    DSMap.range_imageι_fromSpecResidueField x
  have hinj : Function.Injective (X.fromSpecResidueField x).imageι :=
    (X.fromSpecResidueField x).imageι.isClosedEmbedding.injective
  have hfin : (((X.fromSpecResidueField x).imageι ≫ f) ⁻¹' {DSMap.genericPointOfSpec A}).Finite := by
    refine Set.Subsingleton.finite fun a ha b hb => ?_
    have key : ∀ c, c ∈ ((X.fromSpecResidueField x).imageι ≫ f) ⁻¹' {DSMap.genericPointOfSpec A} →
        (X.fromSpecResidueField x).imageι c = x := by
      intro c hc
      have hmem : (X.fromSpecResidueField x).imageι c ∈
          Set.range (X.fromSpecResidueField x).imageι ∩ f ⁻¹' {DSMap.genericPointOfSpec A} := by
        refine ⟨Set.mem_range_self c, ?_⟩
        show f ((X.fromSpecResidueField x).imageι c) = DSMap.genericPointOfSpec A
        rw [← Scheme.Hom.comp_apply]
        exact hc
      rw [hrange, hmin] at hmem
      exact hmem
    exact hinj ((key a ha).trans (key b hb).symm)
  obtain ⟨V, hVmem, hVfin⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton
      ((X.fromSpecResidueField x).imageι ≫ f) (DSMap.genericPointOfSpec A) hfin
  obtain ⟨g, hg, hsub⟩ := DSMap.exists_ne_zero_basicOpen_subset (A := A) hVmem
  exact ⟨g, hg, DSMap.isFinite_morphismRestrict_of_le _ hsub hVfin⟩

end Work.DSG3
