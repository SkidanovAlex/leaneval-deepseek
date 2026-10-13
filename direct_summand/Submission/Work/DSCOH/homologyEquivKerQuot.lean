import Mathlib

open CategoryTheory CategoryTheory.Limits

namespace Work.DSCOH

/-- The `q`-th cohomology of a cochain complex of `A`-modules is the quotient of the
kernel of the differential `d^q` by the image of `d^{q-1}` (viewed inside that kernel).

We first identify `C.homology q` with the homology of the short complex
`C.sc' (q-1) q (q+1)` (which is `C.X (q-1) ⟶ C.X q ⟶ C.X (q+1)`), using the canonical
isomorphism `HomologicalComplex.isoSc'`.  Then Mathlib's `ShortComplex.moduleCatHomologyIso`
describes the homology of a short complex of modules as the quotient of `ker g` by the image
of the induced map `ker g`; the range of that map is `comap (ker g).subtype (range f)`. -/
theorem homologyEquivKerQuot {A : Type*} [CommRing A] (C : CochainComplex (ModuleCat A) ℕ) (q : ℕ) :
    Nonempty (↥(C.homology q) ≃ₗ[A]
      (LinearMap.ker (C.d q (q + 1)).hom ⧸
        Submodule.comap (LinearMap.ker (C.d q (q + 1)).hom).subtype
          (LinearMap.range (C.d (q - 1) q).hom))) := by
  have hprev : (ComplexShape.up ℕ).prev q = q - 1 := by
    rcases q with _ | q <;> simp
  have hnext : (ComplexShape.up ℕ).next q = q + 1 := CochainComplex.next ℕ q
  let S := C.sc' (q - 1) q (q + 1)
  have hEq : S.moduleCatToCycles.range =
      Submodule.comap (S.g.hom.ker).subtype (S.f.hom.range) := by
    simpa only [ShortComplex.moduleCatToCycles] using
      LinearMap.range_codRestrict (S.g.hom.ker) (S.f.hom) (S.moduleCat_zero_apply)
  refine ⟨(((ShortComplex.homologyMapIso (C.isoSc' (q - 1) q (q + 1) hprev hnext)) ≪≫
    S.moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEq S.moduleCatToCycles.range _ hEq).toModuleIso).toLinearEquiv)⟩

end Work.DSCOH
