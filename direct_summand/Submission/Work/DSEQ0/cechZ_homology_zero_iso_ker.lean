import Mathlib
import Submission.Work.DSMap.Map

universe a

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Limits

/-- **The degree-`0` cohomology of the `ℤ`-indexed Čech complex is the kernel of `d 0 1`.**

The Čech complex `DSMap.cechZ A X f U` is the extension of the `ℕ`-indexed complex
`DSMap.cech A X f U` by zero in negative degrees.  Hence it is `0` in degree `-1`, so
the degree-`0` homology — the cycles modulo the boundaries, and there are no boundaries
in the extended complex — is the kernel of the degree-`0` differential `d 0 1`. -/
theorem cechZ_homology_zero_iso_ker (A : Type a) [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} (U : ι → X.Opens) :
    Nonempty ((DSMap.cechZ A X f U).homology 0 ≃ₗ[A]
      LinearMap.ker ((DSMap.cech A X f U).d 0 1).hom) := by
  set K := DSMap.cech A X f U with hK
  -- (1) the extension of a complex by zero in negative degrees is a quasi-isomorphism in
  -- degrees that lie in the image of the embedding, here `0`.
  have e1 : (DSMap.cechZ A X f U).homology 0 ≅ K.homology 0 :=
    HomologicalComplex.extendHomologyIso K ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl
  -- (2) `K.homology 0` is the homology of the short complex `K.d 0 0 → K.d 0 1`, and the
  -- first differential vanishes, so the homology is the kernel of the second.
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 :=
    ComplexShape.prev_eq_self' _ _ (by intro k; simp [ComplexShape.up])
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := ComplexShape.next_eq' _ rfl
  have hf : (K.sc' 0 0 1).f = 0 := by
    show K.d 0 0 = 0
    exact K.shape 0 0 (by simp [ComplexShape.up])
  have e2 : K.homology 0 ≅ kernel (K.d 0 1) :=
    (HomologicalComplex.homologyIsoSc' K 0 0 1 hprev hnext) ≪≫
      (ShortComplex.LeftHomologyData.ofHasKernel (K.sc' 0 0 1) hf).homologyIso
  -- (3) the categorical kernel in `ModuleCat A` is the module-theoretic kernel.
  have e3 : kernel (K.d 0 1) ≅ ↧((K.d 0 1).hom.ker) := ModuleCat.kernelIsoKer (K.d 0 1)
  exact ⟨(e1 ≪≫ e2 ≪≫ e3).toLinearEquiv⟩

end Work.DSEQ0
