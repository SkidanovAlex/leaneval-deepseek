import Mathlib

/-!
# Finiteness of the top cohomology of a cochain complex of modules

If `C` is a cochain complex of `A`-modules indexed by `ℕ` and the differential
`C.d j (j+1)` vanishes, then the `j`-th cohomology of `C` is the quotient of
`C.X j` by the image of `C.d (j-1) j`. Hence if that quotient is a finite
`A`-module, so is `C.homology j`.
-/

open CategoryTheory Limits

namespace Work.DSCOH

theorem homology_top_finite {A : Type*} [CommRing A] (C : CochainComplex (ModuleCat A) ℕ) {j : ℕ}
    (hj : 1 ≤ j) (hd : C.d j (j + 1) = 0)
    (h : Module.Finite A (↥(C.X j) ⧸ LinearMap.range (C.d (j - 1) j).hom)) :
    Module.Finite A (C.homology j) := by
  -- `C.homology j` is computed by the short complex `C.X (j-1) ⟶ C.X j ⟶ C.X (j+1)`
  have hprev : (ComplexShape.up ℕ).prev j = j - 1 :=
    ComplexShape.prev_eq' (c := ComplexShape.up ℕ) (ComplexShape.up_mk (j - 1) j (by omega))
  have hnext : (ComplexShape.up ℕ).next j = j + 1 :=
    ComplexShape.next_eq' (c := ComplexShape.up ℕ) (ComplexShape.up_mk j (j + 1) rfl)
  -- the second differential of that short complex vanishes
  have hg : (C.sc' (j - 1) j (j + 1)).g = 0 := hd
  -- hence its homology is the cokernel of the first differential
  have eH : (C.sc' (j - 1) j (j + 1)).homology ≅ cokernel (C.d (j - 1) j) :=
    (ShortComplex.LeftHomologyData.ofHasCokernel _ hg).homologyIso
  have e1 : C.homology j ≅ (C.sc' (j - 1) j (j + 1)).homology :=
    C.homologyIsoSc' (j - 1) j (j + 1) hprev hnext
  have e2 : cokernel (C.d (j - 1) j) ≅ ↧(↥(C.X j) ⧸ LinearMap.range (C.d (j - 1) j).hom) :=
    ModuleCat.cokernelIsoRangeQuotient (C.d (j - 1) j)
  exact Module.Finite.equiv (e2.symm ≪≫ eH.symm ≪≫ e1.symm).toLinearEquiv

end Work.DSCOH
