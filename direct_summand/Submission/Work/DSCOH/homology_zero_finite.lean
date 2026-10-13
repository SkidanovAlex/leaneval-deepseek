import Mathlib

/-!
In degree `0` of a cochain complex of `A`-modules indexed by `ℕ`, the incoming differential
is `C.d 0 0 = 0`, so `H⁰(C)` is the `A`-module `ker (C.d 0 1)`; in particular it is finitely
generated as soon as that kernel is.
-/

open CategoryTheory

namespace Work.DSCOH

theorem homology_zero_finite {A : Type*} [CommRing A] (C : CochainComplex (ModuleCat A) ℕ)
    (h : Module.Finite A (LinearMap.ker (C.d 0 1).hom)) : Module.Finite A (C.homology 0) := by
  -- in degree `0` the shape `ComplexShape.up ℕ` has `prev 0 = 0` and `next 0 = 1`
  have hi : (ComplexShape.up ℕ).prev 0 = 0 :=
    ComplexShape.prev_eq_self' (ComplexShape.up ℕ) 0 (by intro k hk; simp at hk)
  have hk : (ComplexShape.up ℕ).next 0 = 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℕ) rfl
  -- `C.homology 0` is the degree-`0` homology of the short complex `C.X 0 ⟶ C.X 0 ⟶ C.X 1`
  -- whose first map is `C.d 0 0 = 0`
  have hf : (C.sc' 0 0 1).f = 0 := by
    rw [HomologicalComplex.shortComplexFunctor'_obj_f]
    exact C.shape 0 0 (by simp)
  -- hence it is the homology of a short complex with vanishing first map, and any such
  -- homology is the kernel of the second map, i.e. `ker (C.d 0 1)`
  let e1 : C.homology 0 ≅ (C.sc' 0 0 1).homology := C.homologyIsoSc' 0 0 1 hi hk
  let e2 : (C.sc' 0 0 1).homology ≅ Limits.kernel (C.d 0 1) :=
    ShortComplex.LeftHomologyData.homologyIso
      (ShortComplex.HomologyData.ofHasKernel (S := C.sc' 0 0 1) hf).left
  let e3 : Limits.kernel (C.d 0 1) ≅ ModuleCat.of A (LinearMap.ker (C.d 0 1).hom) :=
    ModuleCat.kernelIsoKer (C.d 0 1)
  let e : C.homology 0 ≅ ModuleCat.of A (LinearMap.ker (C.d 0 1).hom) := e1 ≪≫ e2 ≪≫ e3
  exact Module.Finite.equiv e.symm.toLinearEquiv

end Work.DSCOH
