import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.singularCohomology_zero

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Limits Simplicial

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- An isomorphism of `R`-modules, regarded as a linear equivalence of the underlying modules. -/
def moduleIsoToLinearEquiv {R : Type} [Ring R] {M N : ModuleCat R} (e : M ≅ N) :
    M ≃ₗ[R] N :=
  LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)

/-- The underlying linear map of the dual differential is the transpose of the differential. -/
lemma dualDifferential_hom (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    (dualDifferential R X n).hom = ((singularChains R X).d (n + 1) n).hom.dualMap := by
  ext f
  rw [LinearMap.dualMap_apply']
  rfl

/-- The zeroth singular cohomology is the kernel of the zeroth differential of the cochain
complex. -/
theorem singularCohomology_zero_iso_ker (R : Type) [CommRing R] (X : TopCat) :
    Nonempty (singularCohomology R 0 X ≅
      ModuleCat.of R (LinearMap.ker (dualDifferential R X 0).hom)) := by
  let K := singularCochainComplex R X
  have : K.HasHomology 0 := inferInstance
  have hf : (K.sc 0).f = 0 := rfl
  have c1 : singularCohomology R 0 X ≅ K.cycles 0 :=
    (ShortComplex.asIsoHomologyπ (K.sc 0) hf).symm
  have c2 : K.cycles 0 ≅ (K.sc' 0 0 1).cycles := K.cyclesIsoSc' 0 0 1 (by simp) (by simp)
  have c3 : (K.sc' 0 0 1).cycles ≅ kernel (K.d 0 1) := ShortComplex.cyclesIsoKernel _
  have hd : K.d 0 1 = dualDifferential R X 0 := by
    simp only [K, singularCochainComplex, CochainComplex.of, CochainComplex.of.d]
    rfl
  rw [hd] at c3
  have c4 : kernel (dualDifferential R X 0) ≅
      ModuleCat.of R (LinearMap.ker (dualDifferential R X 0).hom) :=
    ModuleCat.kernelIsoKer _
  exact ⟨c1 ≪≫ c2 ≪≫ c3 ≪≫ c4⟩

/-- Degree-zero universal coefficients: the zeroth singular cohomology of a space is the `R`-dual of
its zeroth singular homology.  (At degree zero the universal coefficient sequence degenerates,
because the dual complex has `H⁰ = ker d⁰ = Hom(coker d₁, R)`.) -/
theorem singularCohomology_zero_Hom (R : Type) [CommRing R] (X : TopCat) :
    Nonempty (Work.Cohomology.singularCohomology R 0 X ≅
      ModuleCat.of R
        ((((singularHomologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).obj X) →ₗ[R] R)) := by
  obtain ⟨e1⟩ := singularCohomology_zero_iso_ker R X
  let C := singularChains R X
  let co : ModuleCat R := cokernel (C.d 1 0)
  let op : ModuleCat R := C.opcycles 0
  let H : ModuleCat R := C.homology 0
  have hdual : (dualDifferential R X 0).hom = (C.d 1 0).hom.dualMap := by
    rw [dualDifferential_hom]
  -- `H⁰ = ker (d₁ᴴ)`
  have e_a : LinearMap.ker ((dualDifferential R X 0).hom) ≃ₗ[R]
      LinearMap.ker ((C.d 1 0).hom.dualMap) :=
    LinearEquiv.ofEq _ _ (by rw [hdual])
  -- `ker (d₁ᴴ) = (range d₁)ᵃⁿⁿ`
  have e_b : LinearMap.ker ((C.d 1 0).hom.dualMap) ≃ₗ[R]
      (LinearMap.range (C.d 1 0).hom).dualAnnihilator :=
    LinearEquiv.ofEq _ _ (LinearMap.ker_dualMap_eq_dualAnnihilator_range (C.d 1 0).hom)
  -- `(range d₁)ᵃⁿⁿ ≅ Dual (M ⧸ range d₁)`
  have e_c : (LinearMap.range (C.d 1 0).hom).dualAnnihilator ≃ₗ[R]
      Module.Dual R ((C.X 0) ⧸ LinearMap.range (C.d 1 0).hom) :=
    (Submodule.dualQuotEquivDualAnnihilator (LinearMap.range (C.d 1 0).hom)).symm
  -- `M ⧸ range d₁ ≅ coker d₁`
  have e_d : Module.Dual R ((C.X 0) ⧸ LinearMap.range (C.d 1 0).hom) ≃ₗ[R]
      Module.Dual R co :=
    (moduleIsoToLinearEquiv (ModuleCat.cokernelIsoRangeQuotient (C.d 1 0))).dualMap
  -- `coker d₁ ≅ opcycles 0`
  have e_e : Module.Dual R co ≃ₗ[R] Module.Dual R op :=
    ((moduleIsoToLinearEquiv (colimit.isoColimitCocone ⟨_,
      HomologicalComplex.opcyclesIsCokernel C 1 0
        (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl))⟩)).dualMap).symm
  -- `opcycles 0 ≅ H₀`
  have e_f : Module.Dual R op ≃ₗ[R] Module.Dual R H :=
    (moduleIsoToLinearEquiv (ChainComplex.isoHomologyι₀ C)).dualMap
  have e := e_a ≪≫ₗ e_b ≪≫ₗ e_c ≪≫ₗ e_d ≪≫ₗ e_e ≪≫ₗ e_f
  exact ⟨e1 ≪≫ e.toModuleIso⟩

end

end Work.Cohomology
