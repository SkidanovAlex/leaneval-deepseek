import Mathlib
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] AddCommGroup.toIntModule

open CategoryTheory CategoryTheory.Limits
namespace Work.SSSR

noncomputable section

variable {R : Type} [CommRing R]

/-- The inclusion of the cycles of a chain complex is injective. -/
lemma iCycles_injective_C (C : ChainComplex (ModuleCat R) ℕ) (m : ℕ) :
    Function.Injective (C.iCycles m).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- `iCycles` of `cyclesMk`. -/
lemma iCycles_cyclesMk_C (C : ChainComplex (ModuleCat R) ℕ) {n j : ℕ} (x : C.X n)
    (hj : (ComplexShape.down ℕ).next n = j) (hx : (C.d n j).hom x = 0) :
    (C.iCycles n).hom (C.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := C) (x := x) (j := j) (hj := hj) (hx := hx)

/-- The elementwise form of the naturality of `homologyπ`. -/
lemma homologyMap_homologypi_C (C D : ChainComplex (ModuleCat R) ℕ) (φ : C ⟶ D) (n : ℕ)
    (z : C.cycles n) :
    (HomologicalComplex.homologyMap φ n).hom ((C.homologyπ n).hom z)
      = (D.homologyπ n).hom ((HomologicalComplex.cyclesMap φ n).hom z) := by
  have h := congrArg (fun (g : C.cycles n ⟶ D.homology n) => (ModuleCat.Hom.hom g) z)
    (HomologicalComplex.homologyπ_naturality φ n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The elementwise form of `cyclesMap_i`. -/
lemma iCycles_cyclesMap_C (C D : ChainComplex (ModuleCat R) ℕ) (φ : C ⟶ D) (n : ℕ)
    (z : C.cycles n) :
    (D.iCycles n).hom ((HomologicalComplex.cyclesMap φ n).hom z)
      = (φ.f n).hom ((C.iCycles n).hom z) := by
  have h := congrArg (fun (g : C.cycles n ⟶ D.X n) => (ModuleCat.Hom.hom g) z)
    (HomologicalComplex.cyclesMap_i φ n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- `cyclesMap` of `cyclesMk`. -/
lemma cyclesMap_cyclesMk_C (C D : ChainComplex (ModuleCat R) ℕ) (φ : C ⟶ D) {n j : ℕ}
    (x : C.X n) (hj : (ComplexShape.down ℕ).next n = j) (hx : (C.d n j).hom x = 0)
    (hy : (D.d n j).hom ((φ.f n).hom x) = 0) :
    (HomologicalComplex.cyclesMap φ n).hom (C.cyclesMk x j hj hx) = D.cyclesMk ((φ.f n).hom x) j hj hy := by
  apply iCycles_injective_C D n
  rw [iCycles_cyclesMap_C, iCycles_cyclesMk_C, iCycles_cyclesMk_C]

/-- The elementwise form of the commutativity of a chain map with the differential. -/
lemma chainMap_comm_apply_C (C D : ChainComplex (ModuleCat R) ℕ) (φ : C ⟶ D) (n m : ℕ)
    (x : C.X n) : (D.d n m).hom ((φ.f n).hom x) = (φ.f m).hom ((C.d n m).hom x) := by
  have h := congrArg (fun (g : C.X n ⟶ D.X m) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.Hom.comm φ n m)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- `iCycles` of `toCycles`. -/
lemma toCycles_i_C' (C : ChainComplex (ModuleCat R) ℕ) (n m : ℕ) (x : C.X (n+1)) :
    (C.iCycles m).hom ((C.toCycles (n+1) m).hom x) = (C.d (n+1) m).hom x := by
  have h := congrArg (fun (g : C.X (n+1) ⟶ C.X m) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.toCycles_i C (n+1) m)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- `homologyπ` of `toCycles` vanishes. -/
lemma homologyπ_toCycles_C' (C : ChainComplex (ModuleCat R) ℕ) (n m : ℕ) (x : C.X (n+1)) :
    (C.homologyπ m).hom ((C.toCycles (n+1) m).hom x) = 0 := by
  have h := congrArg (fun (g : C.X (n+1) ⟶ C.homology m) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.toCycles_comp_homologyπ C (n+1) m)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- **Vanishing of the homology class of a cycle of a short complex of modules.** -/
lemma moduleCat_homologypi_eq_zero_iff (S : ShortComplex (ModuleCat R)) [S.HasHomology]
    (z : S.cycles) :
    S.homologyπ z = 0 ↔ ∃ w : S.X₁, S.f.hom w = S.iCycles z := by
  have h1 : S.homologyπ z = 0 ↔ S.homologyι (S.homologyπ z) = 0 :=
    ⟨fun h => by rw [h, map_zero], fun h =>
      (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance (by rw [h, map_zero])⟩
  rw [h1]
  have h2 : S.homologyι (S.homologyπ z) = S.pOpcycles (S.iCycles z) := by
    have h := congrArg (fun (g : S.cycles ⟶ S.opcycles) => g z) (S.homology_π_ι)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  rw [h2, S.moduleCat_pOpcycles_eq_zero_iff, LinearMap.mem_range]

/-- **A cycle of a chain complex whose homology class vanishes is a boundary**, in the degrees of
the short complex `C.sc n`. -/
lemma exists_prev_d_eq_of_homologypi_eq_zero (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (z : C.cycles n) (h : (C.homologyπ n).hom z = 0) :
    ∃ w : C.X ((ComplexShape.down ℕ).prev n),
      (C.d ((ComplexShape.down ℕ).prev n) n).hom w = (C.iCycles n).hom z := by
  obtain ⟨u, hu⟩ := (moduleCat_homologypi_eq_zero_iff (R := R) (C.sc n) z).mp h
  exact ⟨u, hu⟩

/-- **A cycle of a chain complex whose homology class vanishes is a boundary.** -/
lemma exists_d_eq_of_homologypi_eq_zero (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (z : C.cycles n)
    (h : (C.homologyπ n).hom z = 0) :
    ∃ w : C.X (n+1), (C.d (n+1) n).hom w = (C.iCycles n).hom z := by
  have hrel : (ComplexShape.down ℕ).Rel (n+1) n := by simp [ComplexShape.down]
  have hprev : (ComplexShape.down ℕ).prev n = n + 1 := ComplexShape.prev_eq' _ hrel
  obtain ⟨u, hu⟩ := exists_prev_d_eq_of_homologypi_eq_zero C n z h
  refine ⟨(C.XIsoOfEq hprev).hom u, ?_⟩
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.XIsoOfEq_hom_comp_d]
  exact hu

/-- **A cycle is a boundary iff its homology class vanishes.** -/
lemma d_eq_iCycles_iff_homologypi_eq_zero (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (z : C.cycles n) :
    (∃ w : C.X (n+1), (C.d (n+1) n).hom w = (C.iCycles n).hom z) ↔ (C.homologyπ n).hom z = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    have htw : C.toCycles (n+1) n w = z := by
      apply iCycles_injective_C C n
      rw [toCycles_i_C', hw]
    rw [← htw]
    exact homologyπ_toCycles_C' C n n w
  · exact exists_d_eq_of_homologypi_eq_zero C n z

/-- **Two cycles have the same homology class iff their difference is a boundary.** -/
lemma homologypi_eq_iff_sub_mem_range (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (z w : C.cycles n) :
    (C.homologyπ n).hom z = (C.homologyπ n).hom w ↔
      (C.iCycles n).hom z - (C.iCycles n).hom w ∈ LinearMap.range (C.d (n+1) n).hom := by
  have hsub : ((C.iCycles n).hom z - (C.iCycles n).hom w) = (C.iCycles n).hom (z - w) := by
    simp
  rw [hsub, LinearMap.mem_range, d_eq_iCycles_iff_homologypi_eq_zero C n (z - w), map_sub]
  exact sub_eq_zero.symm

end

end Work.SSSR
