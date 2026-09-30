import Mathlib

/-!
# Element-level lemmas about cycles and homology classes of chain complexes of modules

This file collects the elementary manipulation lemmas about `HomologicalComplex.cyclesMk`,
`homologyπ`, `homologyMap` and `cyclesMap` for chain complexes of `ℤ`-modules which are used in the
first-page computation of the Serre spectral sequence (`Work.SSS.FirstPage.Zsq_quot_injects_E2`).

The statements are phrased in terms of elements and morphism application rather than the homology
API, so that they can be used in the environment where the canonical `Module ℤ` structure coming
from `AddCommGroup.toIntModule` is switched off (as it is throughout the `Work.SSS` development).

Several of these lemmas are adapted from `Submission/Work/Cohomology/relCapHHom.lean`,
`Submission/Work/Cohomology/pd_us_ab_resolve.lean` and
`Submission/Work/ThomBordism/transgressionCapPairConnecting.lean` of the shared workspace.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AddCommGroup.toIntModule

open CategoryTheory CategoryTheory.Limits

namespace Work.SSS

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

/-- The underlying chain of a cycle is killed by the differential. -/
lemma iCycles_d_C (C : ChainComplex (ModuleCat R) ℕ) (n j : ℕ) (c : C.cycles n) :
    (C.d n j).hom ((C.iCycles n).hom c) = 0 := by
  have h := congrArg (fun (g : C.cycles n ⟶ C.X j) => (ModuleCat.Hom.hom g) c)
    (HomologicalComplex.iCycles_d C n j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- `cyclesMk` of the underlying chain of a cycle is the cycle. -/
lemma cyclesMk_iCycles_C (C : ChainComplex (ModuleCat R) ℕ) {n j : ℕ}
    (hj : (ComplexShape.down ℕ).next n = j) (c : C.cycles n)
    (hx : (C.d n j).hom ((C.iCycles n).hom c) = 0) :
    C.cyclesMk ((C.iCycles n).hom c) j hj hx = c := by
  apply iCycles_injective_C C n
  rw [iCycles_cyclesMk_C]

/-- `cyclesMk` does not depend on the proof that the element is a cycle. -/
lemma cyclesMk_congr_C (C : ChainComplex (ModuleCat R) ℕ) {n j : ℕ} (x : C.X n)
    (hj : (ComplexShape.down ℕ).next n = j) (h1 h2 : (C.d n j).hom x = 0) :
    C.cyclesMk x j hj h1 = C.cyclesMk x j hj h2 := by
  apply iCycles_injective_C C n
  rw [iCycles_cyclesMk_C]

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

/-- The inclusion of the cycles is additive. -/
lemma iCycles_map_add_C (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (a b : K.cycles n) :
    (K.iCycles n) (a + b) = (K.iCycles n) a + (K.iCycles n) b := by simp

/-- The inclusion of the cycles is `ℤ`-linear for scalars. -/
lemma iCycles_map_smul_C (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (c : ℤ) (a : K.cycles n) :
    (K.iCycles n) (c • a) = c • (K.iCycles n) a := by simp

/-- The class map `homologyπ` is additive. -/
lemma homologypi_map_add_C (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (a b : K.cycles n) :
    (K.homologyπ n) (a + b) = (K.homologyπ n) a + (K.homologyπ n) b := by simp

/-- The class map `homologyπ` is `ℤ`-linear for scalars. -/
lemma homologypi_map_smul_C (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (c : ℤ) (a : K.cycles n) :
    (K.homologyπ n) (c • a) = c • (K.homologyπ n) a := by simp


/-- `(ComplexShape.down ℕ).next n = n - 1` (with the convention `0 - 1 = 0`). -/
lemma next_down_eq_pred (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [ComplexShape.next_eq_self' _ _ (fun k => by simp [ComplexShape.down])]
  · exact ComplexShape.next_eq' _ (by simp [ComplexShape.down]; omega)

/-- `(ComplexShape.down ℕ).prev n = n + 1`. -/
lemma prev_down_eq_succ (n : ℕ) : (ComplexShape.down ℕ).prev n = n + 1 :=
  ComplexShape.prev_eq' _ (by simp [ComplexShape.down])


/-- `cyclesIso` sends `cyclesMk` to the corresponding element of the kernel of the differential. -/
lemma cyclesIso_hom_cyclesMk_C (S : ShortComplex (ModuleCat ℤ)) (x : S.X₂) (hx : S.g.hom x = 0) :
    (S.moduleCatLeftHomologyData.cyclesIso.hom) (S.cyclesMk x hx) = ⟨x, hx⟩ := by
  have hx'' : x ∈ (ModuleCat.Hom.hom S.g).ker := hx
  have hx' : (ConcreteCategory.hom ((forget₂ (ModuleCat ℤ) Ab).map S.g))
      (x : ↑((forget₂ (ModuleCat ℤ) Ab).obj S.X₂)) = 0 := hx
  apply (ModuleCat.mono_iff_injective S.moduleCatLeftHomologyData.i).1 inferInstance
  show ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i
      (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.cyclesIso.hom (S.cyclesMk x hx')) = _
  rw [show ModuleCat.Hom.hom S.moduleCatLeftHomologyData.cyclesIso.hom
      = ConcreteCategory.hom S.moduleCatLeftHomologyData.cyclesIso.hom from rfl]
  rw [← ConcreteCategory.comp_apply, ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
  change (ConcreteCategory.hom ((forget₂ (ModuleCat ℤ) Ab).map S.iCycles)) (S.cyclesMk x hx') = _
  rw [ShortComplex.i_cyclesMk]
  show x = ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i ⟨x, hx''⟩
  exact (congrArg (fun f => f ⟨x, hx''⟩) (ShortComplex.moduleCatLeftHomologyData_i_hom S)).symm

/-- **The class of a cycle in the concrete model of the homology.**  The isomorphism
`moduleCatHomologyIso` sends the homology class of `cyclesMk x` to the class of `x` in
`ker (S.g) / range (S.moduleCatToCycles)`. -/
lemma moduleCatHomologyIso_hom_homologypi_cyclesMk_C (S : ShortComplex (ModuleCat ℤ))
    (x : S.X₂) (hx : S.g.hom x = 0) :
    (S.moduleCatHomologyIso.hom) (S.homologyπ (S.cyclesMk x hx))
      = Submodule.mkQ (LinearMap.range S.moduleCatToCycles) ⟨x, hx⟩ := by
  have h := ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom S S.moduleCatLeftHomologyData
  have h2 := congrArg (fun (g : S.cycles ⟶ S.moduleCatLeftHomologyData.H) =>
      (ConcreteCategory.hom g) (S.cyclesMk x hx)) h
  simp only [ConcreteCategory.comp_apply] at h2
  change (ConcreteCategory.hom S.moduleCatLeftHomologyData.homologyIso.hom)
      ((ConcreteCategory.hom S.homologyπ) (S.cyclesMk x hx)) = _
  rw [h2]
  have hx'' : x ∈ (ModuleCat.Hom.hom S.g).ker := hx
  rw [show (ConcreteCategory.hom S.moduleCatLeftHomologyData.cyclesIso.hom) (S.cyclesMk x hx)
      = ⟨x, hx''⟩ from cyclesIso_hom_cyclesMk_C S x hx]
  change (S.moduleCatLeftHomologyData.π.hom) ⟨x, hx''⟩ = _
  rw [ShortComplex.moduleCatLeftHomologyData_π_hom]
  rfl


/-- `cyclesMk` of a short complex `K.sc n` and of the complex `K` agree. -/
lemma sc_cyclesMk_eq_C (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (x : K.X n)
    (h : (K.sc n).g.hom x = 0) (j : ℕ) (hj : (ComplexShape.down ℕ).next n = j)
    (hx : ((K.d n j).hom x : ↑(K.X j)) = 0) :
    (K.sc n).cyclesMk x h = K.cyclesMk x j hj hx := by
  apply iCycles_injective_C
  change (ConcreteCategory.hom ((forget₂ (ModuleCat ℤ) Ab).map (ShortComplex.iCycles (K.sc n))))
      ((K.sc n).cyclesMk x h) = _
  rw [ShortComplex.i_cyclesMk, iCycles_cyclesMk_C]

/-- A Prop-valued function of the degree, used to transport statements across equal indices. -/
lemma eq_mp_of_eq_index {j₁ j₂ : ℕ} (h : j₁ = j₂) (P : ℕ → Prop) (hp : P j₁) : P j₂ :=
  h ▸ hp


/-- `ComplexShape.down ℕ` relates `i` to `j` when `j + 1 = i`. -/
lemma rel_down (i j : ℕ) (h : j + 1 = i) : (ComplexShape.down ℕ).Rel i j := h


/-- `cyclesMk` of `0` is `0`. -/
lemma cyclesMk_zero_C (K : ChainComplex (ModuleCat ℤ) ℕ) (n j : ℕ)
    (hj : (ComplexShape.down ℕ).next n = j) (h : (K.d n j).hom (0 : K.X n) = 0) :
    K.cyclesMk (0 : K.X n) j hj h = 0 := by
  apply iCycles_injective_C
  rw [iCycles_cyclesMk_C, map_zero]


/-- The composite of two consecutive differentials vanishes. -/
lemma d_comp_d_apply_C (K : ChainComplex (ModuleCat ℤ) ℕ) (i j k : ℕ) (x : K.X i) :
    (K.d j k).hom ((K.d i j).hom x) = 0 := by
  have h := congrArg (fun (g : K.X i ⟶ K.X k) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.d_comp_d K i j k)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h


/-- The underlying element of `moduleCatToCycles x` is `S.f x`. -/
lemma moduleCatToCycles_val_C (S : ShortComplex (ModuleCat ℤ)) (x : S.X₁) :
    (S.moduleCatToCycles x).1 = S.f.hom x := rfl


end

end Work.SSS
