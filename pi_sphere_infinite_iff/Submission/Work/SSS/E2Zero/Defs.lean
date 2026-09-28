import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.E2Aux.homologyZeroIsoCokernel
import Submission.Work.SSS.LESFacts
import Submission.Work.SSS.E2Zero.homologypi_eq_zero_iff
import Submission.Work.SSS.E2Zero.Cincl_mem_V_one_iff

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace Work.SSS.E2Zero

attribute [-instance] AddCommGroup.toIntModule

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-! ## Index bookkeeping for `ComplexShape.down ℕ` -/

theorem next_eq_down (i : ℕ) : (ComplexShape.down ℕ).next i = i - 1 := by
  rcases i with _ | k
  · exact ComplexShape.next_eq_self' _ 0 (by intro k hk; simp [ComplexShape.down] at hk)
  · exact ComplexShape.next_eq' _ (by simp [ComplexShape.down])

theorem prev_eq_down (i : ℕ) : (ComplexShape.down ℕ).prev i = i + 1 :=
  ComplexShape.prev_eq' _ (by simp [ComplexShape.down])

/-! ## Chain-map facts for the filtration -/

theorem Cincl_injective (ξ : Filtration C) (s n : ℕ) : Function.Injective (Cincl ξ s n) := by
  haveI := ξ.mono_incl s
  exact (ModuleCat.mono_iff_injective _).1 (inferInstance : Mono ((ξ.incl s).f n))

theorem Cincl_dFs (ξ : Filtration C) (s n : ℕ) (y : (ξ.F.obj s).X n) :
    dC C n (n - 1) (Cincl ξ s n y) = Cincl ξ s (n - 1) (dFs ξ s n (n - 1) y) :=
  ConcreteCategory.congr_hom (HomologicalComplex.Hom.comm (ξ.incl s) n (n - 1)) y

theorem Cincl_dFs_in (ξ : Filtration C) (s n : ℕ) (y : (ξ.F.obj s).X (n + 1)) :
    Cincl ξ s n (dFs ξ s (n + 1) n y) = dC C (n + 1) n (Cincl ξ s (n + 1) y) :=
  (ConcreteCategory.congr_hom (HomologicalComplex.Hom.comm (ξ.incl s) (n + 1) n) y).symm

theorem Cincl_Finc (ξ : Filtration C) {s s' : ℕ} (h : s ≤ s') (n : ℕ) (y : (ξ.F.obj s).X n) :
    Cincl ξ s' n (Finc ξ s s' h n y) = Cincl ξ s n y := by
  have h1 := HomologicalComplex.congr_hom (ξ.compat h) n
  rw [HomologicalComplex.comp_f] at h1
  exact ConcreteCategory.congr_hom h1 y

/-- `Cincl ξ 0 n` factors through `Cincl ξ 1 n` along `F_0 → F_1`. -/
theorem Cincl_zero_eq_one (ξ : Filtration C) (n : ℕ) (y : (ξ.F.obj 0).X n) :
    Cincl ξ 0 n y = Cincl ξ 1 n (((incF ξ.F 0).f n).hom y) := by
  have h := Cincl_Finc (s := 0) (s' := 1) ξ (Nat.le_succ 0) n y
  rw [show Finc ξ 0 1 (Nat.le_succ 0) n = ((incF ξ.F 0).f n).hom from rfl] at h
  exact h.symm

theorem dFs_comp (ξ : Filtration C) (s n : ℕ) (y : (ξ.F.obj s).X (n + 1)) :
    dFs ξ s n (n - 1) (dFs ξ s (n + 1) n y) = 0 :=
  ConcreteCategory.congr_hom (HomologicalComplex.d_comp_d (ξ.F.obj s) (n + 1) n (n - 1)) y

theorem dC_comp (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (y : C.X (n + 1)) :
    dC C n (n - 1) (dC C (n + 1) n y) = 0 :=
  ConcreteCategory.congr_hom (HomologicalComplex.d_comp_d C (n + 1) n (n - 1)) y

/-! ## Transports from the short complex `K.sc i` to the complex `K` -/

/-- The `ℤ`-linear transport `(K.sc i).X₁ → K.X (i+1)`. -/
def tau1LM (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) :
    ↥((K.sc i).X₁) →ₗ[ℤ] ↥(K.X (i + 1)) :=
  (eqToHom (show (K.sc i).X₁ = K.X ((ComplexShape.down ℕ).prev i) from rfl) ≫
    (K.XIsoOfEq (prev_eq_down i)).hom).hom

/-- The `ℤ`-linear transport `(K.sc i).X₂ → K.X i`. -/
def tau2LM (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) :
    ↥((K.sc i).X₂) →ₗ[ℤ] ↥(K.X i) :=
  (eqToHom (show (K.sc i).X₂ = K.X i from rfl)).hom

/-- The `ℤ`-linear transport `(K.sc i).X₃ → K.X (i-1)`. -/
def tau3LM (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) :
    ↥((K.sc i).X₃) →ₗ[ℤ] ↥(K.X (i - 1)) :=
  (eqToHom (show (K.sc i).X₃ = K.X ((ComplexShape.down ℕ).next i) from rfl) ≫
    (K.XIsoOfEq (next_eq_down i)).hom).hom

/-- The underlying chain of a cycle of `K` in degree `i`. -/
def valCyc (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) :
    ↥((K.sc i).cycles) →ₗ[ℤ] ↥(K.X i) :=
  (tau2LM K i).comp ((K.sc i).iCycles).hom

/-- The underlying chain of an element of the concrete model of the cycles. -/
def valK (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) :
    ↥((K.sc i).moduleCatLeftHomologyData.K) →ₗ[ℤ] ↥(K.X i) :=
  (tau2LM K i).comp ((K.sc i).moduleCatLeftHomologyData.i).hom

/-- The `t`-th component of `incF ξ.F 0`, as a linear map of chain modules. -/
def incf (ξ : Filtration C) (t : ℕ) :
    ↥((ξ.F.obj 0).X t) →ₗ[ℤ] ↥((ξ.F.obj 1).X t) :=
  ((incF ξ.F 0).f t).hom

theorem tau2_f (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) (u : ↥((K.sc i).X₁)) :
    tau2LM K i ((K.sc i).f u) = K.d (i + 1) i (tau1LM K i u) := by
  have h := ConcreteCategory.congr_hom (K.XIsoOfEq_hom_comp_d (prev_eq_down i) i) u
  simp only [ModuleCat.hom_comp] at h
  simp only [tau1LM, tau2LM, HomologicalComplex.shortComplexFunctor_obj_f, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  exact h.symm

theorem tau3_g (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) (x : ↥((K.sc i).X₂)) :
    tau3LM K i ((K.sc i).g x) = K.d i (i - 1) (tau2LM K i x) := by
  have h := ConcreteCategory.congr_hom (K.d_comp_XIsoOfEq_hom (next_eq_down i) i) x
  simp only [ModuleCat.hom_comp] at h
  simp only [tau3LM, tau2LM, HomologicalComplex.shortComplexFunctor_obj_g, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  exact h

theorem valK_moduleCatToCycles (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ)
    (u : ↥((K.sc i).X₁)) :
    valK K i ((K.sc i).moduleCatToCycles u) = K.d (i + 1) i (tau1LM K i u) := by
  simp only [valK, tau2LM, ShortComplex.moduleCatToCycles,
    ShortComplex.moduleCatLeftHomologyData_i_hom, LinearMap.comp_apply, LinearMap.codRestrict_apply,
    Submodule.subtype_apply]
  exact tau2_f K i u

theorem valK_moduleCatToCycles' (ξ : Filtration C) (s : ℕ) (t : ℕ)
    (u : ↥(((ξ.F.obj s).sc t).X₁)) :
    valK (ξ.F.obj s) t (((ξ.F.obj s).sc t).moduleCatToCycles u)
      = dFs ξ s (t + 1) t (tau1LM (ξ.F.obj s) t u) :=
  valK_moduleCatToCycles (ξ.F.obj s) t u

theorem tau2_incf (ξ : Filtration C) (t : ℕ) (x : ↥(((ξ.F.obj 0).sc t).X₂)) :
    tau2LM (ξ.F.obj 1) t (((incF ξ.F 0).f t) x) = incf ξ t (tau2LM (ξ.F.obj 0) t x) :=
  rfl

theorem valK_cycle_eq (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ)
    (v : ↥((K.sc i).cycles)) : valK K i ((K.sc i).moduleCatCyclesIso.hom v) = valCyc K i v := by
  have h := ConcreteCategory.congr_hom (ShortComplex.moduleCatCyclesIso_hom_i (K.sc i)) v
  simp only [CategoryTheory.comp_apply, Submodule.subtype_apply] at h
  simp only [valK, valCyc, tau2LM, LinearMap.comp_apply]
  exact h

theorem moduleCatLeftHomologyData_i_apply (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ)
    (y : ↥((K.sc i).moduleCatLeftHomologyData.K)) :
    ((K.sc i).moduleCatLeftHomologyData.i.hom) y = ((K.sc i).g.hom).ker.subtype y :=
  LinearMap.congr_fun (ShortComplex.moduleCatLeftHomologyData_i_hom (K.sc i)) y

theorem valK_isCycle (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ)
    (y : ↥((K.sc i).moduleCatLeftHomologyData.K)) :
    K.d i (i - 1) (valK K i y) = 0 := by
  have ht := tau3_g K i ((K.sc i).moduleCatLeftHomologyData.i y)
  have h : (K.sc i).g ((K.sc i).moduleCatLeftHomologyData.i y) = 0 := by
    have h2 := moduleCatLeftHomologyData_i_apply K i y
    have h3 : (K.sc i).g.hom (((K.sc i).g.hom).ker.subtype y) = 0 := LinearMap.mem_ker.mp y.2
    have h4 : (K.sc i).g.hom ((K.sc i).moduleCatLeftHomologyData.i.hom y) = 0 := by
      rw [h2]
      exact h3
    exact h4
  have h1 : valK K i y = tau2LM K i ((K.sc i).moduleCatLeftHomologyData.i y) := by
    simp only [valK, LinearMap.comp_apply]
  calc K.d i (i - 1) (valK K i y)
      = K.d i (i - 1) (tau2LM K i ((K.sc i).moduleCatLeftHomologyData.i y)) := by rw [h1]
    _ = tau3LM K i ((K.sc i).g ((K.sc i).moduleCatLeftHomologyData.i y)) := ht.symm
    _ = 0 := by rw [h, map_zero]

theorem valCyc_isCycle (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) (v : ↥((K.sc i).cycles)) :
    K.d i (i - 1) (valCyc K i v) = 0 := by
  have h1 : valCyc K i v = tau2LM K i ((K.sc i).iCycles v) := by
    simp only [valCyc, LinearMap.comp_apply]
  rw [h1]
  simp only [tau2LM]
  exact ConcreteCategory.congr_hom (K.iCycles_d i (i - 1)) v

/-! ## The concrete map on the cycles of `F_0` -/

/-- The `ℤ`-linear map on the cycles of `F_0` in degree `t` sending a cycle `z` to the class of
`Cincl ξ 0 t z` in `Z_t(F_0)/V_1`. -/
def psi0 (ξ : Filtration C) (t : ℕ) :
    ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K) →ₗ[ℤ] (↥(Zof ξ t) ⧸ VZ ξ t 1) :=
  (VZ ξ t 1).mkQ.comp (LinearMap.codRestrict (Zof ξ t)
    ((Cincl ξ 0 t).comp (valK (ξ.F.obj 0) t)) (by
      intro y
      refine ⟨?_, ?_⟩
      · show dC C t (t - 1) (Cincl ξ 0 t (valK (ξ.F.obj 0) t y)) = 0
        rw [Cincl_dFs,
          show dFs ξ 0 t (t - 1) (valK (ξ.F.obj 0) t y) = 0 from valK_isCycle (ξ.F.obj 0) t y,
          map_zero]
      · exact ⟨valK (ξ.F.obj 0) t y, rfl⟩))

theorem psi0_apply (ξ : Filtration C) (t : ℕ)
    (y : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K)) :
    psi0 ξ t y = (VZ ξ t 1).mkQ
      ⟨Cincl ξ 0 t (valK (ξ.F.obj 0) t y), by
        refine ⟨?_, ?_⟩
        · show dC C t (t - 1) (Cincl ξ 0 t (valK (ξ.F.obj 0) t y)) = 0
          rw [Cincl_dFs,
            show dFs ξ 0 t (t - 1) (valK (ξ.F.obj 0) t y) = 0 from valK_isCycle (ξ.F.obj 0) t y,
            map_zero]
        · exact ⟨valK (ξ.F.obj 0) t y, rfl⟩⟩ := rfl

theorem psi0_eq_zero_iff (ξ : Filtration C) (t : ℕ)
    (y : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K)) :
    psi0 ξ t y = 0 ↔ Cincl ξ 0 t (valK (ξ.F.obj 0) t y) ∈ V ξ t 1 := by
  rw [psi0_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simp only [VZ, Submodule.mem_comap, Submodule.subtype_apply]

/-- The image of the concrete boundaries of `F_0` lies in `V_1`. -/
theorem psi0_boundaries (ξ : Filtration C) (t : ℕ)
    (y : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K))
    (hy : ∃ u : ↥(((ξ.F.obj 0).sc t).X₁), (((ξ.F.obj 0).sc t).moduleCatToCycles u = y)) :
    psi0 ξ t y = 0 := by
  obtain ⟨u, hu⟩ := hy
  rw [psi0_eq_zero_iff]
  have hcoe : valK (ξ.F.obj 0) t y = dFs ξ 0 (t + 1) t (tau1LM (ξ.F.obj 0) t u) := by
    rw [← hu]
    exact valK_moduleCatToCycles' ξ 0 t u
  rw [hcoe]
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Cincl_dFs_in]
    exact Submodule.mem_map.mpr ⟨Cincl ξ 0 (t + 1) (tau1LM (ξ.F.obj 0) t u),
      LinearMap.mem_range.mpr ⟨incf ξ (t + 1) (tau1LM (ξ.F.obj 0) t u),
        (Cincl_zero_eq_one ξ (t + 1) (tau1LM (ξ.F.obj 0) t u)).symm⟩, rfl⟩
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, Cincl_dFs, dFs_comp, map_zero]
    · exact ⟨dFs ξ 0 (t + 1) t (tau1LM (ξ.F.obj 0) t u), rfl⟩

/-! ## The map `χ` from `H_t(F_0)` to `Z_t(F_0)/V_1` -/

/-- The map induced by `psi0` on the homology `H_t(F_0)`. -/
def psi (ξ : Filtration C) (t : ℕ) :
    ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.H) →ₗ[ℤ] (↥(Zof ξ t) ⧸ VZ ξ t 1) :=
  Submodule.liftQ _ (psi0 ξ t) (by
    intro y hy
    exact LinearMap.mem_ker.mpr (psi0_boundaries ξ t y (LinearMap.mem_range.mp hy)))

/-- The map `χ : H_t(F_0) → Z_t(F_0)/V_1`. -/
def chi (ξ : Filtration C) (t : ℕ) :
    ↥(((ξ.F.obj 0).sc t).homology) →ₗ[ℤ] (↥(Zof ξ t) ⧸ VZ ξ t 1) :=
  (psi ξ t).comp (((ξ.F.obj 0).sc t).moduleCatHomologyIso.hom).hom

theorem moduleCatHomologyIso_apply (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ)
    (v : ↥((K.sc i).cycles)) :
    ((K.sc i).moduleCatHomologyIso.hom.hom) ((K.sc i).homologyπ v)
      = ((K.sc i).moduleCatLeftHomologyData.π.hom) ((K.sc i).moduleCatCyclesIso.hom v) :=
  ConcreteCategory.congr_hom (ShortComplex.π_moduleCatCyclesIso_hom (K.sc i)) v

theorem chi_apply (ξ : Filtration C) (t : ℕ) (v : ↥(((ξ.F.obj 0).sc t).cycles)) :
    chi ξ t (((ξ.F.obj 0).sc t).homologyπ v)
      = psi0 ξ t (((ξ.F.obj 0).sc t).moduleCatCyclesIso.hom v) := by
  have h := moduleCatHomologyIso_apply (ξ.F.obj 0) t v
  have h1 : chi ξ t (((ξ.F.obj 0).sc t).homologyπ v)
      = psi ξ t (((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.π.hom
          (((ξ.F.obj 0).sc t).moduleCatCyclesIso.hom v)) := by
    simp only [chi, LinearMap.comp_apply]
    exact congrArg (psi ξ t) h
  rw [h1]
  exact Submodule.liftQ_apply _ _ _

theorem iCycles_cyclesMap_apply (ξ : Filtration C) (t : ℕ)
    (v : ↥(((ξ.F.obj 0).sc t).cycles)) :
    ((ξ.F.obj 1).sc t).iCycles
        (HomologicalComplex.cyclesMap (incF ξ.F 0) t (show ↥((ξ.F.obj 0).cycles t) from v))
      = ((incF ξ.F 0).f t) (((ξ.F.obj 0).sc t).iCycles v) :=
  ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (incF ξ.F 0) t)
    (show ↥((ξ.F.obj 0).cycles t) from v)


/-! ## The identification of `H_t(F_0)` with the concrete model `(F_0.sc t).homology` -/

/-- The canonical linear equivalence from `H_t(F_0)` with the index `0 + t` (as produced by
`kF ξ 0 t`) to the concrete model `(F_0.sc t).homology`. -/
def hT (ξ : Filtration C) (t : ℕ) :
    ↥((ξ.F.obj 0).homology (0 + t)) ≃ₗ[ℤ] ↥(((ξ.F.obj 0).sc t).homology) :=
  ((eqToIso (congrArg (fun i => (ξ.F.obj 0).homology i) (Nat.zero_add t)) ≪≫
      Iso.refl _)).toLinearEquiv

theorem valK_mk (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ)
    (y : ↥((K.sc i).X₂)) (hy : (K.sc i).g.hom y = 0) :
    valK K i (⟨y, hy⟩ : ↥((K.sc i).moduleCatLeftHomologyData.K)) = tau2LM K i y := by
  have h1 : ((K.sc i).moduleCatLeftHomologyData.i)
        (⟨y, hy⟩ : ↥((K.sc i).moduleCatLeftHomologyData.K))
      = (show ↥((K.sc i).X₂) from y) :=
    LinearMap.congr_fun (ShortComplex.moduleCatLeftHomologyData_i_hom (K.sc i)) ⟨y, hy⟩
  calc valK K i (⟨y, hy⟩ : ↥((K.sc i).moduleCatLeftHomologyData.K))
      = tau2LM K i (((K.sc i).moduleCatLeftHomologyData.i)
          (⟨y, hy⟩ : ↥((K.sc i).moduleCatLeftHomologyData.K))) := rfl
    _ = tau2LM K i (show ↥((K.sc i).X₂) from y) := by rw [h1]
    _ = tau2LM K i y := rfl

theorem tau2LM_eq (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) (y : ↥((K.sc i).X₂)) :
    tau2LM K i y = (show ↥(K.X i) from y) := rfl

end

end Work.SSS.E2Zero
