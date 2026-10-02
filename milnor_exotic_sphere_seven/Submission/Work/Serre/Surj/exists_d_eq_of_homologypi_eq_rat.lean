import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.Serre.Surj

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-! ## A cycle of vanishing homology class is a boundary

For a chain complex of `ℚ`-modules the kernel of the canonical map
`homologyπ n : K.cycles n ⟶ K.homology n` is exactly the image of the differential
`K.X (n+1) ⟶ K.cycles n`: a cycle whose homology class vanishes is a boundary.
This is the "surjectivity of the differential onto the degree-`n` cycles modulo degree-`n`
homology" statement used in the Serre surjectivity argument.

The proof goes through the explicit left homology data of a short complex of modules
(`ShortComplex.moduleCatLeftHomologyData`), where the homology is exhibited as the quotient of
the cycles by the range of `S.moduleCatToCycles`. -/

/-- A linear map version of the elementary quotient fact: an element dies in the quotient of the
codomain by the range of a linear map iff it lies in that range. -/
private lemma exists_of_mkQ_range_eq_zero {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {x : N}
    (h : Submodule.mkQ f.range x = 0) : ∃ y, f y = x := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  exact LinearMap.mem_range.mp h

/-- For a short complex of modules, a cycle whose class in the homology vanishes is the image of
the boundary map `S.toCycles : S.X₁ ⟶ S.cycles`.  This is the elementwise form of the statement
that the kernel of `S.homologyπ` is the image of `S.toCycles`. -/
theorem exists_toCycles_eq_of_homologyπ_eq_zero {R : Type*} [Ring R]
    (S : ShortComplex (ModuleCat R)) (z : ↥S.cycles)
    (h : (ModuleCat.Hom.hom S.homologyπ) z = 0) :
    ∃ w : ↥S.X₁, (ModuleCat.Hom.hom S.toCycles) w = z := by
  -- push the hypothesis through the explicit identification of `S.homology` with the quotient
  -- of `S.cycles` by `S.toCycles`
  have key := congrArg (fun (m : S.cycles ⟶ S.moduleCatLeftHomologyData.H) =>
      (ModuleCat.Hom.hom m) z) (ShortComplex.π_moduleCatCyclesIso_hom S)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  rw [h, map_zero] at key
  have h1 : S.moduleCatToCycles.range.mkQ ((ModuleCat.Hom.hom S.moduleCatCyclesIso.hom) z) = 0 :=
    key.symm
  obtain ⟨w, hw⟩ := exists_of_mkQ_range_eq_zero
    (S.moduleCatToCycles : ↥S.X₁ →ₗ[R] ↥(LinearMap.ker S.g.hom)) h1
  refine ⟨w, ?_⟩
  -- bring the information back along the isomorphism `S.cycles ≅ LinearMap.ker S.g`
  have h3 := congrArg (fun (m : S.X₁ ⟶ S.moduleCatLeftHomologyData.K) =>
      (ModuleCat.Hom.hom m) w) (ShortComplex.toCycles_moduleCatCyclesIso_hom S)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h3
  have h4 : (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom) ((ModuleCat.Hom.hom S.toCycles) w)
      = (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom) z := by
    rw [h3, ShortComplex.moduleCatLeftHomologyData_f'_hom]
    exact hw
  exact (ModuleCat.mono_iff_injective S.moduleCatCyclesIso.hom).mp inferInstance h4

/-- **A cycle of a rational chain complex whose homology class vanishes is a boundary.** -/
theorem exists_d_eq_of_homologypi_eq_rat (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (z : ↥(K.cycles n)) (h : (ModuleCat.Hom.hom (K.homologyπ n)) z = 0) :
    ∃ w : ↥(K.X (n + 1)),
      (ModuleCat.Hom.hom (K.d (n + 1) n)) w = (ModuleCat.Hom.hom (K.iCycles n)) z := by
  -- the short complex `K.X (n+1) ⟶ K.X n ⟶ K.X (n-1)` whose cycles are `K.cycles n`
  obtain ⟨y, hy⟩ : ∃ y : ↥(K.X ((ComplexShape.down ℕ).prev n)),
      (ModuleCat.Hom.hom ((K.sc n).toCycles)) y = z :=
    exists_toCycles_eq_of_homologyπ_eq_zero (K.sc n) z h
  -- take the underlying chain
  have hfy : (ModuleCat.Hom.hom ((K.sc n).f)) y = (ModuleCat.Hom.hom (K.iCycles n)) z := by
    have hh0 := congrArg (fun (m : (K.sc n).X₁ ⟶ (K.sc n).X₂) => ModuleCat.Hom.hom m)
      (ShortComplex.toCycles_i (S := K.sc n))
    have hh : ModuleCat.Hom.hom ((K.sc n).f)
        = ModuleCat.Hom.hom ((K.sc n).iCycles) ∘ₗ ModuleCat.Hom.hom ((K.sc n).toCycles) :=
      hh0.symm.trans (ModuleCat.hom_comp (K.sc n).toCycles (K.sc n).iCycles)
    have h2 : (ModuleCat.Hom.hom ((K.sc n).f)) y
        = (ModuleCat.Hom.hom ((K.sc n).iCycles)) ((ModuleCat.Hom.hom ((K.sc n).toCycles)) y) :=
      (DFunLike.congr_fun hh y).trans (LinearMap.comp_apply _ _ _)
    rw [h2, hy]
    rfl
  -- identify the index `c.prev n` with `n + 1`
  have hprev : (ComplexShape.down ℕ).prev n = n + 1 :=
    ComplexShape.prev_eq' (ComplexShape.down ℕ) (i := n) (j := n + 1) (by rfl)
  refine ⟨(ModuleCat.Hom.hom (K.XIsoOfEq hprev).hom) y, ?_⟩
  have step1 : (ModuleCat.Hom.hom (K.d (n + 1) n)) ((ModuleCat.Hom.hom (K.XIsoOfEq hprev).hom) y)
      = (ModuleCat.Hom.hom (K.d ((ComplexShape.down ℕ).prev n) n)) y := by
    have hh := congrArg (fun (m : K.X ((ComplexShape.down ℕ).prev n) ⟶ K.X n) =>
        ModuleCat.Hom.hom m) (HomologicalComplex.XIsoOfEq_hom_comp_d K hprev n)
    have hh2 := DFunLike.congr_fun hh y
    rw [ModuleCat.hom_comp] at hh2
    simpa using hh2
  rw [step1]
  exact hfy

end Work.Serre.Surj
