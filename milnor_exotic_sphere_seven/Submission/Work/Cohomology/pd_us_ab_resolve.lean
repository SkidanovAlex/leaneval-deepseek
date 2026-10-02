import Mathlib
import Submission.Work.Cohomology.pdABCoh_quasiIso
import Submission.Work.Cohomology.pd_ab_incl_rel
import Submission.Work.Cohomology.pd_ab_clean

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The restriction `H^{n+1}(X, A+B) → H^{n+1}(X, A∪B)` of the `A+B` complex is onto

For open `A, B ⊆ X` the inclusion of cochain complexes
`pdABInclRel X A B : C^*(X, A∪B) ⟶ C^*(X, A+B)` is a quasi-isomorphism
(`Work.Cohomology.pdABCoh_quasiIso`).  Consequently every cohomology class of the `A+B` complex of
degree `n+1` is represented by a relative cocycle of the pair `(X, A∪B)`.

Concretely, for a cocycle `ψ ∈ C^{n+1}(X, A+B)` there is a relative cycle `u ∈ Z^{n+1}(X, A∪B)` and a
cochain `χ ∈ C^n(X, A+B)` with `dχ = u - ψ`.  This is the statement
`Work.Cohomology.pd_us_ab_resolve`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The `singularCochainComplex` differential is the `cochainDiff`.  (Local copy, to keep this
module independent of `pd_us_aux`.) -/
theorem pd_us_ab_resolve_singularD_eq_cochainDiff (X : TopCat) (n : ℕ)
    (φ : Cochain ℤ (TopCat.toSSet.obj X) n) :
    (ConcreteCategory.hom ((singularCochainComplex ℤ X).d n (n+1))) φ
      = cochainDiff ℤ (TopCat.toSSet.obj X) φ := by
  simp only [singularCochainComplex_eq, SSetCochainComplex_d]
  exact cochainDiffLM_apply ℤ (TopCat.toSSet.obj X) n φ

/-- **Vanishing of the homology class of a cycle of a short complex of `ℤ`-modules.**

For a short complex `S` of `ℤ`-modules and a cycle `z ∈ S.cycles`, the class `S.homologyπ z` is
zero if and only if the underlying element `S.iCycles z` lies in the image of `S.f`.

This is the elementary structure of the "left homology" of a short complex of modules: `homologyπ`
followed by the monomorphism `homologyι` is `pOpcycles ∘ iCycles`, and `pOpcycles` vanishes exactly
on the range of `f`. -/
theorem pd_us_ab_resolve_sc_homologyπ_eq_zero_iff {R : Type} [CommRing R]
    (S : ShortComplex (ModuleCat R)) [S.HasHomology] (z : S.cycles) :
    S.homologyπ z = 0 ↔ ∃ w : S.X₁, S.f.hom w = S.iCycles z := by
  have h1 : S.homologyπ z = 0 ↔ S.homologyι (S.homologyπ z) = 0 :=
    ⟨fun h => by rw [h, map_zero], fun h =>
      (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance (by rw [h, map_zero])⟩
  rw [h1]
  have h2 : S.homologyι (S.homologyπ z) = S.pOpcycles (S.iCycles z) := by
    have h := congrArg (fun (g : S.cycles ⟶ S.opcycles) => g z) (S.homology_π_ι)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  rw [h2, S.moduleCat_pOpcycles_eq_zero_iff, LinearMap.mem_range]

/-- **A cycle of a cochain complex whose class vanishes is a boundary.**

For a cochain complex `K` of `ℤ`-modules and a cycle `z ∈ Z^{n+1}(K)` with vanishing cohomology
class, the underlying element is the coboundary of a degree-`n` cochain.  This is
`pd_us_ab_resolve_sc_homologyπ_eq_zero_iff` applied to `K.sc (n+1)`, with the index
`(up ℕ).prev (n+1) = n` transported by `HomologicalComplex.XIsoOfEq`. -/
theorem pd_us_ab_resolve_exists_of_homologyπ_eq_zero (K : CochainComplex (ModuleCat ℤ) ℕ)
    [∀ i, K.HasHomology i] (n : ℕ) (z : K.cycles (n+1))
    (h : K.homologyπ (n+1) z = 0) :
    ∃ y : K.X n, (K.d n (n+1)).hom y = K.iCycles (n+1) z := by
  have hrel : (ComplexShape.up ℕ).Rel n (n+1) := (ComplexShape.up_Rel ℕ n (n+1)).mpr rfl
  have hprev : (ComplexShape.up ℕ).prev (n+1) = n := ComplexShape.prev_eq' _ hrel
  have key := pd_us_ab_resolve_sc_homologyπ_eq_zero_iff (S := K.sc (n+1)) z
  obtain ⟨u, hu⟩ := key.mp h
  refine ⟨(K.XIsoOfEq hprev).hom u, ?_⟩
  have hh := congrArg (fun (g : K.X ((ComplexShape.up ℕ).prev (n+1)) ⟶ K.X (n+1)) => g u)
    (HomologicalComplex.XIsoOfEq_hom_comp_d K hprev (n+1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
  rw [hh]
  exact hu

/-- **Every class of `C^{n+1}(X, A+B)` comes from a relative class of `(X, A∪B)`.**

For open `A, B ⊆ X`, a cocycle `ψ ∈ C^{n+1}(X, A+B)` is cohomologous to the image of a relative
cocycle `u ∈ Z^{n+1}(X, A∪B)`: there is `χ ∈ C^n(X, A+B)` with `dχ = u - ψ`.  This is surjectivity
on cohomology of the quasi-isomorphism `pdABInclRel X A B` (which is an isomorphism in every degree
by `Work.Cohomology.pdABCoh_quasiIso`). -/
theorem pd_us_ab_resolve {X : TopCat} {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) {n : ℕ}
    (ψ : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) (n+1))
    (hψ : ψ ∈ Work.Cohomology.pdABKern X A B (n+1))
    (hψd : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) (n := n+1) ψ = 0) :
    ∃ (u : (Work.Cohomology.relComplex ℤ X (A ∪ B)).cycles (n+1))
      (χ : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) n),
      χ ∈ Work.Cohomology.pdABKern X A B n ∧
      Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) (n := n) χ
        = (show Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) (n+1) from
            ((Work.Cohomology.relComplex ℤ X (A ∪ B)).iCycles (n+1) u).1) - ψ := by
  classical
  let D : CochainComplex (ModuleCat ℤ) ℕ := pdABCoh X A B
  let C : CochainComplex (ModuleCat ℤ) ℕ := relComplex ℤ X (A ∪ B)
  let f : C ⟶ D := pdABInclRel X A B
  have hf : IsIso (HomologicalComplex.homologyMap f (n+1)) := pdABCoh_quasiIso hA hB (n+1)
  let ψD : D.X (n+1) := ⟨ψ, hψ⟩
  have hψD : (D.d (n+1) (n+2)).hom ψD = 0 := by
    apply Subtype.ext
    rw [pdABCoh_d_coe, Submodule.coe_zero]
    exact (pd_us_ab_resolve_singularD_eq_cochainDiff X (n+1) ψ).trans hψd
  let z : D.cycles (n+1) := cocycleOfK D ψD hψD
  have hz : (D.iCycles (n+1)).hom z = ψD := iCycles_cocycleOfK D ψD hψD
  let x : D.homology (n+1) := (D.homologyπ (n+1)).hom z
  haveI := hf
  obtain ⟨u, hu⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ (n+1))).mp inferInstance
      ((asIso (HomologicalComplex.homologyMap f (n+1))).inv x)
  have hxu : (HomologicalComplex.homologyMap f (n+1)).hom ((C.homologyπ (n+1)).hom u) = x := by
    rw [hu]
    exact (asIso (HomologicalComplex.homologyMap f (n+1))).inv_hom_id_apply x
  let w : D.cycles (n+1) := (HomologicalComplex.cyclesMap f (n+1)).hom u - z
  have hn : (D.homologyπ (n+1)).hom ((HomologicalComplex.cyclesMap f (n+1)).hom u) = x := by
    have hnat := congrArg (fun (g : C.cycles (n+1) ⟶ D.homology (n+1)) => g.hom u)
      (HomologicalComplex.homologyπ_naturality (φ := f) (i := n+1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [hxu] at hnat
    exact hnat.symm
  have hw0 : (D.homologyπ (n+1)).hom w = 0 := by
    show (D.homologyπ (n+1)).hom ((HomologicalComplex.cyclesMap f (n+1)).hom u - z) = 0
    rw [map_sub, hn, show (D.homologyπ (n+1)).hom z = x from rfl, sub_self]
  obtain ⟨χD, hχD⟩ := pd_us_ab_resolve_exists_of_homologyπ_eq_zero D n w hw0
  refine ⟨u, χD.1, χD.2, ?_⟩
  have hcm : (D.iCycles (n+1)).hom ((HomologicalComplex.cyclesMap f (n+1)).hom u)
      = (f.f (n+1)).hom ((C.iCycles (n+1)).hom u) := by
    have h := congrArg (fun (g : C.cycles (n+1) ⟶ D.X (n+1)) => g.hom u)
      (HomologicalComplex.cyclesMap_i f (n+1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have hw_eq : (D.iCycles (n+1)).hom w
      = (f.f (n+1)).hom ((C.iCycles (n+1)).hom u) - ψD := by
    show (D.iCycles (n+1)).hom ((HomologicalComplex.cyclesMap f (n+1)).hom u - z) = _
    rw [map_sub, hcm, hz]
  have hfinal : (D.d n (n+1)).hom χD
      = (f.f (n+1)).hom ((C.iCycles (n+1)).hom u) - ψD := hχD.trans hw_eq
  have hmain := congrArg (fun (y : D.X (n+1)) => y.1) hfinal
  rw [pdABCoh_d_coe, pd_us_ab_resolve_singularD_eq_cochainDiff] at hmain
  rw [Submodule.coe_sub, pdABInclRel_coe] at hmain
  exact hmain

end

end Work.Cohomology
