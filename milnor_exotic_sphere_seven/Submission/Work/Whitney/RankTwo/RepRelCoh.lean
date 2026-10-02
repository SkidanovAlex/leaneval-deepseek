import Mathlib
import Submission.Work.Cohomology.relCupHNatural
import Submission.Work.Whitney.RankTwo.RepDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Whitney.RankTwo

open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-- **Vanishing of `homologyπ` in a short complex of `ℤ`-modules** is "the cycle is a boundary". -/
theorem sc_homologyπ_eq_zero_iff {S : ShortComplex (ModuleCat ℤ)} [S.HasHomology]
    (z : S.cycles) :
    S.homologyπ z = 0 ↔ ∃ w : S.X₁, S.f.hom w = S.iCycles z := by
  have h1 : S.homologyπ z = 0 ↔ S.homologyι (S.homologyπ z) = 0 :=
    ⟨fun h => by rw [h, map_zero], fun h =>
      (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance (by rw [h, map_zero])⟩
  rw [h1]
  have h2 : S.homologyι (S.homologyπ z) = S.pOpcycles (S.iCycles z) := by
    have hh := congrArg (fun (g : S.cycles ⟶ S.opcycles) => g z) (S.homology_π_ι)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  rw [h2, S.moduleCat_pOpcycles_eq_zero_iff, LinearMap.mem_range]

/-- **Vanishing of `homologyπ` in a cochain complex of `ℤ`-modules** means "the cycle is a
coboundary". -/
theorem cochain_homologyπ_eq_zero_iff_d {C : CochainComplex (ModuleCat ℤ) ℕ}
    [∀ i, C.HasHomology i] (k : ℕ) (z : C.cycles (k+1)) :
    C.homologyπ (k+1) z = 0 ↔ ∃ w : C.X k, C.d k (k+1) w = C.iCycles (k+1) z := by
  have hrel : (ComplexShape.up ℕ).Rel k (k+1) := ComplexShape.up_mk k (k+1) rfl
  have hprev : (ComplexShape.up ℕ).prev (k+1) = k := ComplexShape.prev_eq' _ hrel
  have key := sc_homologyπ_eq_zero_iff (S := C.sc (k+1)) (z := z)
  have hR : (∃ w : (C.sc (k+1)).X₁, (C.sc (k+1)).f.hom w = (C.sc (k+1)).iCycles z)
      ↔ ∃ w : C.X k, C.d k (k+1) w = C.iCycles (k+1) z := by
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨(C.XIsoOfEq hprev.symm).inv w, ?_⟩
      rw [← ModuleCat.comp_apply, HomologicalComplex.XIsoOfEq_inv_comp_d]
      exact hw
    · rintro ⟨w, hw⟩
      refine ⟨(C.XIsoOfEq hprev).inv w, ?_⟩
      change C.d ((ComplexShape.up ℕ).prev (k+1)) (k+1)
        ((C.XIsoOfEq hprev).inv w) = C.iCycles (k+1) z
      rw [← ModuleCat.comp_apply, HomologicalComplex.XIsoOfEq_inv_comp_d]
      exact hw
  exact (Iff.of_eq (show ((C.sc (k+1)).homologyπ z = 0) = (C.homologyπ (k+1) z = 0)
    from rfl)).symm.trans (key.trans hR)

/-- **Representatives of the same relative cohomology class differ by a coboundary.** -/
theorem relClassOf_coboundary {X : TopCat} (A : Set ↑X) {n : ℕ}
    (α α' : ↥(relKern ℤ X A (n+1)))
    (hα : relDiffLM ℤ X A (n+1) α = 0)
    (hα' : relDiffLM ℤ X A (n+1) α' = 0)
    (h : relClassOf ℤ X A α hα = relClassOf ℤ X A α' hα') :
    ∃ v : ↥(relKern ℤ X A n), relDiffLM ℤ X A n v = α - α' := by
  set z : (relComplex ℤ X A).cycles (n+1) := relCocycleOf ℤ X A α hα with hz
  set z' : (relComplex ℤ X A).cycles (n+1) := relCocycleOf ℤ X A α' hα' with hz'
  have hclass : ((relComplex ℤ X A).homologyπ (n+1)).hom z
      = ((relComplex ℤ X A).homologyπ (n+1)).hom z' := h
  have hzero : ((relComplex ℤ X A).homologyπ (n+1)).hom (z - z') = 0 := by
    rw [map_sub, hclass, sub_self]
  obtain ⟨w, hw⟩ := (cochain_homologyπ_eq_zero_iff_d (C := relComplex ℤ X A) n (z - z')).mp hzero
  refine ⟨w, ?_⟩
  have hw' : (relDiffLM ℤ X A n) w = α - α' := by
    rw [← relComplex_d_apply ℤ X A (n := n) (γ := w)]
    rw [hw, map_sub, iCycles_relCocycleOf, iCycles_relCocycleOf]
  exact hw'

/-- **The class of a pulled-back relative cocycle is the pullback of its class.** -/
theorem relClassOf_relMapLM {X₁ X₂ : TopCat} (A₁ : Set ↑X₁) (A₂ : Set ↑X₂)
    (f : C(↑X₁, ↑X₂))
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ)
    (a : ↥(relKern ℤ X₂ A₂ n))
    (ha : relDiffLM ℤ X₂ A₂ n a = 0)
    (hcoc : relDiffLM ℤ X₁ A₁ n
      (relMapLM ℤ A₁ A₂ (TopCat.ofHom f) h n a) = 0) :
    relClassOf ℤ X₁ A₁
        (relMapLM ℤ A₁ A₂ (TopCat.ofHom f) h n a) hcoc
      = (Work.Thom.relCohMap f A₁ A₂ h ℤ n).hom
          (relClassOf ℤ X₂ A₂ a ha) := by
  rw [show relClassOf ℤ X₁ A₁ (relMapLM ℤ A₁ A₂ (TopCat.ofHom f) h n a) hcoc
      = relClassOf ℤ X₁ A₁ (relMapLM ℤ A₁ A₂ (TopCat.ofHom f) h n a)
          (relDiffLM_relMapLM ℤ A₁ A₂ (TopCat.ofHom f) h a ha) from
    relClassOf_proof_irrel ℤ X₁ A₁ _ _ _]
  exact (homologyMap_relComplexMap_relClassOf ℤ A₁ A₂ (TopCat.ofHom f) h a ha).symm

end

end Work.Whitney.RankTwo
