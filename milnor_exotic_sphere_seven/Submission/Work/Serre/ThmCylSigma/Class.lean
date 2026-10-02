import Submission.Work.Serre.ThmCylSigma.Defs
import Submission.Work.Serre.ThmCylSigma.cochain_homologypi_eq_zero_rat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The elementary calculus of cohomology classes of cocycles

For the absolute cochain complex of a simplicial set and for the relative cochain complex of a pair
of spaces, over `ℚ`:

* the class of a coboundary vanishes;
* a cocycle of vanishing class is a coboundary;
* two cocycles with the same class differ by a coboundary.

The second and third facts are deduced from the generic statement
`Work.Serre.ThmCylSigma.cochain_homologypi_eq_zero_rat`; the first is proved directly from
`toCycles_comp_homologyπ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.Serre.Sigma

noncomputable section

variable {R : Type} [CommRing R]

/-! ## The coboundary of a coboundary -/

/-- The coboundary of a coboundary of a cochain vanishes. -/
theorem cochainDiff_cochainDiff' (Y : SSet) {k : ℕ} (w : Work.Cohomology.Cochain R Y k) :
    Work.Cohomology.cochainDiff R Y (Work.Cohomology.cochainDiff R Y w) = 0 := by
  have h := congrArg
    (fun (m : (Work.Cohomology.SSetCochainComplex R Y).X k ⟶
        (Work.Cohomology.SSetCochainComplex R Y).X (k + 2)) => m.hom w)
    (HomologicalComplex.d_comp_d (Work.Cohomology.SSetCochainComplex R Y) k (k + 1) (k + 2))
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h
  simpa only [Work.Cohomology.SSetCochainComplex_d_hom] using h

/-! ## The class of a coboundary vanishes -/

/-- **The absolute cohomology class of a coboundary vanishes.** -/
theorem cohomologyClassOf_cochainDiff_eq_zero' (X : SSet) {k : ℕ}
    (w : Work.Cohomology.Cochain R X k) :
    Work.Cohomology.cohomologyClassOf R X (Work.Cohomology.cochainDiff R X w)
      (cochainDiff_cochainDiff' X w) = 0 := by
  have hcyc : Work.Cohomology.cocycleOf R X (Work.Cohomology.cochainDiff R X w)
      (cochainDiff_cochainDiff' X w) =
      (Work.Cohomology.SSetCochainComplex R X).toCycles k (k + 1) w := by
    apply Work.Cohomology.iCycles_injective R X (k + 1)
    have h := congrArg (fun (m : (Work.Cohomology.SSetCochainComplex R X).X k ⟶
        (Work.Cohomology.SSetCochainComplex R X).X (k + 1)) => m.hom w)
      (HomologicalComplex.toCycles_i (Work.Cohomology.SSetCochainComplex R X) k (k + 1))
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [Work.Cohomology.iCycles_cocycleOf]
    simpa only [Work.Cohomology.SSetCochainComplex_d_hom] using h.symm
  rw [Work.Cohomology.cohomologyClassOf, hcyc]
  have h := HomologicalComplex.toCycles_comp_homologyπ
    (Work.Cohomology.SSetCochainComplex R X) k (k + 1)
  have h2 := congrArg (fun (m : (Work.Cohomology.SSetCochainComplex R X).X k ⟶
      (Work.Cohomology.SSetCochainComplex R X).homology (k + 1)) => m.hom w) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h2

/-- The differential of a relative coboundary vanishes. -/
theorem relDiffLM_relDiffLM (X : TopCat) (A : Set X) {n : ℕ}
    (w : Work.Cohomology.relKern R X A n) :
    Work.Cohomology.relDiffLM R X A (n + 1) (Work.Cohomology.relDiffLM R X A n w) = 0 := by
  apply Subtype.ext
  rw [Work.Cohomology.relDiffLM_coe, Work.Cohomology.relDiffLM_coe, Submodule.coe_zero,
    Work.Cohomology.singularCochain_d_apply, Work.Cohomology.singularCochain_d_apply]
  exact cochainDiff_cochainDiff' (TopCat.toSSet.obj X) w.1

/-- **The relative cohomology class of a relative coboundary vanishes.** -/
theorem relClassOf_relDiffLM_eq_zero (X : TopCat) (A : Set X) {n : ℕ}
    (w : Work.Cohomology.relKern R X A n) :
    Work.Cohomology.relClassOf R X A (Work.Cohomology.relDiffLM R X A n w)
      (relDiffLM_relDiffLM X A w) = 0 := by
  have hcyc : Work.Cohomology.relCocycleOf R X A (Work.Cohomology.relDiffLM R X A n w)
      (relDiffLM_relDiffLM X A w) =
      (Work.Cohomology.relComplex R X A).toCycles n (n + 1) w := by
    have key : ((Work.Cohomology.relComplex R X A).iCycles (n + 1)).hom
        (Work.Cohomology.relCocycleOf R X A (Work.Cohomology.relDiffLM R X A n w)
          (relDiffLM_relDiffLM X A w)) =
        ((Work.Cohomology.relComplex R X A).iCycles (n + 1)).hom
          ((Work.Cohomology.relComplex R X A).toCycles n (n + 1) w) := by
      rw [Work.Cohomology.iCycles_relCocycleOf]
      have h := congrArg (fun (m : (Work.Cohomology.relComplex R X A).X n ⟶
          (Work.Cohomology.relComplex R X A).X (n + 1)) => m.hom w)
        (HomologicalComplex.toCycles_i (Work.Cohomology.relComplex R X A) n (n + 1))
      rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      rw [Work.Cohomology.relComplex_d_apply] at h
      exact h.symm
    exact Work.Cohomology.iCycles_injective_K (Work.Cohomology.relComplex R X A) (n + 1) key
  rw [Work.Cohomology.relClassOf, hcyc]
  have h := HomologicalComplex.toCycles_comp_homologyπ
    (Work.Cohomology.relComplex R X A) n (n + 1)
  have h2 := congrArg (fun (m : (Work.Cohomology.relComplex R X A).X n ⟶
      (Work.Cohomology.relComplex R X A).homology (n + 1)) => m.hom w) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h2


/-! ## Cocycles of vanishing class, and cocycles with the same class -/

/-- **The generic form**: a cycle of a cochain complex of `ℚ`-modules whose class vanishes is a
boundary. -/
theorem exists_d_eq_iCycles_of_homologyπ_eq_zero_rat (K : CochainComplex (ModuleCat ℚ) ℕ)
    (n : ℕ) (z : K.cycles (n + 1)) (h : K.homologyπ (n + 1) z = 0) :
    ∃ y : K.X n, (K.d n (n + 1)).hom y = (K.iCycles (n + 1)).hom z :=
  Work.Serre.ThmCylSigma.cochain_homologypi_eq_zero_rat K n z h

/-- **The generic form**: two cycles of a cochain complex of `ℚ`-modules with the same class differ
by a boundary. -/
theorem exists_d_eq_sub_iCycles_of_homologyπ_eq_rat (K : CochainComplex (ModuleCat ℚ) ℕ)
    (n : ℕ) (z z' : K.cycles (n + 1)) (h : K.homologyπ (n + 1) z = K.homologyπ (n + 1) z') :
    ∃ y : K.X n, (K.d n (n + 1)).hom y =
      (K.iCycles (n + 1)).hom z - (K.iCycles (n + 1)).hom z' := by
  have hz : K.homologyπ (n + 1) (z - z') = 0 := by
    rw [map_sub, h, sub_self]
  obtain ⟨y, hy⟩ := exists_d_eq_iCycles_of_homologyπ_eq_zero_rat K n (z - z') hz
  exact ⟨y, by rw [hy, map_sub]⟩

/-- **A cocycle of vanishing cohomology class is a coboundary.** -/
theorem exists_cochainDiff_of_cohomologyClassOf_eq_zero (X : SSet) {k : ℕ}
    (β : Work.Cohomology.Cochain ℚ X (k + 1))
    (hβ : Work.Cohomology.cochainDiff ℚ X β = 0)
    (h : Work.Cohomology.cohomologyClassOf ℚ X β hβ = 0) :
    ∃ w : Work.Cohomology.Cochain ℚ X k, Work.Cohomology.cochainDiff ℚ X w = β := by
  obtain ⟨w, hw⟩ := exists_d_eq_iCycles_of_homologyπ_eq_zero_rat
    (Work.Cohomology.SSetCochainComplex ℚ X) k (Work.Cohomology.cocycleOf ℚ X β hβ) h
  refine ⟨w, ?_⟩
  rw [← Work.Cohomology.SSetCochainComplex_d_apply ℚ X k w, hw,
    Work.Cohomology.iCycles_cocycleOf]

/-- **Two cocycles with the same cohomology class differ by a coboundary.** -/
theorem exists_cochainDiff_sub_of_cohomologyClassOf_eq (X : SSet) {k : ℕ}
    {β γ : Work.Cohomology.Cochain ℚ X (k + 1)}
    (hβ : Work.Cohomology.cochainDiff ℚ X β = 0)
    (hγ : Work.Cohomology.cochainDiff ℚ X γ = 0)
    (h : Work.Cohomology.cohomologyClassOf ℚ X β hβ =
      Work.Cohomology.cohomologyClassOf ℚ X γ hγ) :
    ∃ w : Work.Cohomology.Cochain ℚ X k, Work.Cohomology.cochainDiff ℚ X w = β - γ := by
  obtain ⟨w, hw⟩ := exists_d_eq_sub_iCycles_of_homologyπ_eq_rat
    (Work.Cohomology.SSetCochainComplex ℚ X) k
    (Work.Cohomology.cocycleOf ℚ X β hβ) (Work.Cohomology.cocycleOf ℚ X γ hγ) h
  refine ⟨w, ?_⟩
  rw [← Work.Cohomology.SSetCochainComplex_d_apply ℚ X k w, hw,
    Work.Cohomology.iCycles_cocycleOf, Work.Cohomology.iCycles_cocycleOf]

/-- **A relative cocycle of vanishing class is a relative coboundary.** -/
theorem exists_relDiff_of_relClassOf_eq_zero (X : TopCat) (A : Set X) {n : ℕ}
    (a : Work.Cohomology.relKern ℚ X A (n + 1))
    (ha : Work.Cohomology.relDiffLM ℚ X A (n + 1) a = 0)
    (h : Work.Cohomology.relClassOf ℚ X A a ha = 0) :
    ∃ w : Work.Cohomology.relKern ℚ X A n, Work.Cohomology.relDiffLM ℚ X A n w = a := by
  obtain ⟨w, hw⟩ := exists_d_eq_iCycles_of_homologyπ_eq_zero_rat
    (Work.Cohomology.relComplex ℚ X A) n (Work.Cohomology.relCocycleOf ℚ X A a ha) h
  refine ⟨w, ?_⟩
  rw [← Work.Cohomology.relComplex_d_apply ℚ X A, hw, Work.Cohomology.iCycles_relCocycleOf]

/-- **Two relative cocycles with the same class differ by a relative coboundary.** -/
theorem exists_relDiff_sub_of_relClassOf_eq (X : TopCat) (A : Set X) {n : ℕ}
    {a b : Work.Cohomology.relKern ℚ X A (n + 1)}
    (ha : Work.Cohomology.relDiffLM ℚ X A (n + 1) a = 0)
    (hb : Work.Cohomology.relDiffLM ℚ X A (n + 1) b = 0)
    (h : Work.Cohomology.relClassOf ℚ X A a ha = Work.Cohomology.relClassOf ℚ X A b hb) :
    ∃ w : Work.Cohomology.relKern ℚ X A n, Work.Cohomology.relDiffLM ℚ X A n w = a - b := by
  obtain ⟨w, hw⟩ := exists_d_eq_sub_iCycles_of_homologyπ_eq_rat
    (Work.Cohomology.relComplex ℚ X A) n
    (Work.Cohomology.relCocycleOf ℚ X A a ha) (Work.Cohomology.relCocycleOf ℚ X A b hb) h
  refine ⟨w, ?_⟩
  rw [← Work.Cohomology.relComplex_d_apply ℚ X A, hw,
    Work.Cohomology.iCycles_relCocycleOf, Work.Cohomology.iCycles_relCocycleOf]

end

end Work.Serre.Sigma

