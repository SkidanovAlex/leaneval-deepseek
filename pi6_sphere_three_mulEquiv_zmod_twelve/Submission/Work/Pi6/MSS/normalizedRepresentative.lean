import Mathlib
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupH
import Submission.Work.Cohomology.homotopyEquivDual

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.MSS

theorem normalizedRepresentative (𝕜 : Type) [Field 𝕜] (X : SSet.{0}) (s : ℕ) :
    ∀ x : (Work.Cohomology.SSetCochainComplex 𝕜 X).homology s,
      ∃ (α : Work.Cohomology.Cochain 𝕜 X s)
        (hα : Work.Cohomology.cochainDiff 𝕜 X α = 0),
        (∀ σ : X.obj (Opposite.op (SimplexCategory.mk s)),
            σ ∈ SSet.degenerate X s → Work.Cohomology.genEval 𝕜 X α σ = 0) ∧
        Work.Cohomology.cohomologyClassOf 𝕜 X α hα = x := by
  intro x
  let C : ChainComplex (ModuleCat 𝕜) ℕ := X.chainComplex (ModuleCat.of 𝕜 𝕜)
  let N : ChainComplex (ModuleCat 𝕜) ℕ := X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)
  let e₀ : HomotopyEquiv C N := X.homotopyEquivNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)
  let q : C ⟶ N := X.toNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)
  let T : Work.Cohomology.dualComplex 𝕜 N ⟶ Work.Cohomology.dualComplex 𝕜 C :=
    Work.Cohomology.dualComplexMap 𝕜 C N q
  let S : Work.Cohomology.dualComplex 𝕜 C ⟶ Work.Cohomology.dualComplex 𝕜 N :=
    Work.Cohomology.dualComplexMap 𝕜 N C e₀.inv
  have hST : Homotopy (S ≫ T) (𝟙 (Work.Cohomology.dualComplex 𝕜 C)) := by
    have h1 := Work.Cohomology.dualHomotopy (R := 𝕜) e₀.homotopyHomInvId
    rw [Work.Cohomology.dualComplexMap_id 𝕜 C,
        Work.Cohomology.dualComplexMap_comp (R := 𝕜) (f := e₀.hom) (g := e₀.inv)] at h1
    exact h1.symm
  have hsurj : Function.Surjective
      (fun y : (Work.Cohomology.dualComplex 𝕜 N).homology s =>
        HomologicalComplex.homologyMap T s y) := by
    intro b
    refine ⟨HomologicalComplex.homologyMap S s b, ?_⟩
    have h2 := Homotopy.homologyMap_eq hST s
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at h2
    have h3 := congrArg (fun (f : (Work.Cohomology.dualComplex 𝕜 C).homology s ⟶
        (Work.Cohomology.dualComplex 𝕜 C).homology s) => f.hom b) h2
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h3
    exact h3
  obtain ⟨y, hy⟩ := hsurj x
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective _).mp
    (inferInstance : Epi ((Work.Cohomology.dualComplex 𝕜 N).homologyπ s)) y
  let ψ : ↑(Work.Cohomology.dualObj 𝕜 N s) := (Work.Cohomology.dualComplex 𝕜 N).iCycles s z
  let α : Work.Cohomology.Cochain 𝕜 X s := (ModuleCat.Hom.hom (T.f s)) ψ
  have hαlin : α = (ModuleCat.Hom.hom (T.f s)) ψ := rfl
  have hαeq : α = ψ.comp (ModuleCat.Hom.hom (q.f s)) := by
    rw [hαlin]
    have hT : ModuleCat.Hom.hom (T.f s)
        = ModuleCat.Hom.hom (Work.Cohomology.dualComplexMapComp 𝕜 C N q s) := by
      rw [Work.Cohomology.dualComplexMap_f]
      rfl
    rw [hT]
    exact Work.Cohomology.dualComplexMapComp_apply' 𝕜 C N q s ψ
  have hψ : (ModuleCat.Hom.hom ((Work.Cohomology.dualComplex 𝕜 N).d s (s+1))) ψ = 0 := by
    have h := congrArg ModuleCat.Hom.hom
      (HomologicalComplex.iCycles_d (Work.Cohomology.dualComplex 𝕜 N) s (s+1))
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    have h' := LinearMap.congr_fun h z
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at h'
    exact h'
  have hψN : ψ.comp (ModuleCat.Hom.hom (N.d (s+1) s)) = 0 := by
    rw [← Work.Cohomology.dualHom_hom_apply 𝕜 (N.d (s+1) s) ψ,
      ← Work.Cohomology.dualComplex_d_self 𝕜 N s]
    exact hψ
  have hα : Work.Cohomology.cochainDiff 𝕜 X α = 0 := by
    have hqc := congrArg ModuleCat.Hom.hom (q.comm (s+1) s)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hqc
    show α.comp (ModuleCat.Hom.hom (C.d (s+1) s)) = 0
    calc α.comp (ModuleCat.Hom.hom (C.d (s+1) s))
        = (ψ.comp (ModuleCat.Hom.hom (q.f s))).comp
            (ModuleCat.Hom.hom (C.d (s+1) s)) := by rw [hαeq]
      _ = ψ.comp ((ModuleCat.Hom.hom (q.f s)).comp
            (ModuleCat.Hom.hom (C.d (s+1) s))) := by rw [LinearMap.comp_assoc]
      _ = ψ.comp ((ModuleCat.Hom.hom (N.d (s+1) s)).comp
            (ModuleCat.Hom.hom (q.f (s+1)))) := by rw [hqc.symm]
      _ = (ψ.comp (ModuleCat.Hom.hom (N.d (s+1) s))).comp
            (ModuleCat.Hom.hom (q.f (s+1))) := by rw [LinearMap.comp_assoc]
      _ = 0 := by rw [hψN, LinearMap.zero_comp]
  refine ⟨α, hα, ?_, ?_⟩
  · intro σ hσ
    have hαeval : α ((X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) σ).hom 1)
        = ψ ((ModuleCat.Hom.hom ((X.toNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f s))
            ((X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) σ).hom 1)) := by
      rw [hαeq, LinearMap.comp_apply]
    have hq1 : (ModuleCat.Hom.hom ((X.toNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)).f s))
        ((X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) σ).hom 1)
        = (X.ιNormalizedChainComplex (R := ModuleCat.of 𝕜 𝕜) σ).hom 1 := by
      have h := congrArg ModuleCat.Hom.hom
        (SSet.ιChainComplex_toNormalizedChainComplex_f X (R := ModuleCat.of 𝕜 𝕜) σ)
      rw [ModuleCat.hom_comp] at h
      exact LinearMap.congr_fun h 1
    rw [show Work.Cohomology.genEval 𝕜 X α σ
        = α ((X.ιChainComplex (R := ModuleCat.of 𝕜 𝕜) σ).hom 1) from rfl,
      hαeval, hq1, SSet.ιNormalizedChainComplex_eq_zero X σ hσ, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    simp
  · have hcyc : Work.Cohomology.cocycleOf 𝕜 X α hα = HomologicalComplex.cyclesMap T s z := by
      apply Work.Cohomology.iCycles_injective 𝕜 X s
      rw [Work.Cohomology.iCycles_cocycleOf 𝕜 X α hα]
      have hci := congrArg ModuleCat.Hom.hom (HomologicalComplex.cyclesMap_i T s)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hci
      have hci' := LinearMap.congr_fun hci z
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hci'
      exact hci'.symm
    have hnat := congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyπ_naturality T s)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hnat
    have h3 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap T s))
        ((ModuleCat.Hom.hom ((Work.Cohomology.dualComplex 𝕜 N).homologyπ s)) z)
        = (ModuleCat.Hom.hom ((Work.Cohomology.dualComplex 𝕜 C).homologyπ s))
          ((ModuleCat.Hom.hom (HomologicalComplex.cyclesMap T s)) z) :=
      LinearMap.congr_fun hnat z
    have hA : Work.Cohomology.cohomologyClassOf 𝕜 X α hα
        = (ModuleCat.Hom.hom ((Work.Cohomology.SSetCochainComplex 𝕜 X).homologyπ s))
            (HomologicalComplex.cyclesMap T s z) := by
      rw [show Work.Cohomology.cohomologyClassOf 𝕜 X α hα
          = (ModuleCat.Hom.hom ((Work.Cohomology.SSetCochainComplex 𝕜 X).homologyπ s))
              (Work.Cohomology.cocycleOf 𝕜 X α hα) from rfl]
      exact congrArg (fun u => (ModuleCat.Hom.hom
        ((Work.Cohomology.SSetCochainComplex 𝕜 X).homologyπ s)) u) hcyc
    have hB : (ModuleCat.Hom.hom ((Work.Cohomology.SSetCochainComplex 𝕜 X).homologyπ s))
            (HomologicalComplex.cyclesMap T s z)
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap T s))
            ((ModuleCat.Hom.hom ((Work.Cohomology.dualComplex 𝕜 N).homologyπ s)) z) := h3.symm
    have hC : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap T s))
            ((ModuleCat.Hom.hom ((Work.Cohomology.dualComplex 𝕜 N).homologyπ s)) z)
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap T s)) y :=
      congrArg (fun u => (ModuleCat.Hom.hom (HomologicalComplex.homologyMap T s)) u) hz
    exact hA.trans (hB.trans (hC.trans hy))

end Work.Pi6.MSS
