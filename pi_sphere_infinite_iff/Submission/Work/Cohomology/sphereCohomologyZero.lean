import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.totallyDisconnected
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.mvCochainDefs
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereInUnitOneHomologyZero
import Submission.Work.Cohomology.pathConnected_band
import Submission.Work.Cohomology.epi_singularCohomologyMap_zero

set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial Topology

namespace Work.Cohomology

noncomputable section

/-! # Vanishing of the singular cohomology of spheres off degrees `0` and `n` -/

/-- `chainInclU` is the chain map induced by the inclusion `U ∩ V ↪ U`. -/
lemma chainInclU_eq_chainMap {X : TopCat} (U V : Set X) :
    chainInclU U V = chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U) (inclUVU U V) := rfl

/-- The dual of `chainInclU` is the cochain pullback induced by the inclusion. -/
lemma dualComplexMap_chainInclU {X : TopCat} (U V : Set X) :
    dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V))) (singularChains ℤ (TopCat.of U))
      (chainInclU U V)
      = dualChainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U) (inclUVU U V) := by
  rw [chainInclU_eq_chainMap]
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  rfl

/-- The first component of `mvCochainG` is the dual of `chainInclU`. -/
lemma biprod_inl_mvCochainG {X : TopCat} (U V : Set X) :
    (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) ≫ mvCochainG U V
      = dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
          (singularChains ℤ (TopCat.of U)) (chainInclU U V) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, mvCochainG_inl]

/-- If `U ∩ V` is path-connected, then `mvCochainG` is an epimorphism in degree `0`. -/
theorem epi_homologyMap_mvCochainG_zero {X : TopCat} (U V : Set X)
    [PathConnectedSpace ↥(U ∩ V)] :
    Epi (HomologicalComplex.homologyMap (mvCochainG U V) 0) := by
  have h1 : Epi (HomologicalComplex.homologyMap
      (dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
        (singularChains ℤ (TopCat.of U)) (chainInclU U V)) 0) := by
    rw [dualComplexMap_chainInclU]
    exact epi_singularCohomologyMap_zero (X := TopCat.of ↥(U ∩ V)) (Y := TopCat.of U)
      (inclUVU U V)
  have h2 : HomologicalComplex.homologyMap
        (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) 0
      ≫ HomologicalComplex.homologyMap (mvCochainG U V) 0
      = HomologicalComplex.homologyMap (dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
          (singularChains ℤ (TopCat.of U)) (chainInclU U V)) 0 := by
    rw [← HomologicalComplex.homologyMap_comp, biprod_inl_mvCochainG]
  have h3 : Epi (HomologicalComplex.homologyMap
      (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) 0
      ≫ HomologicalComplex.homologyMap (mvCochainG U V) 0) := h2 ▸ h1
  exact @epi_of_epi _ _ _ _ _
    (HomologicalComplex.homologyMap (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) 0)
    (HomologicalComplex.homologyMap (mvCochainG U V) 0) h3

/-- `H¹` of `Sⁿ` vanishes for `n ≥ 2`: the Mayer–Vietoris connecting map out of `H⁰(U ∩ V)` is
surjective onto `H¹`, and it is zero because the restriction
`H⁰(U) ⊞ H⁰(V) → H⁰(U ∩ V)` is surjective (both caps are contractible, and the intersection is
path-connected). -/
theorem sphereCohomologyOne_vanishing (n : ℕ) (hn : 2 ≤ n) :
    IsZero (singularCohomology ℤ 1 (sphTop (n + 1))) := by
  haveI hA : ContractibleSpace ↥(capA n) := contractibleSpace_capA n
  haveI hB : ContractibleSpace ↥(capB n) := contractibleSpace_capB n
  haveI hp : PathConnectedSpace ↥(capA n ∩ capB n) := pathConnected_band n hn
  have hbU : IsZero ((cochainU (capA n) (capB n)).homology 1) :=
    contractible ℤ (TopCat.of ↥(capA n)) 0
  have hbV : IsZero ((cochainV (capA n) (capB n)).homology 1) :=
    contractible ℤ (TopCat.of ↥(capB n)) 0
  haveI hb : IsZero ((cochainU (capA n) (capB n) ⊞ cochainV (capA n) (capB n)).homology 1) :=
    isZero_coh_homology_biprod _ _ 1 hbU hbV
  haveI hE : Epi (mvCohδ (capA n) (capB n) 0) := by
    have h := mvCoh_H_exact₁ (capA n) (capB n) 0
    have hg : (ShortComplex.mk (mvCohδ (capA n) (capB n) 0)
        (HomologicalComplex.homologyMap (mvCochainF (capA n) (capB n)) (0 + 1))
        (by
          show mvCohδ (capA n) (capB n) 0
            ≫ HomologicalComplex.homologyMap (mvCochainF (capA n) (capB n)) (0 + 1) = 0
          exact (mvCochainSES (capA n) (capB n)).δ_comp 0 1 (by simp [ComplexShape.up]))).g = 0 :=
      IsZero.eq_zero_of_tgt hb _
    exact (ShortComplex.exact_iff_epi _ hg).1 h
  have h0epi : Epi (HomologicalComplex.homologyMap (mvCochainG (capA n) (capB n)) 0) :=
    epi_homologyMap_mvCochainG_zero (capA n) (capB n)
  haveI := h0epi
  have hδ0 : mvCohδ (capA n) (capB n) 0 = 0 := by
    have hcomp : HomologicalComplex.homologyMap (mvCochainG (capA n) (capB n)) 0
        ≫ mvCohδ (capA n) (capB n) 0 = 0 :=
      (mvCochainSES (capA n) (capB n)).comp_δ 0 1 (by simp [ComplexShape.up])
    exact (cancel_epi _).mp (hcomp.trans (comp_zero).symm)
  have hz : IsZero ((dualComplex ℤ (smallChains (capA n) (capB n))).homology 1) := by
    rw [IsZero.iff_id_eq_zero]
    refine (cancel_epi (mvCohδ (capA n) (capB n) 0)).mp ?_
    rw [hδ0]; simp
  obtain ⟨e⟩ := cohSmallIso (X := sphTop (n + 1)) (capA n) (capB n)
    (isOpen_capA n) (isOpen_capB n) (capA_union_capB n) 1
  exact IsZero.of_iso hz e

/-- The positive-degree singular cohomology of `S⁰` vanishes: `S⁰` is totally disconnected. -/
theorem sphereCohomologyZero_Sph1 (k : ℕ) :
    IsZero (singularCohomology ℤ (k + 1) (sphTop 1)) := by
  haveI : Finite ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    finite_metricSphere_fin_one.to_subtype
  haveI : TotallyDisconnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    inferInstance
  have h : IsZero (singularCohomology ℤ (k + 1)
      (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))) :=
    totallyDisconnected ℤ _ k
  obtain ⟨e⟩ := cohomologyIso_of_homotopyEquiv
    (Homeomorph.setCongr (sphereSet_eq 1)).toHomotopyEquiv (k + 1)
  exact IsZero.of_iso h e.symm

set_option maxHeartbeats 800000 in
/-- **Vanishing of the cohomology of `Sⁿ` off degrees `0` and `n`**, for the model sphere
`sphTop (n+1) = Sⁿ ⊆ ℝ^(n+1)`. -/
theorem sphereCohomologyZero_aux (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, k ≠ 0 → k ≠ n → IsZero (singularCohomology ℤ k (sphTop (n + 1))) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k h0 hnk
    rcases k with _ | _ | k
    · exact (h0 rfl).elim
    · exact sphereCohomologyOne_vanishing n (by omega)
    · rcases eq_or_lt_of_le hn with hn1 | hn2
      · subst hn1
        haveI hA : ContractibleSpace ↥(capA 1) := contractibleSpace_capA 1
        haveI hB : ContractibleSpace ↥(capB 1) := contractibleSpace_capB 1
        obtain ⟨e1⟩ := mvCohIso (X := sphTop 2) (capA 1) (capB 1) (isOpen_capA 1) (isOpen_capB 1)
          (capA_union_capB 1) (k + 1) (by omega)
        obtain ⟨e2⟩ := cohomologyIso_of_homotopyEquiv (bandHomotopyEquiv 1 le_rfl).some (k + 1)
        rw [band] at e2
        exact IsZero.of_iso (IsZero.of_iso (sphereCohomologyZero_Sph1 k) e2) e1
      · haveI hA : ContractibleSpace ↥(capA n) := contractibleSpace_capA n
        haveI hB : ContractibleSpace ↥(capB n) := contractibleSpace_capB n
        obtain ⟨e1⟩ := mvCohIso (X := sphTop (n + 1)) (capA n) (capB n) (isOpen_capA n)
          (isOpen_capB n) (capA_union_capB n) (k + 1) (by omega)
        obtain ⟨e2⟩ := cohomologyIso_of_homotopyEquiv (bandHomotopyEquiv n (by omega)).some (k + 1)
        rw [band] at e2
        have hIH := ih (n - 1) (by omega) (by omega) (k + 1) (by omega) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hIH
        exact IsZero.of_iso (IsZero.of_iso hIH e2) e1

/-- **Vanishing of the singular cohomology of the sphere**: for `n ≥ 1` and `k ≠ 0, n`, the
`k`-th singular cohomology of `Sⁿ = Metric.sphere (0 : ℝ^(n+1)) 1` with `ℤ` coefficients is the
zero module. -/
theorem sphereCohomologyZero (n k : ℕ) (hn : 1 ≤ n) (h0 : k ≠ 0) (hnk : k ≠ n) :
    CategoryTheory.Limits.IsZero
      (Work.Cohomology.singularCohomology ℤ k
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) := by
  obtain ⟨e⟩ := cohomologyIso_of_homotopyEquiv
    (Homeomorph.setCongr (sphereSet_eq (n + 1))).toHomotopyEquiv k
  exact IsZero.of_iso (sphereCohomologyZero_aux n hn k h0 hnk) e

end

end Work.Cohomology
