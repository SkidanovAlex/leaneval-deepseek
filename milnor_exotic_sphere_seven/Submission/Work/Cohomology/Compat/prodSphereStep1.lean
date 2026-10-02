import Mathlib
import Submission.Work.Cohomology.Compat.prodSphereDefs
import Submission.Work.Cohomology.Compat.prodSphereAux
import Submission.Work.Cohomology.Compat.homotopyEquiv_A1set
import Submission.Work.Cohomology.Compat.homotopyEquiv_B1set
import Submission.Work.Cohomology.Compat.contractible_A1set_inter_B1set
import Submission.Work.Cohomology.mvLeft_zero_injective
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.homologyContractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Step 1 of the computation of `Hₙ(Sᵖ × Sᵍ)`: the punctured product

The cover `A1set ∪ B1set = Yset` of `Sᵖ × Sᵍ \ {pt}` has contractible intersection, so the map
`mvRightX` from the biproduct of the two pieces to `Hₙ(Yset)` is an isomorphism, and hence
`Hₙ(Sᵖ × Sᵍ \ {pt}) ≅ Hₙ(Sᵖ) ⊞ Hₙ(Sᵍ)` for `n ≥ 1`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
open CategoryTheory AlgebraicTopology Limits
open scoped Topology
namespace Work.Cohomology.Compat
noncomputable section

/-- **Step 1**: the map from the biproduct of the two pieces to the punctured product is an
isomorphism on homology. -/
theorem isIso_mvRightX_A1B1 (p q k : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    IsIso (mvRightX (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q) (isOpen_A1set p q)
      (isOpen_B1set p q) (A1set_union_B1set p q) (k + 1)) := by
  haveI hcontr : ContractibleSpace ↥(A1set p q ∩ B1set p q) :=
    contractible_A1set_inter_B1set p q
  have hf : HomologicalComplex.homologyMap (mvLeft (X := TopCat.of ↥(Yset p q))
      (A1set p q) (B1set p q)) (k + 1) = 0 :=
    IsZero.eq_zero_of_src (homologyContractible (k + 1) (by omega)) _
  have h1 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₁ (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q) k)
  have h2 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₂ (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q) (k + 1))
  have h3 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₃ (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q) k)
  have hf' : Function.Injective (HomologicalComplex.homologyMap (mvLeft
      (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q)) k).hom := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      haveI hpc : PathConnectedSpace ↥(A1set p q ∩ B1set p q) := inferInstance
      exact @mvLeft_zero_injective (TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q) hpc
    · exact injective_of_isZero_src (HomologicalComplex.homologyMap (mvLeft
        (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q)) k)
        (homologyContractible k (by omega))
  haveI : IsIso (HomologicalComplex.homologyMap (mvRight (X := TopCat.of ↥(Yset p q))
      (A1set p q) (B1set p q)) (k + 1)) :=
    isIso_of_exact_of_zero_of_inj
      (A := HInter (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q) (k + 1))
      (B := HBiprod (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q) (k + 1))
      (M := HSmall (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q) (k + 1))
      (C := HInter (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q) k)
      (D := HBiprod (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q) k)
      _ _ _ _ h1 h2 h3 hf hf'
  rw [mvRightX]
  infer_instance

/-- **Step 1, consequence**: `Hₙ(Sᵖ × Sᵍ \ {pt}) ≅ Hₙ(Sᵖ) ⊞ Hₙ(Sᵍ)` for `n ≥ 1`. -/
theorem nonempty_homology_Yset (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    Nonempty ((singularChains ℤ (TopCat.of ↥(Yset p q))).homology n ≅
      (singularChains ℤ (sphTop (p+1))).homology n ⊞
        (singularChains ℤ (sphTop (q+1))).homology n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  haveI := isIso_mvRightX_A1B1 p q k hp hq
  obtain ⟨eA⟩ := homotopyEquiv_A1set p q
  obtain ⟨eA'⟩ := homologyIso_of_homotopyEquiv eA (k + 1)
  obtain ⟨eB⟩ := homotopyEquiv_B1set p q
  obtain ⟨eB'⟩ := homologyIso_of_homotopyEquiv eB (k + 1)
  refine ⟨?_⟩
  refine (asIso (mvRightX (X := TopCat.of ↥(Yset p q)) (A1set p q) (B1set p q)
      (isOpen_A1set p q) (isOpen_B1set p q) (A1set_union_B1set p q) (k + 1))).symm
    ≪≫ ?_
  refine (homologyBiprodIso (singularChains ℤ (TopCat.of ↥(A1set p q)))
      (singularChains ℤ (TopCat.of ↥(B1set p q))) (k + 1)) ≪≫ ?_
  refine (biprod.mapIso eA' eB' :
    (singularChains ℤ (TopCat.of ↥(A1set p q))).homology (k + 1) ⊞
        (singularChains ℤ (TopCat.of ↥(B1set p q))).homology (k + 1) ≅
      (singularChains ℤ (sphTop (q+1))).homology (k + 1) ⊞
        (singularChains ℤ (sphTop (p+1))).homology (k + 1)) ≪≫ ?_
  exact biprodSwap _ _

end
end Work.Cohomology.Compat
