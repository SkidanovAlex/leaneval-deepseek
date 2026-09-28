import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.mvCochainShortExact
import Submission.Work.Cohomology.mvCochainDegreewise
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.homotopyEquivDual
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.smallChainsHomotopyEquiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial Topology

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-! ## 1. The cohomological Mayer–Vietoris long exact sequence -/

/-- The homology-level form of the biproduct identity `fst ≫ inl + snd ≫ inr = 𝟙`, for
`ℕ`-indexed cochain complexes of `ℤ`-modules. -/
theorem coh_homologyMap_total (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) k
        ≫ HomologicalComplex.homologyMap (biprod.inl (X := C) (Y := D)) k
      + HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) k
        ≫ HomologicalComplex.homologyMap (biprod.inr (X := C) (Y := D)) k
    = 𝟙 ((C ⊞ D).homology k) := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_add, biprod.total, HomologicalComplex.homologyMap_id]

/-- The homology of a biproduct of cochain complexes vanishes in degree `k` when both factors do -/
theorem isZero_coh_homology_biprod (C D : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (hC : IsZero (C.homology k)) (hD : IsZero (D.homology k)) :
    IsZero ((C ⊞ D).homology k) := by
  rw [IsZero.iff_id_eq_zero, ← coh_homologyMap_total (C := C) (D := D) k]
  rw [show HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) k = 0 from
        IsZero.eq_zero_of_tgt hC _,
      show HomologicalComplex.homologyMap (biprod.inl (X := C) (Y := D)) k = 0 from
        IsZero.eq_zero_of_src hC _,
      show HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) k = 0 from
        IsZero.eq_zero_of_tgt hD _,
      show HomologicalComplex.homologyMap (biprod.inr (X := C) (Y := D)) k = 0 from
        IsZero.eq_zero_of_src hD _]
  simp

/-- **The cochain Mayer–Vietoris sequence is short exact** (with the explicit maps
`mvCochainF`, `mvCochainG`). -/
theorem mvCochainSES (U V : Set X) :
    (ShortComplex.mk (mvCochainF U V) (mvCochainG U V) (mvCochainComp U V)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => mvCochainDegreewise U V n)

/-- **The connecting homomorphism** of the cohomological Mayer–Vietoris sequence,
`Hⁿ(U ∩ V) ⟶ Hⁿ⁺¹(C^{U,V})`. -/
noncomputable def mvCohδ (U V : Set X) (n : ℕ) :
    (cochainUV U V).homology n ⟶ (dualComplex ℤ (smallChains U V)).homology (n + 1) :=
  (mvCochainSES U V).δ n (n + 1) (by simp [ComplexShape.up])

/-- Exactness of the cohomological Mayer–Vietoris sequence at `Hⁿ⁺¹(C^{U,V})`. -/
theorem mvCoh_H_exact₁ (U V : Set X) (n : ℕ) :
    (ShortComplex.mk (mvCohδ U V n)
      (HomologicalComplex.homologyMap (mvCochainF U V) (n + 1))
      (by
        show mvCohδ U V n ≫ HomologicalComplex.homologyMap (mvCochainF U V) (n + 1) = 0
        exact (mvCochainSES U V).δ_comp n (n + 1) (by simp [ComplexShape.up]))).Exact :=
  (mvCochainSES U V).homology_exact₁ n (n + 1) (by simp [ComplexShape.up])

/-- Exactness of the cohomological Mayer–Vietoris sequence at `Hⁿ(U ∩ V)`. -/
theorem mvCoh_H_exact₃ (U V : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (mvCochainG U V) n) (mvCohδ U V n)
      (by
        show HomologicalComplex.homologyMap (mvCochainG U V) n ≫ mvCohδ U V n = 0
        exact (mvCochainSES U V).comp_δ n (n + 1) (by simp [ComplexShape.up]))).Exact :=
  (mvCochainSES U V).homology_exact₃ n (n + 1) (by simp [ComplexShape.up])

/-- **The connecting map is an isomorphism** when the two intermediate cohomology groups of the
biproduct term vanish. -/
theorem mvCohδ_isIso (U V : Set X) (n : ℕ)
    (hLn : IsZero ((cochainU U V ⊞ cochainV U V).homology n))
    (hLm : IsZero ((cochainU U V ⊞ cochainV U V).homology (n + 1))) :
    IsIso (mvCohδ U V n) := by
  have hg : (ShortComplex.mk (mvCohδ U V n)
      (HomologicalComplex.homologyMap (mvCochainF U V) (n + 1))
      (by
        show mvCohδ U V n ≫ HomologicalComplex.homologyMap (mvCochainF U V) (n + 1) = 0
        exact (mvCochainSES U V).δ_comp n (n + 1) (by simp [ComplexShape.up]))).g = 0 :=
    IsZero.eq_zero_of_tgt hLm _
  haveI : Epi (mvCohδ U V n) :=
    (ShortComplex.exact_iff_epi _ hg).1 (mvCoh_H_exact₁ U V n)
  have hf : (ShortComplex.mk (HomologicalComplex.homologyMap (mvCochainG U V) n) (mvCohδ U V n)
      (by
        show HomologicalComplex.homologyMap (mvCochainG U V) n ≫ mvCohδ U V n = 0
        exact (mvCochainSES U V).comp_δ n (n + 1) (by simp [ComplexShape.up]))).f = 0 :=
    IsZero.eq_zero_of_src hLn _
  haveI : Mono (mvCohδ U V n) :=
    (ShortComplex.exact_iff_mono _ hf).1 (mvCoh_H_exact₃ U V n)
  exact isIso_of_mono_of_epi _

/-! ## 2. Identifying the cohomology of the small chains with the singular cohomology -/

/-- The dual of the small-chains homotopy equivalence identifies the cohomology of the dual of the
small chains with the singular cohomology of `X`. -/
theorem cohSmallIso (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (n : ℕ) :
    Nonempty (singularCohomology ℤ n X ≅ (dualComplex ℤ (smallChains U V)).homology n) := by
  obtain ⟨e, _⟩ := smallChainsHomotopyEquiv U V hU hV hcov
  obtain ⟨e'⟩ := homotopyEquivDual ℤ e
  exact ⟨e'.toHomologyIso n⟩

/-! ## 3. The Mayer–Vietoris step for a cover by two contractible sets -/

/-- **The Mayer–Vietoris isomorphism in cohomology.**  For an open cover `X = U ∪ V` by two
contractible sets and `k ≥ 1`, the connecting homomorphism of the cohomological Mayer–Vietoris
sequence is an isomorphism `H^k(U ∩ V) ≅ H^(k+1)(X)`. -/
theorem mvCohIso {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) [ContractibleSpace ↥U] [ContractibleSpace ↥V]
    (k : ℕ) (hk : 1 ≤ k) :
    Nonempty (singularCohomology ℤ (k + 1) X ≅ singularCohomology ℤ k (TopCat.of ↥(U ∩ V))) := by
  haveI hUn : IsZero ((cochainU U V).homology k) := by
    have h := contractible ℤ (TopCat.of U) (k - 1)
    rw [Nat.sub_add_cancel hk] at h
    exact h
  haveI hVn : IsZero ((cochainV U V).homology k) := by
    have h := contractible ℤ (TopCat.of V) (k - 1)
    rw [Nat.sub_add_cancel hk] at h
    exact h
  haveI hUm : IsZero ((cochainU U V).homology (k + 1)) := contractible ℤ (TopCat.of U) k
  haveI hVm : IsZero ((cochainV U V).homology (k + 1)) := contractible ℤ (TopCat.of V) k
  haveI hLn : IsZero ((cochainU U V ⊞ cochainV U V).homology k) :=
    isZero_coh_homology_biprod _ _ k hUn hVn
  haveI hLm : IsZero ((cochainU U V ⊞ cochainV U V).homology (k + 1)) :=
    isZero_coh_homology_biprod _ _ (k + 1) hUm hVm
  haveI hiso : IsIso (mvCohδ U V k) := mvCohδ_isIso U V k hLn hLm
  obtain ⟨e⟩ := cohSmallIso (X := X) U V hU hV hcov (k + 1)
  exact ⟨e ≪≫ (asIso (mvCohδ U V k)).symm⟩

/-- A homotopy equivalence of topological spaces induces an isomorphism on singular cohomology. -/
theorem cohomologyIso_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Nonempty (singularCohomology ℤ n (TopCat.of X) ≅ singularCohomology ℤ n (TopCat.of Y)) := by
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := e.right_inv.some
  haveI := homotopyEquiv ℤ (TopCat.of X) (TopCat.of Y) f g h1 h2 n
  exact ⟨(CategoryTheory.asIso (singularCohomologyMap ℤ (TopCat.of X) (TopCat.of Y) f n)).symm⟩

end

end Work.Cohomology
