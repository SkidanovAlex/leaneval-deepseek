import Mathlib
import Submission.Work.Projective.CPn
import Submission.Work.Projective.cpnV_homotopyEquiv
import Submission.Work.Projective.cpnUV_homotopyEquiv_sphere
import Submission.Work.Projective.PieceCohomology
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.homologyMV
import Submission.Work.Cohomology.mvLeft_zero_injective
import Submission.Work.Cohomology.isZero_homology_biprod
import Submission.Work.Cohomology.homology_biprod_iso
import Submission.Work.Projective.pathConnectedSpace_CP
import Submission.Work.Projective.pathConnectedSpace_cpUV

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-!
# The integral homology of `ℂPⁿ` by Mayer–Vietoris

`Work.Projective.cpn_homology`: the singular homology of `ℂPⁿ` with `ℤ` coefficients is `ℤ` in the
even degrees `k ≤ 2n` and vanishes otherwise.  This is the homology counterpart of
`Work.Projective.cpn_cohomology`, with the same strong induction on `n` and the same cover
`cpU n ∪ cpV n = ℂPⁿ`: the `U`-piece is contractible, the `V`-piece is homotopy equivalent to
`ℂP^{n-1}`, and `U ∩ V` is homotopy equivalent to `S^{2n-1}`.

The three input facts of the induction are `Work.Cohomology.homologyContractible` (the
contractible `U`), `Work.Projective.cpnV_homotopyEquiv` and `Work.Cohomology.sphereHomologyTop`,
`Work.Cohomology.sphereHomologyZero` (the pieces of the intersection).  The Mayer–Vietoris
machinery is that of `Submission/Work/Cohomology/MVSequence.lean` (`HInter`, `HBiprod`, `HSmall`,
`mvδ`, `mvLeft`, `mvRight`, `smallIso`) with the elementary consequences of exactness recorded in
`Submission/Work/Cohomology/homologyMV.lean` (`mvH_isZero`, `mvH_delta_mono`, `mvH_delta_epi`,
`mvH_right_mono`, `mvH_right_epi`, `mvH_one_isZero`) and the injectivity of the zeroth map in
`Submission/Work/Cohomology/mvLeft_zero_injective.lean`.

In degree `k ≥ 2` the argument is:

* if `k = 2 (m+1)` is the top degree, both `H_k(U) ⊞ H_k(V)` and `H_k(U ∩ V)` vanish, so the
  connecting map `H_k(ℂP^{m+1}) → H_{k-1}(U ∩ V)` is an isomorphism onto `H_{2m+1}(S^{2m+1}) = ℤ`;
* if `k` is even and `k ≤ 2m`, then `H_k(U ∩ V)` and `H_{k-1}(U ∩ V)` vanish, so
  `H_k(U) ⊞ H_k(V) → H_k(ℂP^{m+1})` is an isomorphism and `H_k(ℂP^{m+1}) ≅ H_k(ℂP^m) = ℤ`;
* otherwise `H_k(U) ⊞ H_k(V)` and `H_{k-1}(U ∩ V)` vanish, so `H_k(ℂP^{m+1}) = 0` (`mvH_isZero`).

Degree `1` is the only case needing `H_0(U ∩ V) → H_0(U) ⊞ H_0(V)` injective
(`mvH_one_isZero`), and degree `0` is path connectedness.
-/

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology

noncomputable section

/-! ## The model module -/

/-- The module `ℤ` in even degrees `k ≤ 2n`, and `0` otherwise: the expected `k`-th homology
module of `ℂPⁿ`. -/
abbrev cpnHomModel (n k : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (Fin (if Even k ∧ k ≤ 2 * n then 1 else 0) → ℤ)

/-- The model module is a zero object off the even degrees `≤ 2n`. -/
theorem isZero_cpnHomModel {n k : ℕ} (h : ¬(Even k ∧ k ≤ 2 * n)) : IsZero (cpnHomModel n k) := by
  rw [cpnHomModel, if_neg h]
  exact ModuleCat.isZero_of_subsingleton _

/-- In an even degree `≤ 2n` the model module is `ℤ`. -/
theorem cpnHomModel_iso_int {n k : ℕ} (h : Even k ∧ k ≤ 2 * n) :
    Nonempty (cpnHomModel n k ≅ ModuleCat.of ℤ ℤ) := by
  refine ⟨?_⟩
  rw [cpnHomModel, if_pos h]
  exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

/-- The `k`-th homology of a biproduct of chain complexes of `ℤ`-modules is the biproduct of the
homologies.  (The `ChainComplex` version of `Work.Cohomology.homology_biprod_iso`; it lets us
read `H_k(U) ⊞ H_k(V)` off `H_k(U)` and `H_k(V)`.) -/
theorem cpnHom_homology_biprod_iso (C D : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    Nonempty ((C ⊞ D).homology k ≅ C.homology k ⊞ D.homology k) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k
  haveI : PreservesBinaryBiproduct C D F := preservesBinaryBiproduct_of_preservesBiproduct F C D
  exact ⟨F.mapBiprod C D⟩

/-! ## `ℂP⁰` is a point -/

/-- `ℂP⁰` is contractible (its single chart is everything). -/
theorem cpnHom_contractibleSpace_CP_zero : ContractibleSpace (CP 0) := by
  have huniv : chartSet (0 : Fin 1) = (Set.univ : Set (CP 0)) := by
    refine Set.eq_univ_of_forall fun p => ?_
    obtain ⟨i, hi⟩ := exists_mem_chartSet p
    have h : i = 0 := Fin.eq_zero i
    rwa [h] at hi
  haveI : ContractibleSpace ↥(chartSet (0 : Fin 1)) := inferInstance
  exact ((Homeomorph.setCongr huniv).trans (Homeomorph.Set.univ (CP 0))).symm.contractibleSpace

/-- The homology of `ℂP⁰` (a point): `ℤ` in degree `0` and `0` above. -/
theorem cpnHomologyZero (k : ℕ) :
    Nonempty ((singularChains ℤ (CPSpace 0)).homology k ≅ cpnHomModel 0 k) := by
  rcases k with _ | k
  · haveI : PathConnectedSpace ↥(CPSpace 0) := pathConnectedSpace_CP 0
    haveI : IsIso (TopCat.singularHomology₀ε (CPSpace 0) (ModuleCat.of ℤ ℤ)) := inferInstance
    obtain ⟨eZ⟩ := cpnHomModel_iso_int (n := 0) (k := 0) ⟨⟨0, rfl⟩, by omega⟩
    exact ⟨asIso (TopCat.singularHomology₀ε (CPSpace 0) (ModuleCat.of ℤ ℤ)) ≪≫ eZ.symm⟩
  · haveI : ContractibleSpace ↥(CPSpace 0) := cpnHom_contractibleSpace_CP_zero
    refine ⟨IsZero.iso (homologyContractible (k + 1) (by omega)) ?_⟩
    exact isZero_cpnHomModel (by rintro ⟨he, _⟩; obtain ⟨c, hc⟩ := he; omega)

/-! ## The Mayer–Vietoris step -/

/-- **The Mayer–Vietoris step**: the homology of `ℂP^{m+1}` from that of `ℂP^m`. -/
theorem cpnHomologyStep (m : ℕ)
    (ih : ∀ k, Nonempty ((singularChains ℤ (CPSpace m)).homology k ≅ cpnHomModel m k)) (k : ℕ) :
    Nonempty ((singularChains ℤ (CPSpace (m + 1))).homology k ≅ cpnHomModel (m + 1) k) := by
  set U : Set (CPSpace (m + 1)) := cpU (m + 1) with _hUdef
  set V : Set (CPSpace (m + 1)) := cpV (m + 1) with _hVdef
  have hUopen : IsOpen U := isOpen_cpU (m + 1)
  have hVopen : IsOpen V := isOpen_cpV (m + 1)
  have hcov : U ∪ V = Set.univ := cpU_union_cpV (m + 1)
  haveI hUcontr : ContractibleSpace ↥U := contractibleSpace_chartSet (m + 1) 0
  haveI hUVpc : PathConnectedSpace ↥(U ∩ V) := pathConnectedSpace_cpUV m
  -- `U` is contractible, so its positive-degree homology vanishes
  have hUzero : ∀ j, 0 < j → IsZero ((singularChains ℤ (TopCat.of ↥U)).homology j) :=
    fun j hj => homologyContractible j hj
  -- a `j` on which the `V`-piece may be non-trivial is positive
  have hpos : ∀ j, ¬(Even j ∧ j ≤ 2 * m) → 0 < j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact absurd ⟨⟨0, rfl⟩, by omega⟩ hj
    · exact h
  -- `V` is homotopy equivalent to `ℂP^m`, so its homology is that of `ℂP^m`
  have hVh : ∀ j, Nonempty ((singularChains ℤ (TopCat.of ↥V)).homology j ≅ cpnHomModel m j) := by
    intro j
    obtain ⟨e1⟩ := homologyIso_of_homotopyEquiv (cpnV_homotopyEquiv m).some j
    obtain ⟨e2⟩ := ih j
    exact ⟨e1 ≪≫ e2⟩
  have hVzero : ∀ j, ¬(Even j ∧ j ≤ 2 * m) →
      IsZero ((singularChains ℤ (TopCat.of ↥V)).homology j) := by
    intro j hj
    obtain ⟨e⟩ := hVh j
    exact IsZero.of_iso (isZero_cpnHomModel hj) e
  -- `U ∩ V` is homotopy equivalent to `S^{2m+1}`
  have hInterZero : ∀ j, j ≠ 0 → j ≠ 2 * m + 1 → IsZero (HInter U V j) := by
    intro j hj0 hjt
    obtain ⟨e1⟩ := homologyIso_of_homotopyEquiv (cpnUV_homotopyEquiv_sphere (m + 1)).some j
    exact IsZero.of_iso (sphereHomologyZero (2 * m + 1) j (by omega) hj0 hjt) e1
  have hInterTop : Nonempty (HInter U V (2 * m + 1) ≅ ModuleCat.of ℤ ℤ) := by
    obtain ⟨e1⟩ :=
      homologyIso_of_homotopyEquiv (cpnUV_homotopyEquiv_sphere (m + 1)).some (2 * m + 1)
    obtain ⟨e2⟩ := sphereHomologyTop (2 * m + 1) (by omega)
    exact ⟨e1 ≪≫ e2⟩
  -- the biproduct `H_j(U) ⊞ H_j(V)` vanishes away from the even degrees `j ≤ 2m`
  have hBiprodZero : ∀ j, ¬(Even j ∧ j ≤ 2 * m) → IsZero (HBiprod U V j) :=
    fun j hj => isZero_homology_biprod j (hUzero j (hpos j hj)) (hVzero j hj)
  rcases k with _ | _ | k
  · -- degree `0`
    haveI : PathConnectedSpace ↥(CPSpace (m + 1)) := pathConnectedSpace_CP (m + 1)
    haveI : IsIso (TopCat.singularHomology₀ε (CPSpace (m + 1)) (ModuleCat.of ℤ ℤ)) := inferInstance
    obtain ⟨eZ⟩ := cpnHomModel_iso_int (n := m + 1) (k := 0) ⟨⟨0, rfl⟩, by omega⟩
    exact ⟨asIso (TopCat.singularHomology₀ε (CPSpace (m + 1)) (ModuleCat.of ℤ ℤ)) ≪≫ eZ.symm⟩
  · -- degree `1`
    have hB : IsZero (HBiprod U V 1) :=
      hBiprodZero 1 (by rintro ⟨he, _⟩; obtain ⟨c, hc⟩ := he; omega)
    have hl : Mono (HomologicalComplex.homologyMap (mvLeft U V) 0) :=
      (ModuleCat.mono_iff_injective _).mpr (mvLeft_zero_injective U V)
    have hsm : IsZero (HSmall U V 1) := mvH_one_isZero U V hB hl
    refine ⟨IsZero.iso (IsZero.of_iso hsm (smallIso U V hUopen hVopen hcov 1).symm) ?_⟩
    exact isZero_cpnHomModel (by rintro ⟨he, _⟩; obtain ⟨c, hc⟩ := he; omega)
  · -- degree `k + 2`
    by_cases htop : k + 2 = 2 * (m + 1)
    · -- the top degree `2m + 2`: the connecting map is an isomorphism
      have hk1 : k + 1 = 2 * m + 1 := by omega
      have hBtop : IsZero (HBiprod U V (k + 2)) :=
        hBiprodZero (k + 2) (by rintro ⟨he, hle⟩; omega)
      have hB1 : IsZero (HBiprod U V (k + 1)) :=
        hBiprodZero (k + 1) (by rintro ⟨he, _⟩; obtain ⟨c, hc⟩ := he; omega)
      haveI hm : Mono (mvδ U V (k + 1)) := mvH_delta_mono U V (k + 1) hBtop
      haveI he : Epi (mvδ U V (k + 1)) := mvH_delta_epi U V (k + 1) hB1
      haveI hiso : IsIso (mvδ U V (k + 1)) := isIso_of_mono_of_epi _
      have hInterTop' : Nonempty (HInter U V (k + 1) ≅ ModuleCat.of ℤ ℤ) := by
        rw [hk1]; exact hInterTop
      have hZZ : Nonempty ((singularChains ℤ (CPSpace (m + 1))).homology (k + 2) ≅
          ModuleCat.of ℤ ℤ) :=
        ⟨(smallIso U V hUopen hVopen hcov (k + 2)).symm ≪≫
          asIso (mvδ U V (k + 1)) ≪≫ hInterTop'.some⟩
      obtain ⟨e⟩ := hZZ
      obtain ⟨eZ⟩ := cpnHomModel_iso_int (n := m + 1) (k := k + 2) ⟨⟨m + 1, by omega⟩, by omega⟩
      exact ⟨e ≪≫ eZ.symm⟩
    · by_cases hmid : Even (k + 2) ∧ k + 2 ≤ 2 * m
      · -- an even degree `≤ 2m`: the second Mayer–Vietoris map is an isomorphism
        obtain ⟨c, hc⟩ := hmid.1
        have hne : k + 2 ≠ 2 * m + 1 := by omega
        have hI0 : IsZero (HInter U V (k + 2)) := hInterZero (k + 2) (by omega) hne
        have hI1 : IsZero (HInter U V (k + 1)) := hInterZero (k + 1) (by omega) (by omega)
        haveI hm : Mono (HomologicalComplex.homologyMap (mvRight U V) (k + 2)) :=
          mvH_right_mono U V (k + 2) hI0
        haveI he : Epi (HomologicalComplex.homologyMap (mvRight U V) (k + 2)) :=
          mvH_right_epi U V (k + 1) hI1
        haveI hiso : IsIso (HomologicalComplex.homologyMap (mvRight U V) (k + 2)) :=
          isIso_of_mono_of_epi _
        obtain ⟨ebip⟩ := cpnHom_homology_biprod_iso (singularChains ℤ (TopCat.of ↥U))
          (singularChains ℤ (TopCat.of ↥V)) (k + 2)
        obtain ⟨eV⟩ := hVh (k + 2)
        obtain ⟨eZm⟩ := cpnHomModel_iso_int (n := m) (k := k + 2) hmid
        have hU2 : IsZero ((singularChains ℤ (TopCat.of ↥U)).homology (k + 2)) :=
          hUzero (k + 2) (by omega)
        have hZZ : Nonempty ((singularChains ℤ (CPSpace (m + 1))).homology (k + 2) ≅
            ModuleCat.of ℤ ℤ) :=
          ⟨(smallIso U V hUopen hVopen hcov (k + 2)).symm ≪≫
            (asIso (HomologicalComplex.homologyMap (mvRight U V) (k + 2))).symm ≪≫ ebip ≪≫
            (isoZeroBiprod hU2).symm ≪≫ eV ≪≫ eZm⟩
        obtain ⟨e⟩ := hZZ
        obtain ⟨eZ⟩ := cpnHomModel_iso_int (n := m + 1) (k := k + 2) ⟨hmid.1, by omega⟩
        exact ⟨e ≪≫ eZ.symm⟩
      · -- every other degree: `H_{k+2}(ℂP^{m+1}) = 0`
        have hnot : ¬(Even (k + 2) ∧ k + 2 ≤ 2 * (m + 1)) := by
          rintro ⟨hev, hle⟩
          obtain ⟨c, hc⟩ := hev
          rcases Nat.lt_or_ge (2 * m) (k + 2) with hlt | hge
          · exact htop (by omega)
          · exact hmid ⟨⟨c, hc⟩, hge⟩
        have hI1 : IsZero (HInter U V (k + 1)) :=
          hInterZero (k + 1) (by omega) (by omega)
        have hB : IsZero (HBiprod U V (k + 2)) := hBiprodZero (k + 2) hmid
        have hsm : IsZero (HSmall U V (k + 2)) := mvH_isZero U V (k + 2) (by omega) hB hI1
        refine ⟨IsZero.iso (IsZero.of_iso hsm (smallIso U V hUopen hVopen hcov (k + 2)).symm) ?_⟩
        exact isZero_cpnHomModel hnot

/-! ## The main theorem -/

/-- The homology of `ℂPⁿ` with `ℤ` coefficients is `ℤ` in even degrees `k ≤ 2n` and `0`
otherwise. -/
theorem cpnHomology_aux (n k : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ (Work.Projective.CPSpace n)).homology k ≅
      cpnHomModel n k) := by
  revert k
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    rcases n with _ | m
    · exact cpnHomologyZero k
    · exact cpnHomologyStep m (ih m (by omega)) k

/-- The homology of `ℂPⁿ` with `ℤ` coefficients is `ℤ` in even degrees `k ≤ 2n` and `0`
otherwise (in particular it is torsion-free).  Same Mayer–Vietoris induction as
`Work.Projective.cpn_cohomology`, in homology (`Work.Cohomology.mvShort`, `mvδ`, `smallIso`,
`homologyContractible`, `sphereHomologyTop`, `sphereHomologyZero`); the `n = 2` case is
`Work.Projective.singularHomology_four_cp2`. -/
theorem cpn_homology (n k : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ (Work.Projective.CPSpace n)).homology k ≅
      ModuleCat.of ℤ (Fin (if Even k ∧ k ≤ 2 * n then 1 else 0) → ℤ)) :=
  cpnHomology_aux n k

end

end Work.Projective
