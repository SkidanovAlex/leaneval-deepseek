import Mathlib
import Submission.Work.Projective.CPn
import Submission.Work.Projective.cpnV_homotopyEquiv
import Submission.Work.Projective.cpnUV_homotopyEquiv_sphere
import Submission.Work.Projective.PieceCohomology
import Submission.Work.Projective.pathConnectedSpace_CP
import Submission.Work.Projective.pathConnectedSpace_cpUV
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.sphereCohomologyZero
import Submission.Work.Cohomology.homology_biprod_iso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology

noncomputable section

/-! ## The model module -/

/-- The module `ℤ` in even degrees `k ≤ 2n`, and `0` otherwise: the expected `k`-th cohomology
module of `ℂPⁿ`. -/
abbrev cpnModel (n k : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (Fin (if Even k ∧ k ≤ 2 * n then 1 else 0) → ℤ)

/-- The model module is a zero object off the even degrees `≤ 2n`. -/
theorem isZero_cpnModel {n k : ℕ} (h : ¬(Even k ∧ k ≤ 2 * n)) : IsZero (cpnModel n k) := by
  rw [cpnModel, if_neg h]
  exact ModuleCat.isZero_of_subsingleton _

/-- In an even degree `≤ 2n` the model module is `ℤ`. -/
theorem cpnModel_iso_int {n k : ℕ} (h : Even k ∧ k ≤ 2 * n) :
    Nonempty (cpnModel n k ≅ ModuleCat.of ℤ ℤ) := by
  refine ⟨?_⟩
  rw [cpnModel, if_pos h]
  exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

/-- Away from the top degree of `ℂP^{m+1}` the model of `ℂP^m` and that of `ℂP^{m+1}` agree. -/
theorem cpnModel_succ (m k : ℕ) (h : k ≠ 2 * (m + 1)) :
    cpnModel (m + 1) k = cpnModel m k := by
  have hiff : (Even k ∧ k ≤ 2 * (m + 1)) ↔ (Even k ∧ k ≤ 2 * m) := by
    constructor
    · rintro ⟨hk, hle⟩
      obtain ⟨j, hj⟩ := hk
      refine ⟨⟨j, hj⟩, ?_⟩
      by_contra hlt
      push Not at hlt
      omega
    · rintro ⟨hk, hle⟩
      exact ⟨hk, by omega⟩
  have hif : (if Even k ∧ k ≤ 2 * (m + 1) then 1 else 0)
      = (if Even k ∧ k ≤ 2 * m then 1 else 0) := by
    by_cases hc : Even k ∧ k ≤ 2 * (m + 1)
    · rw [if_pos hc, if_pos (hiff.mp hc)]
    · rw [if_neg hc, if_neg (fun hh => hc (hiff.mpr hh))]
  rw [cpnModel, cpnModel, hif]

/-- An odd number is not even. -/
theorem not_even_two_mul_add_one (m : ℕ) : ¬ Even (2 * m + 1) := by
  rintro ⟨j, hj⟩
  omega

/-! ## `ℂP⁰` is a point -/

/-- `ℂP⁰` is contractible (its single chart is everything). -/
theorem contractibleSpace_CP_zero : ContractibleSpace (CP 0) := by
  have huniv : chartSet (0 : Fin 1) = (Set.univ : Set (CP 0)) := by
    refine Set.eq_univ_of_forall fun p => ?_
    obtain ⟨i, hi⟩ := exists_mem_chartSet p
    have : i = 0 := Fin.eq_zero i
    rwa [this] at hi
  haveI : ContractibleSpace ↥(chartSet (0 : Fin 1)) := inferInstance
  exact ((Homeomorph.setCongr huniv).trans (Homeomorph.Set.univ (CP 0))).symm.contractibleSpace

/-- The cohomology of `ℂP⁰` (a point): `ℤ` in degree `0` and `0` above. -/
theorem cpnCohomologyZero (k : ℕ) :
    Nonempty (singularCohomology ℤ k (CPSpace 0) ≅ cpnModel 0 k) := by
  rcases k with _ | k
  · haveI : PathConnectedSpace (CP 0) := pathConnectedSpace_CP 0
    obtain ⟨e0⟩ := singularCohomology_zero ℤ (CPSpace 0)
    refine ⟨e0 ≪≫ ?_⟩
    show ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ (Fin (if Even 0 ∧ 0 ≤ 2 * 0 then 1 else 0) → ℤ)
    have hc : (if Even 0 ∧ 0 ≤ 2 * 0 then 1 else 0) = 1 := by
      rw [if_pos ⟨⟨0, rfl⟩, by omega⟩]
    rw [hc]
    exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm
  · haveI : ContractibleSpace (CP 0) := contractibleSpace_CP_zero
    have h := contractible ℤ (CPSpace 0) k
    exact ⟨IsZero.iso h (isZero_cpnModel fun hh => by omega)⟩

/-! ## The Mayer–Vietoris machinery -/

/-- Exactness of the cohomological Mayer–Vietoris sequence at `H^{n+1}(C^{U,V})`. -/
theorem range_mvCohδ_eq_ker_mvCochainF {X : TopCat} (U V : Set X) (n : ℕ) :
    LinearMap.range (mvCohδ U V n).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (mvCochainF U V) (n + 1)).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker (mvCoh_H_exact₁ U V n)

/-- Exactness of the cohomological Mayer–Vietoris sequence at `H^{n+1}(U) ⊞ H^{n+1}(V)`. -/
theorem range_mvCochainF_eq_ker_mvCochainG {X : TopCat} (U V : Set X) (n : ℕ) :
    LinearMap.range (HomologicalComplex.homologyMap (mvCochainF U V) (n + 1)).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (mvCochainG U V) (n + 1)).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker ((mvCochainSES U V).homology_exact₂ (n + 1))

/-- The first map of the cohomological Mayer–Vietoris sequence is an isomorphism in degree `n + 1`
when `H^n(U ∩ V) = 0` and the second map vanishes in degree `n + 1`. -/
theorem isIso_homologyMap_mvCochainF {X : TopCat} (U V : Set X) (n : ℕ)
    (hδ : mvCohδ U V n = 0)
    (hG : HomologicalComplex.homologyMap (mvCochainG U V) (n + 1) = 0) :
    IsIso (HomologicalComplex.homologyMap (mvCochainF U V) (n + 1)) := by
  have hker : LinearMap.ker (HomologicalComplex.homologyMap (mvCochainF U V) (n + 1)).hom = ⊥ := by
    rw [← range_mvCohδ_eq_ker_mvCochainF U V n, hδ]
    exact LinearMap.range_zero
  have hrange : LinearMap.range (HomologicalComplex.homologyMap (mvCochainF U V) (n + 1)).hom
      = ⊤ := by
    rw [range_mvCochainF_eq_ker_mvCochainG U V n, hG]
    exact LinearMap.ker_zero
  haveI : Mono (HomologicalComplex.homologyMap (mvCochainF U V) (n + 1)) :=
    (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker_eq_bot.mp hker)
  haveI : Epi (HomologicalComplex.homologyMap (mvCochainF U V) (n + 1)) :=
    (ModuleCat.epi_iff_surjective _).mpr (LinearMap.range_eq_top.mp hrange)
  exact isIso_of_mono_of_epi _

/-- When the `U`-part vanishes and the first Mayer–Vietoris map is an isomorphism in degree
`n + 1`, the degree-`n + 1` cohomology of `X` is that of `V`. -/
theorem iso_of_isIso_mvCochainF {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) (hZ : IsZero ((cochainU U V).homology (n + 1)))
    (hF : IsIso (HomologicalComplex.homologyMap (mvCochainF U V) (n + 1))) :
    Nonempty (singularCohomology ℤ (n + 1) X ≅ (cochainV U V).homology (n + 1)) := by
  obtain ⟨eSmall⟩ := cohSmallIso U V hU hV hcov (n + 1)
  obtain ⟨eBip⟩ := homology_biprod_iso (cochainU U V) (cochainV U V) (n + 1)
  haveI := hF
  exact ⟨eSmall ≪≫ asIso (HomologicalComplex.homologyMap (mvCochainF U V) (n + 1)) ≪≫ eBip ≪≫
    (isoZeroBiprod (X := (cochainU U V).homology (n + 1))
      (Y := (cochainV U V).homology (n + 1)) hZ).symm⟩

/-! ## The cohomology of the cover pieces of `ℂP^{n+1}` -/

/-- `H^{2n+1}(U ∩ V; ℤ) ≅ ℤ` for the pieces of the standard cover of `ℂP^{n+1}`. -/
theorem cpnUV_cohomology_top (n : ℕ) :
    Nonempty ((cochainUV (cpU (n + 1)) (cpV (n + 1))).homology (2 * n + 1) ≅
      ModuleCat.of ℤ ℤ) := by
  obtain ⟨e1⟩ :=
    cohomologyIso_of_homotopyEquiv (cpnUV_homotopyEquiv_sphere (n + 1)).some (2 * n + 1)
  obtain ⟨e2⟩ := sphereCohomologyTop (2 * n + 1) (by omega)
  exact ⟨e1 ≪≫ e2⟩

/-- `H^k(U ∩ V; ℤ) = 0` for `k ≠ 0, 2n+1`. -/
theorem cpnUV_cohomology_zero (n k : ℕ) (hk0 : k ≠ 0) (hktop : k ≠ 2 * n + 1) :
    IsZero ((cochainUV (cpU (n + 1)) (cpV (n + 1))).homology k) := by
  obtain ⟨e1⟩ := cohomologyIso_of_homotopyEquiv (cpnUV_homotopyEquiv_sphere (n + 1)).some k
  have h2 := sphereCohomologyZero (2 * n + 1) k (by omega) hk0 hktop
  exact IsZero.of_iso h2 e1

/-! ## The Mayer–Vietoris step -/

/-- **The Mayer–Vietoris step**: the cohomology of `ℂP^{m+1}` from that of `ℂP^m`. -/
theorem cpnCohomologyStep (m : ℕ)
    (ih : ∀ k, Nonempty (singularCohomology ℤ k (CPSpace m) ≅ cpnModel m k)) (k : ℕ) :
    Nonempty (singularCohomology ℤ k (CPSpace (m + 1)) ≅ cpnModel (m + 1) k) := by
  set U : Set (CPSpace (m + 1)) := cpU (m + 1) with hUdef
  set V : Set (CPSpace (m + 1)) := cpV (m + 1) with hVdef
  have hUopen : IsOpen U := isOpen_cpU (m + 1)
  have hVopen : IsOpen V := isOpen_cpV (m + 1)
  have hcov : U ∪ V = Set.univ := cpU_union_cpV (m + 1)
  haveI hUcontr : ContractibleSpace ↥U := contractibleSpace_chartSet (m + 1) 0
  haveI hUVpc : PathConnectedSpace ↥(U ∩ V) := pathConnectedSpace_cpUV m
  -- the `V`-part: the cohomology of `ℂP^m`
  have hV : ∀ j, Nonempty ((cochainV U V).homology j ≅ cpnModel m j) := by
    intro j
    obtain ⟨e1⟩ := cohomologyIso_of_homotopyEquiv (cpnV_homotopyEquiv m).some j
    obtain ⟨e2⟩ := ih j
    exact ⟨e1 ≪≫ e2⟩
  have hVzero : ∀ j, ¬(Even j ∧ j ≤ 2 * m) → IsZero ((cochainV U V).homology j) := by
    intro j hj
    obtain ⟨e⟩ := hV j
    exact IsZero.of_iso (isZero_cpnModel hj) e
  -- the `U`-part: contractible
  have hUzero : ∀ j, IsZero ((cochainU U V).homology (j + 1)) :=
    fun j => contractible ℤ (TopCat.of ↥U) j
  -- the `U ∩ V`-part: a sphere
  have hUVzero : ∀ j, j ≠ 0 → j ≠ 2 * m + 1 → IsZero ((cochainUV U V).homology j) :=
    fun j hj0 hjt => cpnUV_cohomology_zero m j hj0 hjt
  have hUVtop : Nonempty ((cochainUV U V).homology (2 * m + 1) ≅ ModuleCat.of ℤ ℤ) :=
    cpnUV_cohomology_top m
  have hLtop : IsZero ((cochainU U V ⊞ cochainV U V).homology (2 * m + 1)) :=
    isZero_coh_homology_biprod _ _ (2 * m + 1) (hUzero (2 * m))
      (hVzero (2 * m + 1) fun hh => not_even_two_mul_add_one m hh.1)
  rcases k with _ | _ | k
  · -- degree `0`
    haveI : PathConnectedSpace ↥(CPSpace (m + 1)) := pathConnectedSpace_CP (m + 1)
    obtain ⟨e0⟩ := singularCohomology_zero ℤ (CPSpace (m + 1))
    refine ⟨e0 ≪≫ ?_⟩
    show ModuleCat.of ℤ ℤ ≅
      ModuleCat.of ℤ (Fin (if Even 0 ∧ 0 ≤ 2 * (m + 1) then 1 else 0) → ℤ)
    have hc : (if Even 0 ∧ 0 ≤ 2 * (m + 1) then 1 else 0) = 1 := by
      rw [if_pos ⟨⟨0, rfl⟩, by omega⟩]
    rw [hc]
    exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm
  · -- degree `1`
    haveI hG0 : Epi (HomologicalComplex.homologyMap (mvCochainG U V) 0) :=
      epi_homologyMap_mvCochainG_zero U V
    have hcomp : HomologicalComplex.homologyMap (mvCochainG U V) 0 ≫ mvCohδ U V 0 = 0 :=
      (mvCochainSES U V).comp_δ 0 1 (by simp [ComplexShape.up])
    have hδ0 : mvCohδ U V 0 = 0 := (cancel_epi _).mp (hcomp.trans (comp_zero).symm)
    have hker : LinearMap.ker (HomologicalComplex.homologyMap (mvCochainF U V) 1).hom = ⊥ := by
      rw [← range_mvCohδ_eq_ker_mvCochainF U V 0, hδ0]
      exact LinearMap.range_zero
    haveI : Mono (HomologicalComplex.homologyMap (mvCochainF U V) 1) :=
      (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker_eq_bot.mp hker)
    have hL : IsZero ((cochainU U V ⊞ cochainV U V).homology 1) :=
      isZero_coh_homology_biprod _ _ 1 (hUzero 0)
        (hVzero 1 fun hh => absurd hh.1 (by rintro ⟨j, hj⟩; omega))
    haveI hsrc : IsZero ((dualComplex ℤ (smallChains U V)).homology 1) :=
      IsZero.of_mono (HomologicalComplex.homologyMap (mvCochainF U V) 1) hL
    obtain ⟨eSmall⟩ := cohSmallIso U V hUopen hVopen hcov 1
    haveI hX1 : IsZero (singularCohomology ℤ 1 (CPSpace (m + 1))) := IsZero.of_iso hsrc eSmall
    refine ⟨IsZero.iso hX1 ?_⟩
    exact isZero_cpnModel fun hh => absurd hh.1 (by rintro ⟨j, hj⟩; omega)
  · -- degree `k + 2`
    change Nonempty (singularCohomology ℤ (k + 2) (CPSpace (m + 1)) ≅ cpnModel (m + 1) (k + 2))
    by_cases htop : k + 2 = 2 * (m + 1)
    · -- the top degree `2(m+1) = 2m + 2`
      rw [htop]
      have hL2 : IsZero ((cochainU U V ⊞ cochainV U V).homology (2 * m + 2)) :=
        isZero_coh_homology_biprod _ _ (2 * m + 2) (hUzero (2 * m + 1))
          (hVzero (2 * m + 2) fun hh => by omega)
      haveI : IsIso (mvCohδ U V (2 * m + 1)) := mvCohδ_isIso U V (2 * m + 1) hLtop hL2
      obtain ⟨eSmall⟩ := cohSmallIso U V hUopen hVopen hcov (2 * (m + 1))
      refine ⟨eSmall ≪≫ (asIso (mvCohδ U V (2 * m + 1))).symm ≪≫ hUVtop.some ≪≫ ?_⟩
      show ModuleCat.of ℤ ℤ ≅
        ModuleCat.of ℤ (Fin (if Even (2 * (m + 1)) ∧ 2 * (m + 1) ≤ 2 * (m + 1) then 1 else 0) → ℤ)
      have hc : (if Even (2 * (m + 1)) ∧ 2 * (m + 1) ≤ 2 * (m + 1) then 1 else 0) = 1 := by
        rw [if_pos ⟨⟨m + 1, by ring⟩, le_rfl⟩]
      rw [hc]
      exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm
    · -- all other degrees `≥ 2`: the first Mayer–Vietoris map is an isomorphism
      have hk1 : k + 1 ≠ 2 * m + 1 := by omega
      have hδ : mvCohδ U V (k + 1) = 0 :=
        IsZero.eq_zero_of_src (hUVzero (k + 1) (by omega) hk1) _
      have hG : HomologicalComplex.homologyMap (mvCochainG U V) (k + 2) = 0 := by
        by_cases hk : k + 2 = 2 * m + 1
        · rw [hk]
          exact IsZero.eq_zero_of_src hLtop _
        · exact IsZero.eq_zero_of_tgt (hUVzero (k + 2) (by omega) hk) _
      haveI hF : IsIso (HomologicalComplex.homologyMap (mvCochainF U V) (k + 2)) :=
        isIso_homologyMap_mvCochainF U V (k + 1) hδ hG
      have hk2 : k + 2 ≠ 2 * (m + 1) := htop
      have hUz : IsZero ((cochainU U V).homology (k + 2)) := hUzero (k + 1)
      obtain ⟨e⟩ := iso_of_isIso_mvCochainF U V hUopen hVopen hcov (k + 1) hUz hF
      obtain ⟨eV⟩ := hV (k + 2)
      exact ⟨e ≪≫ eV ≪≫ eqToIso (cpnModel_succ m (k + 2) hk2).symm⟩

/-! ## The main theorem -/

/-- The cohomology of `ℂPⁿ` with `ℤ` coefficients is `ℤ` in even degrees `k ≤ 2n` and `0`
otherwise. -/
theorem cpn_cohomology_aux (n k : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ k (Work.Projective.CPSpace n) ≅
      cpnModel n k) := by
  revert k
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    rcases n with _ | m
    · exact cpnCohomologyZero k
    · exact cpnCohomologyStep m (ih m (by omega)) k

/-- The cohomology of `ℂPⁿ` with `ℤ` coefficients is `ℤ` in even degrees `k ≤ 2n` and `0`
otherwise.  Suggested proof: strong induction on `n`, with the Mayer–Vietoris sequence of the
cover `cpU n ∪ cpV n = ⊤` (`cpU_union_cpV`), whose pieces have the cohomology of `ℂP^{n-1}`
(`cpnV_homotopyEquiv`, the induction hypothesis), of `ℂⁿ` (contractible, hence vanishing in
positive degrees) and of `S^{2n-1}` (`cpnUV_homotopyEquiv_sphere`, `sphereCohomologyTop`,
`sphereCohomologyZero`); the `n = 2` case is carried out in `CP2Cohomology.lean`. -/
theorem cpn_cohomology (n k : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ k (Work.Projective.CPSpace n) ≅
      ModuleCat.of ℤ (Fin (if Even k ∧ k ≤ 2 * n then 1 else 0) → ℤ)) :=
  cpn_cohomology_aux n k

end

end Work.Projective

