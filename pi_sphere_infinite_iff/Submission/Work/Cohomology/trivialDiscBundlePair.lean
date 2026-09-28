import Mathlib
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.diskPairCohomologyTop
import Submission.Work.Cohomology.isZeroRelCohomologyZero
import Submission.Work.Cohomology.epi_singularCohomologyMap_zero
import Submission.Work.Cohomology.cohomology_prod_contractible
import Submission.Work.Cohomology.diskPairHomologyZero

set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cohomology of the trivial disc bundle pair `(D⁴ × D⁴, D⁴ × S³)`

The pair `(D⁴ × D⁴, D⁴ × S³)` is the trivial rank-`4` disc bundle over `D⁴` together with its unit
sphere bundle.  Since the total space `D⁴ × D⁴` is contractible and the sphere bundle
`D⁴ × S³` is homotopy equivalent to `S³`, the long exact sequence of the pair gives

  `Hⁿ(D⁴ × D⁴, D⁴ × S³; ℤ) ≅ ℤ`  for `n = 4`, and `0` otherwise,

which is `trivialDiscBundlePair` below.

The argument copies `Work.Cohomology.cohomologyPairVk`:
* `H⁰(X,A) = 0` because `X` is path connected and `A ≠ ∅` (`isZeroRelCohomologyZero`);
* `H¹(X,A) = 0` because `H⁰(X) ⟶ H⁰(A)` is onto (`A` is path connected,
  `epi_singularCohomologyMap_zero`) and `H¹(X) = 0`;
* for `n ≥ 2` the connecting map `pairδ : Hⁿ⁻¹(A) ⟶ Hⁿ(X,A)` is an isomorphism
  (`pairδ_isIso`, since `Hⁿ⁻¹(X) = Hⁿ(X) = 0`), and `Hⁿ⁻¹(A) ≅ Hⁿ⁻¹(S³)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Limits

noncomputable section

/-- The total space `D⁴ × D⁴` of the trivial rank-`4` disc bundle over `D⁴`. -/
private abbrev tdX : TopCat := TopCat.of (↥(diskUnit 4) × ↥(diskUnit 4))

/-- The unit sphere bundle `D⁴ × S³` inside `D⁴ × D⁴`. -/
private abbrev tdA : Set (↥(diskUnit 4) × ↥(diskUnit 4)) :=
  {p | p.2 ∈ sphereInUnit 4}

/-- The module `Fin 0 → ℤ` is a zero object. -/
private theorem isZero_fin_zero : IsZero (ModuleCat.of ℤ (Fin 0 → ℤ)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  infer_instance

/-- `ℤ` is the free module on one generator, `Fin 1 → ℤ`. -/
private theorem int_fin_one_iso : Nonempty (ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ (Fin 1 → ℤ)) :=
  ⟨LinearEquiv.toModuleIso (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm⟩

/-- A homeomorphism transports path connectedness. -/
private lemma pathConnectedSpace_of_homeomorph {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) [PathConnectedSpace β] : PathConnectedSpace α := by
  rw [pathConnectedSpace_iff_univ]
  have h : IsPathConnected (Set.univ : Set β) := pathConnectedSpace_iff_univ.mp inferInstance
  have h2 := (e.symm.isPathConnected_image (s := Set.univ)).mpr h
  rwa [Set.image_univ_of_surjective e.symm.surjective] at h2

/-- The middle term of a short exact sequence with vanishing outer terms vanishes. -/
private lemma isZero_of_exact_of_isZero_of_isZero {S : ShortComplex (ModuleCat ℤ)} (h : S.Exact)
    (h1 : IsZero S.X₁) (h3 : IsZero S.X₃) : IsZero S.X₂ := by
  have hf0 : ModuleCat.Hom.hom S.f = 0 := by rw [h1.eq_of_src S.f 0, ModuleCat.hom_zero]
  have hg0 : ModuleCat.Hom.hom S.g = 0 := by rw [h3.eq_of_tgt S.g 0, ModuleCat.hom_zero]
  have hrk := ShortComplex.Exact.moduleCat_range_eq_ker h
  rw [hf0, hg0, LinearMap.range_zero, LinearMap.ker_zero] at hrk
  haveI : Subsingleton ↥S.X₂ := ⟨fun a b => by
    have ha : a = 0 := (Submodule.mem_bot ℤ).mp (by rw [hrk]; exact Submodule.mem_top)
    have hb : b = 0 := (Submodule.mem_bot ℤ).mp (by rw [hrk]; exact Submodule.mem_top)
    rw [ha, hb]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The first arrow of a short exact sequence with vanishing target is an epimorphism. -/
private lemma epi_of_exact_of_isZero_tgt {S : ShortComplex (ModuleCat ℤ)} (h : S.Exact)
    (h3 : IsZero S.X₃) : Epi S.f :=
  (ShortComplex.exact_iff_epi S (h3.eq_of_tgt S.g 0)).mp h

/-- Exactness of a short complex of `ℤ`-modules, read on the underlying linear maps. -/
private lemma exact_range_eq_ker {S : ShortComplex (ModuleCat ℤ)} (h : S.Exact) :
    (ModuleCat.Hom.hom S.f).range = (ModuleCat.Hom.hom S.g).ker :=
  ShortComplex.Exact.moduleCat_range_eq_ker h

/-! ## Elementary facts about the pair -/

/-- `D⁴ × D⁴` is contractible. -/
private theorem tdX_contractible : ContractibleSpace ↥tdX := by
  haveI := diskUnit_isContractible 4
  infer_instance

/-- `D⁴ × D⁴` is path connected. -/
private theorem tdX_pathConnected : PathConnectedSpace ↥tdX := by
  haveI := tdX_contractible
  infer_instance

/-- The positive-degree cohomology of `D⁴ × D⁴` vanishes. -/
private theorem tdX_isZero (m : ℕ) (hm : 1 ≤ m) : IsZero (singularCohomology ℤ m tdX) := by
  haveI := tdX_contractible
  have h := contractible ℤ tdX (m - 1)
  rwa [Nat.sub_add_cancel hm] at h

/-- The homeomorphism `D⁴ × S³ ≅ D⁴ × S³` identifying the sphere bundle `tdA` of the pair
`(D⁴ × D⁴, tdA)` with the honest product of `D⁴` and `S³`. -/
private def tdAHomeo : ↥tdA ≃ₜ (↥(diskUnit 4) × ↥(sphereInUnit 4)) :=
  (Homeomorph.setCongr (show tdA =
      (Set.univ : Set ↥(diskUnit 4)) ×ˢ sphereInUnit 4 from by
        ext p; simp [Set.mem_prod])).trans
    ((Homeomorph.Set.prod (Set.univ : Set ↥(diskUnit 4)) (sphereInUnit 4)).trans
      ((Homeomorph.Set.univ ↥(diskUnit 4)).prodCongr (Homeomorph.refl _)))

/-- The sphere bundle `tdA = D⁴ × S³` is path connected (it is homeomorphic to
`D⁴ × S³ ≃ S³`). -/
private theorem tdA_pathConnected : PathConnectedSpace (TopCat.of ↥tdA) := by
  haveI : PathConnectedSpace ↥(diskUnit 4) := by
    haveI := diskUnit_isContractible 4
    infer_instance
  haveI : PathConnectedSpace ↥(sphereInUnit 4) := sphereInUnit_pathConnected 4 (by norm_num)
  exact pathConnectedSpace_of_homeomorph tdAHomeo

/-- `tdA = D⁴ × S³` is nonempty. -/
private theorem tdA_nonempty : tdA.Nonempty := by
  obtain ⟨y, hy⟩ := sphereInUnit_nonempty 4 (by norm_num)
  exact ⟨(⟨0, by simp [Metric.mem_closedBall]⟩, y), hy⟩

/-! ## The cohomology of the sphere bundle -/

/-- `Hᵏ(tdA) ≅ Hᵏ(S³)`: the sphere bundle is homeomorphic to `D⁴ × S³`, which is homotopy
equivalent to `S³ = sphereInUnit 4`. -/
private theorem tdA_cohomologyIso (k : ℕ) :
    Nonempty (singularCohomology ℤ k (TopCat.of ↥tdA) ≅
      singularCohomology ℤ k (TopCat.of (sphereInUnit 4))) := by
  haveI : ContractibleSpace ↥(diskUnit 4) := diskUnit_isContractible 4
  obtain ⟨e1⟩ := cohomologyIso_of_homotopyEquiv tdAHomeo.toHomotopyEquiv k
  obtain ⟨e2⟩ := cohomology_prod_contractible ℤ (diskUnit 4) (TopCat.of (sphereInUnit 4)) k
  exact ⟨e1 ≪≫ e2⟩

/-- The cohomology of the sphere bundle off degrees `0` and `3` vanishes. -/
private theorem tdA_isZero (k : ℕ) (hk0 : k ≠ 0) (hk3 : k ≠ 3) :
    IsZero (singularCohomology ℤ k (TopCat.of ↥tdA)) := by
  obtain ⟨e⟩ := tdA_cohomologyIso k
  obtain ⟨e'⟩ := sphereInUnitCohomologyIso 4 k
  have hsphere : IsZero (singularCohomology ℤ k
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))) :=
    sphereCohomologyZero 3 k (by norm_num) hk0 hk3
  have hz : IsZero (singularCohomology ℤ k (sphTop 4)) := by
    obtain ⟨e''⟩ := cohomologyIso_of_homotopyEquiv
      (Homeomorph.setCongr (sphereSet_eq 4)).toHomotopyEquiv k
    exact IsZero.of_iso hsphere e''.symm
  exact IsZero.of_iso (IsZero.of_iso hz e') e

/-- `H³(tdA) ≅ ℤ ≅ Fin 1 → ℤ`. -/
private theorem tdA_iso3 :
    Nonempty (singularCohomology ℤ 3 (TopCat.of ↥tdA) ≅ ModuleCat.of ℤ (Fin 1 → ℤ)) := by
  obtain ⟨e1⟩ := tdA_cohomologyIso 3
  obtain ⟨e2⟩ := sphereInUnitCohomologyIso 4 3
  obtain ⟨e3⟩ := sphereCohomology_aux 3 (by norm_num)
  obtain ⟨e4⟩ := int_fin_one_iso
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ e4⟩

/-! ## The main computation -/

theorem trivialDiscBundlePair (n : ℕ) :
    Nonempty (Work.Cohomology.relCohomology ℤ
        (TopCat.of (↥(Work.Cohomology.diskUnit 4) × ↥(Work.Cohomology.diskUnit 4)))
        {p : ↥(Work.Cohomology.diskUnit 4) × ↥(Work.Cohomology.diskUnit 4) |
          p.2 ∈ Work.Cohomology.sphereInUnit 4} n ≅
      ModuleCat.of ℤ (Fin (if n = 4 then 1 else 0) → ℤ)) := by
  change Nonempty (relCohomology ℤ tdX tdA n ≅
    ModuleCat.of ℤ (Fin (if n = 4 then 1 else 0) → ℤ))
  rcases eq_or_ne n 0 with rfl | hn0
  · -- degree `0`
    have hidx : (if (0 : ℕ) = 4 then 1 else 0) = 0 := by norm_num
    rw [hidx]
    haveI : PathConnectedSpace ↥tdX := tdX_pathConnected
    exact ⟨IsZero.iso (isZeroRelCohomologyZero tdX tdA tdA_nonempty) isZero_fin_zero⟩
  rcases eq_or_ne n 1 with rfl | hn1
  · -- degree `1`
    have hidx : (if (1 : ℕ) = 4 then 1 else 0) = 0 := by norm_num
    rw [hidx]
    haveI : PathConnectedSpace ↥tdX := tdX_pathConnected
    haveI : PathConnectedSpace ↥(TopCat.of ↥tdA) := tdA_pathConnected
    haveI hEpi : Epi (HomologicalComplex.homologyMap (restr ℤ tdX tdA) 0) :=
      epi_singularCohomologyMap_zero (subtypeIncl tdX tdA)
    have hδepi : Epi (pairδ ℤ tdX tdA 0) :=
      epi_of_exact_of_isZero_tgt (pair_exact₁ ℤ tdX tdA 0) (tdX_isZero 1 (by norm_num))
    have hkerδ : (ModuleCat.Hom.hom (pairδ ℤ tdX tdA 0)).ker = ⊤ := by
      rw [← exact_range_eq_ker (pair_exact₃ ℤ tdX tdA 0)]
      exact LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp hEpi)
    have hδ0 : (ModuleCat.Hom.hom (pairδ ℤ tdX tdA 0)) = 0 := LinearMap.ker_eq_top.mp hkerδ
    have hsurjδ : Function.Surjective (ModuleCat.Hom.hom (pairδ ℤ tdX tdA 0)) :=
      (ModuleCat.epi_iff_surjective _).mp hδepi
    have hz1 : IsZero (relCohomology ℤ tdX tdA 1) := by
      rw [ModuleCat.isZero_iff_subsingleton]
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, hx⟩ := hsurjδ a
      obtain ⟨y, hy⟩ := hsurjδ b
      rw [← hx, ← hy, hδ0]
      simp
    exact ⟨IsZero.iso hz1 isZero_fin_zero⟩
  · -- degrees `n ≥ 2`
    have hn2 : 2 ≤ n := by omega
    rcases eq_or_ne n 4 with rfl | hn4
    · -- degree `4`
      have hidx : (if (4 : ℕ) = 4 then 1 else 0) = 1 := by norm_num
      rw [hidx]
      haveI : IsIso (pairδ ℤ tdX tdA 3) :=
        pairδ_isIso tdX tdA 3 (tdX_isZero 4 (by norm_num)) (tdX_isZero 3 (by norm_num))
      exact ⟨(asIso (pairδ ℤ tdX tdA 3)).symm ≪≫ tdA_iso3.some⟩
    · -- degrees `n ≥ 2`, `n ≠ 4`
      have hidx : (if n = 4 then 1 else 0) = 0 := by rw [if_neg hn4]
      rw [hidx]
      have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      haveI : IsIso (pairδ ℤ tdX tdA (n - 1)) :=
        pairδ_isIso tdX tdA (n - 1)
          (tdX_isZero (n - 1 + 1) (by omega)) (tdX_isZero (n - 1) (by omega))
      have hzA : IsZero (singularCohomology ℤ (n - 1) (TopCat.of ↥tdA)) :=
        tdA_isZero (n - 1) (by omega) (by omega)
      rw [← hsub]
      exact ⟨(asIso (pairδ ℤ tdX tdA (n - 1))).symm ≪≫ IsZero.iso hzA isZero_fin_zero⟩

end

end Work.Cohomology
