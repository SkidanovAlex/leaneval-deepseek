import Mathlib
import Submission.Work.Cohomology.trivialDiscBundlePair
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.diskPairHomologyTop
import Submission.Work.Cohomology.diskPairHomologyZero
import Submission.Work.Cohomology.homology_prod_contractible

set_option synthInstance.maxHeartbeats 400000

/-!
# The relative homology of the trivial disc bundle pair `(D⁴ × D⁴, D⁴ × S³)`

The homology counterpart of `Work.Cohomology.trivialDiscBundlePair`.  The pair
`(D⁴ × D⁴, D⁴ × S³)` is the trivial rank-`4` disc bundle over `D⁴` together with its unit sphere
bundle.  Since the total space `D⁴ × D⁴` is contractible and the sphere bundle `D⁴ × S³` is
homotopy equivalent to `S³`, the long exact sequence of the pair gives

  `Hₙ(D⁴ × D⁴, D⁴ × S³; ℤ) ≅ ℤ`  for `n = 4`, and `0` otherwise,

which is `trivialDiscBundlePairHomology` below.

The argument is the exact analogue of the cohomological one:
* `H₀(X,A) = 0` because `X` is path connected, `A` is path connected and nonempty, so that the
  augmentation identifies `H₀(A) ⟶ H₀(X)` with an isomorphism (hence an epimorphism);
* `H₁(X,A) = 0` because the connecting map `hPairδ X A 0 : H₁(X,A) ⟶ H₀(A)` is injective
  (`H₁(X) = 0`) and zero (since `H₀(A) ⟶ H₀(X)` is injective), hence `H₁(X,A) = 0`;
* for `n ≥ 2` the connecting map `hPairδ : Hₙ(X,A) ⟶ Hₙ₋₁(A)` is an isomorphism
  (`hPairδ_isIso`, since `Hₙ⁻¹(X) = Hₙ(X) = 0`), and `Hₙ₋₁(A) ≅ Hₙ₋₁(S³)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Limits

noncomputable section

/-- The total space `D⁴ × D⁴` of the trivial rank-`4` disc bundle over `D⁴`. -/
private abbrev thX : TopCat := TopCat.of (↥(diskUnit 4) × ↥(diskUnit 4))

/-- The unit sphere bundle `D⁴ × S³` inside `D⁴ × D⁴`. -/
private abbrev thA : Set (↥(diskUnit 4) × ↥(diskUnit 4)) :=
  {p | p.2 ∈ sphereInUnit 4}

/-- The module `Fin 0 → ℤ` is a zero object. -/
private theorem isZero_fin_zero : IsZero (ModuleCat.of ℤ (Fin 0 → ℤ)) :=
  ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- `ℤ` is the free module on one generator, `Fin 1 → ℤ`. -/
private theorem int_fin_one_iso :
    Nonempty (ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ (Fin 1 → ℤ)) :=
  ⟨LinearEquiv.toModuleIso (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm⟩

/-- A homeomorphism transports path connectedness. -/
private lemma pathConnectedSpace_of_homeomorph {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) [PathConnectedSpace β] : PathConnectedSpace α := by
  rw [pathConnectedSpace_iff_univ]
  have h : IsPathConnected (Set.univ : Set β) := pathConnectedSpace_iff_univ.mp inferInstance
  have h2 := (e.symm.isPathConnected_image (s := Set.univ)).mpr h
  rwa [Set.image_univ_of_surjective e.symm.surjective] at h2

/-- The homeomorphism `D⁴ × S³ ≅ D⁴ × S³` identifying the sphere bundle `thA` of the pair
`(D⁴ × D⁴, thA)` with the honest product of `D⁴` and `S³`. -/
private def thAHomeo : ↥thA ≃ₜ (↥(diskUnit 4) × ↥(sphereInUnit 4)) :=
  (Homeomorph.setCongr (show thA =
      (Set.univ : Set ↥(diskUnit 4)) ×ˢ sphereInUnit 4 from by
        ext p; simp [Set.mem_prod])).trans
    ((Homeomorph.Set.prod (Set.univ : Set ↥(diskUnit 4)) (sphereInUnit 4)).trans
      ((Homeomorph.Set.univ ↥(diskUnit 4)).prodCongr (Homeomorph.refl _)))

/-! ## Elementary facts about the pair -/

/-- `D⁴ × D⁴` is contractible. -/
private theorem thX_contractible : ContractibleSpace ↥thX := by
  haveI : ContractibleSpace ↥(diskUnit 4) := diskUnit_contractible 4
  infer_instance

/-- The positive-degree homology of `D⁴ × D⁴` vanishes. -/
private theorem thX_isZero (m : ℕ) (hm : 1 ≤ m) :
    IsZero ((singularChains ℤ thX).homology m) := by
  haveI : ContractibleSpace ↥thX := thX_contractible
  exact homologyContractible m (by omega)

/-- The sphere bundle `thA = D⁴ × S³` is path connected. -/
private theorem thA_pathConnected : PathConnectedSpace (TopCat.of ↥thA) := by
  haveI : PathConnectedSpace ↥(diskUnit 4) := by
    haveI : ContractibleSpace ↥(diskUnit 4) := diskUnit_contractible 4
    infer_instance
  haveI : PathConnectedSpace ↥(sphereInUnit 4) := sphereInUnit_pathConnected 4 (by norm_num)
  exact pathConnectedSpace_of_homeomorph thAHomeo

/-- The map `H₀(A) ⟶ H₀(X)` is an isomorphism: both spaces are path connected, so the natural
augmentation is an isomorphism on each and the map agrees with the identity of `ℤ` through it. -/
private theorem h0_incl_isIso :
    IsIso (HomologicalComplex.homologyMap (inclChains thX thA) 0) := by
  haveI : ContractibleSpace ↥thX := thX_contractible
  haveI : PathConnectedSpace (TopCat.of ↥thA) := thA_pathConnected
  haveI hεX : IsIso (TopCat.singularHomology₀ε thX (ModuleCat.of ℤ ℤ)) := inferInstance
  haveI hεA : IsIso (TopCat.singularHomology₀ε (TopCat.of ↥thA) (ModuleCat.of ℤ ℤ)) :=
    inferInstance
  have hnat := epsilonNaturality (TopCat.of ↥thA) thX (subtypeIncl thX thA)
  have hα : HomologicalComplex.homologyMap (inclChains thX thA) 0
      = TopCat.singularHomology₀ε (TopCat.of ↥thA) (ModuleCat.of ℤ ℤ)
        ≫ inv (TopCat.singularHomology₀ε thX (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hα]
  infer_instance

/-- The map `H₀(A) ⟶ H₀(X)` is surjective, hence `H₀(X,A) = 0`. -/
private theorem h0_incl_epi :
    Epi (HomologicalComplex.homologyMap (inclChains thX thA) 0) := by
  haveI := h0_incl_isIso
  infer_instance

/-! ## The homology of the sphere bundle -/

/-- `Hₖ(thA) ≅ Hₖ(S³)`: the sphere bundle is homeomorphic to `D⁴ × S³`, which is homotopy
equivalent to `S³ = sphereInUnit 4`. -/
private theorem thA_homologyIso (k : ℕ) :
    Nonempty ((singularChains ℤ (TopCat.of ↥thA)).homology k ≅
      (singularChains ℤ (TopCat.of (sphereInUnit 4))).homology k) := by
  haveI : ContractibleSpace ↥(diskUnit 4) := diskUnit_contractible 4
  obtain ⟨e1⟩ := homologyIso_of_homotopyEquiv thAHomeo.toHomotopyEquiv k
  obtain ⟨e2⟩ := homology_prod_contractible (diskUnit 4) (TopCat.of (sphereInUnit 4)) k
  exact ⟨e1 ≪≫ e2⟩

/-- The homology of the sphere bundle off degrees `0` and `3` vanishes. -/
private theorem thA_isZero (k : ℕ) (hk0 : k ≠ 0) (hk3 : k ≠ 3) :
    IsZero ((singularChains ℤ (TopCat.of ↥thA)).homology k) := by
  obtain ⟨e⟩ := thA_homologyIso k
  obtain ⟨e'⟩ := sphereInUnitHomologyIso 4 k
  have hsphere : IsZero ((singularChains ℤ
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))).homology k) :=
    sphereVanishing 3 k (by norm_num) hk0 hk3
  exact IsZero.of_iso (IsZero.of_iso hsphere e') e

/-- `H₃(thA) ≅ ℤ ≅ Fin 1 → ℤ`. -/
private theorem thA_iso3 :
    Nonempty ((singularChains ℤ (TopCat.of ↥thA)).homology 3 ≅
      ModuleCat.of ℤ (Fin 1 → ℤ)) := by
  obtain ⟨e1⟩ := thA_homologyIso 3
  obtain ⟨e2⟩ := sphereInUnitHomologyIso 4 3
  obtain ⟨e3⟩ := sphereHomologyTop 3 (by norm_num)
  obtain ⟨e4⟩ := int_fin_one_iso
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ e4⟩

/-! ## The main computation -/

theorem trivialDiscBundlePairHomology (n : ℕ) :
    Nonempty (((Work.Cohomology.relChains
        (TopCat.of (↥(Work.Cohomology.diskUnit 4) × ↥(Work.Cohomology.diskUnit 4)))
        {p : ↥(Work.Cohomology.diskUnit 4) × ↥(Work.Cohomology.diskUnit 4) |
          p.2 ∈ Work.Cohomology.sphereInUnit 4}).homology n) ≅
      ModuleCat.of ℤ (Fin (if n = 4 then 1 else 0) → ℤ)) := by
  change Nonempty ((relChains thX thA).homology n ≅
    ModuleCat.of ℤ (Fin (if n = 4 then 1 else 0) → ℤ))
  rcases eq_or_ne n 0 with rfl | hn0
  · -- degree `0`
    have hidx : (if (0 : ℕ) = 4 then 1 else 0) = 0 := by norm_num
    rw [hidx]
    have hz : IsZero ((relChains thX thA).homology 0) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      refine (hPairShort_shortExact thX thA).exactAt_X₃ 0 h0_incl_epi ?_
      intro j hj
      simp [ComplexShape.down] at hj
    exact ⟨IsZero.iso hz isZero_fin_zero⟩
  rcases eq_or_ne n 1 with rfl | hn1
  · -- degree `1`
    have hidx : (if (1 : ℕ) = 4 then 1 else 0) = 0 := by norm_num
    rw [hidx]
    haveI hδmono : Mono (hPairδ thX thA 0) := by
      have hX1 : IsZero ((singularChains ℤ thX).homology 1) := thX_isZero 1 (by norm_num)
      have hf : HomologicalComplex.homologyMap (cokernel.π (inclChains thX thA)) 1 = 0 :=
        hX1.eq_of_src _ 0
      exact (ShortComplex.exact_iff_mono _ hf).mp (hPair_exact₃ thX thA 0)
    have hδ0 : hPairδ thX thA 0 = 0 := by
      haveI : IsIso (HomologicalComplex.homologyMap (inclChains thX thA) 0) := h0_incl_isIso
      have hEx := hPair_exact₁ thX thA 0
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
      have hker : (ModuleCat.Hom.hom
          (HomologicalComplex.homologyMap (inclChains thX thA) 0)).ker = ⊥ := by
        rw [LinearMap.ker_eq_bot]
        exact (ModuleCat.mono_iff_injective _).mp inferInstance
      rw [hker] at hEx
      exact ModuleCat.hom_ext (LinearMap.range_eq_bot.mp hEx)
    have hz1 : IsZero ((relChains thX thA).homology 1) := by
      refine IsZero.iff_id_eq_zero _ |>.mpr ?_
      have h : (𝟙 _) ≫ hPairδ thX thA 0 = 0 ≫ hPairδ thX thA 0 := by
        rw [Category.id_comp, hδ0, zero_comp]
      exact (cancel_mono (hPairδ thX thA 0)).mp h
    exact ⟨IsZero.iso hz1 isZero_fin_zero⟩
  · -- degrees `n ≥ 2`
    have hn2 : 2 ≤ n := by omega
    rcases eq_or_ne n 4 with rfl | hn4
    · -- degree `4`
      have hidx : (if (4 : ℕ) = 4 then 1 else 0) = 1 := by norm_num
      rw [hidx]
      haveI : IsIso (hPairδ thX thA 3) :=
        hPairδ_isIso thX thA 3 (thX_isZero 4 (by norm_num)) (thX_isZero 3 (by norm_num))
      exact ⟨asIso (hPairδ thX thA 3) ≪≫ thA_iso3.some⟩
    · -- degrees `n ≥ 2`, `n ≠ 4`
      have hidx : (if n = 4 then 1 else 0) = 0 := by rw [if_neg hn4]
      rw [hidx]
      have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      haveI : IsIso (hPairδ thX thA (n - 1)) :=
        hPairδ_isIso thX thA (n - 1)
          (thX_isZero (n - 1 + 1) (by omega)) (thX_isZero (n - 1) (by omega))
      have hzA : IsZero ((singularChains ℤ (TopCat.of ↥thA)).homology (n - 1)) :=
        thA_isZero (n - 1) (by omega) (by omega)
      rw [← hsub]
      exact ⟨asIso (hPairδ thX thA (n - 1)) ≪≫ IsZero.iso hzA isZero_fin_zero⟩

end

end Work.Cohomology
