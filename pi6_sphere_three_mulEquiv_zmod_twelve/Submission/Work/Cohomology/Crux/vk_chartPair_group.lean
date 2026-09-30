import Mathlib
import Submission.Work.Cohomology.cohomologyPairVk
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.trivialDiscBundlePair
import Submission.Work.Cohomology.trivialDiscBundlePairHomology
import Submission.Work.Cohomology.homology_prod_contractible
import Submission.Work.Cohomology.cohomology_prod_contractible
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.diskPairHomologyTop
import Submission.Work.Cohomology.diskPairCohomologyTop
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.homotopyEquiv_prod_fst
import Submission.Work.Cohomology.RelMVLes
import Submission.Work.Cohomology.MVSequence

set_option synthInstance.maxHeartbeats 400000

/-!
# The relative (co)homology of the pair (first chart, sphere bundle) of `Vk (-2)`

The first chart `U = range (vData (-2)).ιX` of the total space `Vk (-2)` of Milnor's disc bundle
is the total space of the trivial rank-`4` disc bundle over the contractible base chart: the open
embedding `ιX` identifies `U` with `MSpace8 = ℝ⁴ × ℍ`, and the unit sphere bundle over `U` is the
preimage of `ℝ⁴ × S³`.  Hence the pair `(U, U ∩ A)`, where `A` is the unit sphere bundle of
`Vk (-2)`, is homotopy equivalent (as a pair) to `(D⁴, S³)`.

Consequently its relative homology and cohomology are `ℤ` in degree `4` and `0` in every other
degree: this is `vk_chartPair_group` below.

The proof copies `Work.Cohomology.trivialDiscBundlePairHomology` and
`Work.Cohomology.trivialDiscBundlePair`, which do the same computation for the honest trivial disc
bundle pair `(D⁴ × D⁴, D⁴ × S³)`.  Everything reduces to

* `U` is contractible (`Work.Milnor.contractibleSpace_range_ιX`), so `Hᵏ(U) = 0` for `k ≥ 1`;
* the sphere bundle over `U` is `ℝ⁴ × S³`, which is homotopy equivalent to `S³`
  (`Work.Cohomology.homotopyEquiv_prod_fst`, `Work.Cohomology.homology_prod_contractible`);

and then the long exact (co)homology sequence of the pair.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.Cohomology.Crux

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

noncomputable section

/-! ## The pair `(U, U ∩ A)` of the first chart of `Vk (-2)` -/

/-- The first chart `U = range (vData (-2)).ιX` of `Vk (-2)`. -/
private abbrev vkU : Type := ↥(Set.range (Submission.Milnor.vData (-2)).ιX)

/-- `U` as a topological space. -/
private abbrev vkX : TopCat := TopCat.of vkU

/-- The sphere bundle over the chart `U`, as a subset of `U`. -/
private abbrev vkA : Set vkU :=
  {y | (y : Submission.Milnor.Vk (-2)) ∈ Set.range (Work.Milnor.mkToVkFun (-2))}

/-- `Fin 0 → ℤ` is a zero object. -/
private theorem isZero_fin_zero : IsZero (ModuleCat.of ℤ (Fin 0 → ℤ)) :=
  ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- `ℤ` is the free module on one generator, `Fin 1 → ℤ`. -/
private theorem int_fin_one_iso : Nonempty (ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ (Fin 1 → ℤ)) :=
  ⟨LinearEquiv.toModuleIso (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm⟩

/-- A homeomorphism transports path connectedness. -/
private lemma pathConnectedSpace_of_homeomorph' {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) [PathConnectedSpace β] : PathConnectedSpace α := by
  rw [pathConnectedSpace_iff_univ]
  have h : IsPathConnected (Set.univ : Set β) := pathConnectedSpace_iff_univ.mp inferInstance
  have h2 := (e.symm.isPathConnected_image (s := Set.univ)).mpr h
  rwa [Set.image_univ_of_surjective e.symm.surjective] at h2

/-! ## Contractibility and vanishing (co)homology of the total space -/

/-- The chart `U` is contractible: it is homeomorphic to `MSpace8 = ℝ⁴ × ℍ`. -/
private theorem vkX_contractible : ContractibleSpace vkU :=
  Work.Milnor.contractibleSpace_range_ιX (-2)

/-- The chart `U` is path connected. -/
private theorem vkX_pathConnected : PathConnectedSpace vkU := by
  haveI := vkX_contractible
  infer_instance

/-- The positive-degree homology of the contractible chart `U` vanishes. -/
private theorem vkX_homologyIsZero (m : ℕ) (hm : 1 ≤ m) :
    IsZero ((singularChains ℤ vkX).homology m) := by
  haveI : ContractibleSpace vkU := vkX_contractible
  exact homologyContractible m (by omega)

/-- The positive-degree cohomology of the contractible chart `U` vanishes. -/
private theorem vkX_cohomologyIsZero (m : ℕ) (hm : 1 ≤ m) :
    IsZero (singularCohomology ℤ m vkX) := by
  haveI : ContractibleSpace vkU := vkX_contractible
  have h := contractible ℤ vkX (m - 1)
  rwa [Nat.sub_add_cancel hm] at h

/-! ## The chart homeomorphism and the sphere bundle in the chart -/

/-- The chart homeomorphism `MSpace8 = ℝ⁴ × ℍ ≅ U`. -/
private noncomputable def vkChartHomeo : Submission.Milnor.MSpace8 ≃ₜ vkU :=
  ((Submission.Milnor.vData (-2)).isOpenEmbedding_ιX.isEmbedding.toHomeomorph)

/-- The sphere bundle over the chart, transported to `MSpace8`. -/
private def vkA'' : Set Submission.Milnor.MSpace8 := vkChartHomeo ⁻¹' vkA

/-- In the chart, the sphere bundle is exactly the set of points whose fibre coordinate has
norm `1`, i.e. `ℝ⁴ × S³ ⊆ ℝ⁴ × ℍ`. -/
private theorem vkA''_eq : vkA'' = {p : Submission.Milnor.MSpace8 | ‖p.2‖ = 1} := by
  ext p
  rw [vkA'', Set.mem_preimage]
  show ((vkChartHomeo p : vkU) : Submission.Milnor.Vk (-2)) ∈
      Set.range (Work.Milnor.mkToVkFun (-2)) ↔ ‖p.2‖ = 1
  rw [show ((vkChartHomeo p : vkU) : Submission.Milnor.Vk (-2)) =
      (Submission.Milnor.vData (-2)).ιX p from rfl,
    Work.Milnor.mem_range_mkToVkFun_iff, Work.Milnor.fibreNormFun_ιX]

/-- The chart homeomorphism restricts to a homeomorphism of the sphere bundles. -/
private noncomputable def vkA''Homeo : ↥vkA'' ≃ₜ ↥vkA where
  toFun p := ⟨vkChartHomeo p.1, p.2⟩
  invFun y := ⟨vkChartHomeo.symm y.1, by
    show vkChartHomeo (vkChartHomeo.symm y.1) ∈ vkA
    rw [Homeomorph.apply_symm_apply]
    exact y.2⟩
  left_inv p := Subtype.ext (vkChartHomeo.symm_apply_apply p.1)
  right_inv y := Subtype.ext (vkChartHomeo.apply_symm_apply y.1)
  continuous_toFun :=
    Continuous.subtype_mk (vkChartHomeo.continuous.comp continuous_subtype_val) (fun p => p.2)
  continuous_invFun :=
    Continuous.subtype_mk (vkChartHomeo.symm.continuous.comp continuous_subtype_val) (fun y => by
      show vkChartHomeo (vkChartHomeo.symm y.1) ∈ vkA
      rw [Homeomorph.apply_symm_apply]
      exact y.2)

/-! ## `ℝ⁴ × S³` and its homotopy equivalence with `S³` -/

/-- The unit sphere bundle in the chart, `{p : ℝ⁴ × ℍ | ‖p.2‖ = 1}`, is the honest product
`ℝ⁴ × S³`. -/
private noncomputable def vkSphProd :
    ↥{p : Submission.Milnor.MSpace8 | ‖p.2‖ = 1} ≃ₜ
      (EuclideanSpace ℝ (Fin 4) × ↥(Metric.sphere (0 : Quaternion ℝ) 1)) :=
  (Homeomorph.setCongr (by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and, Metric.mem_sphere,
        dist_eq_norm, sub_zero])).trans
    ((Homeomorph.Set.prod (Set.univ : Set (EuclideanSpace ℝ (Fin 4)))
        (Metric.sphere (0 : Quaternion ℝ) 1)).trans
      ((Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 4))).prodCongr (Homeomorph.refl _)))

/-- The trivial product `ℝ⁴ × S³` is homotopy equivalent to `S³`, the base `ℝ⁴` being
contractible. -/
private noncomputable def vkSphProdHomotopy :
    ContinuousMap.HomotopyEquiv
      (EuclideanSpace ℝ (Fin 4) × ↥(Metric.sphere (0 : Quaternion ℝ) 1))
      ↥(Metric.sphere (0 : Quaternion ℝ) 1) :=
  (Homeomorph.prodComm (EuclideanSpace ℝ (Fin 4))
    ↥(Metric.sphere (0 : Quaternion ℝ) 1)).toHomotopyEquiv.trans
    (Work.Cohomology.homotopyEquiv_prod_fst ↥(Metric.sphere (0 : Quaternion ℝ) 1)
      (EuclideanSpace ℝ (Fin 4))).some

/-- Membership in the unit sphere of `ℝ⁴` of the image of a unit quaternion. -/
private theorem quatSphere_mem (y : ↥(Metric.sphere (0 : Quaternion ℝ) 1)) :
    Quaternion.linearIsometryEquivTuple y.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  have h : ‖y.1‖ = 1 := by
    have := Metric.mem_sphere.mp y.2
    rwa [dist_zero_right] at this
  rw [Metric.mem_sphere, dist_zero_right, Quaternion.linearIsometryEquivTuple.norm_map]
  exact h

/-- Membership in the unit sphere of `ℍ` of the image of a unit vector of `ℝ⁴`. -/
private theorem quatSphere_symm_mem (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :
    Quaternion.linearIsometryEquivTuple.symm y.1 ∈ Metric.sphere (0 : Quaternion ℝ) 1 := by
  have h : ‖y.1‖ = 1 := by
    have := Metric.mem_sphere.mp y.2
    rwa [dist_zero_right] at this
  rw [Metric.mem_sphere, dist_zero_right,
    ← Quaternion.linearIsometryEquivTuple.norm_map
      (Quaternion.linearIsometryEquivTuple.symm y.1),
    LinearIsometryEquiv.apply_symm_apply]
  exact h

/-- The isometric identification `ℍ ≅ ℝ⁴` restricts to a homeomorphism of the unit spheres. -/
private noncomputable def quatSphereHomeo :
    ↥(Metric.sphere (0 : Quaternion ℝ) 1) ≃ₜ
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  toFun y := ⟨Quaternion.linearIsometryEquivTuple y.1, quatSphere_mem y⟩
  invFun y := ⟨Quaternion.linearIsometryEquivTuple.symm y.1, quatSphere_symm_mem y⟩
  left_inv y := Subtype.ext (Quaternion.linearIsometryEquivTuple.symm_apply_apply y.1)
  right_inv y := Subtype.ext (Quaternion.linearIsometryEquivTuple.apply_symm_apply y.1)
  continuous_toFun := Continuous.subtype_mk
    (Quaternion.linearIsometryEquivTuple.continuous.comp continuous_subtype_val) quatSphere_mem
  continuous_invFun := Continuous.subtype_mk
    (Quaternion.linearIsometryEquivTuple.symm.continuous.comp continuous_subtype_val)
    quatSphere_symm_mem

/-- **The sphere bundle over the chart `U` is homotopy equivalent to `S³`.** -/
private noncomputable def vkAHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥vkA
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  (vkA''Homeo.symm).toHomotopyEquiv.trans
    ((Homeomorph.setCongr vkA''_eq).toHomotopyEquiv.trans
      (vkSphProd.toHomotopyEquiv.trans
        (vkSphProdHomotopy.trans quatSphereHomeo.toHomotopyEquiv)))

/-- The sphere bundle over the chart is path connected (it is homotopy equivalent to `S³`). -/
private theorem vkA_pathConnected : PathConnectedSpace ↥vkA := by
  haveI : PathConnectedSpace ↥(sphSet 4) := pathConnectedSpace_sphSet 4 (by norm_num)
  haveI hSph : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    pathConnectedSpace_of_homeomorph' (Homeomorph.setCongr (sphereSet_eq 4))
  exact pathConnectedSpace_of_homotopyEquiv vkAHomotopyEquiv hSph

/-- The sphere bundle over the chart is nonempty (take the fibre coordinate `1` over the origin). -/
private theorem vkA_nonempty : vkA.Nonempty := by
  refine ⟨vkChartHomeo (((0 : EuclideanSpace ℝ (Fin 4)), (1 : Quaternion ℝ)) :
    Submission.Milnor.MSpace8), ?_⟩
  show ((vkChartHomeo (((0 : EuclideanSpace ℝ (Fin 4)), (1 : Quaternion ℝ)) :
      Submission.Milnor.MSpace8) : vkU) : Submission.Milnor.Vk (-2)) ∈
    Set.range (Work.Milnor.mkToVkFun (-2))
  rw [show ((vkChartHomeo (((0 : EuclideanSpace ℝ (Fin 4)), (1 : Quaternion ℝ)) :
      Submission.Milnor.MSpace8) : vkU) : Submission.Milnor.Vk (-2)) =
      (Submission.Milnor.vData (-2)).ιX (((0 : EuclideanSpace ℝ (Fin 4)),
        (1 : Quaternion ℝ)) : Submission.Milnor.MSpace8) from rfl,
    Work.Milnor.mem_range_mkToVkFun_iff, Work.Milnor.fibreNormFun_ιX]
  simp

/-! ## The (co)homology of the sphere bundle over the chart -/

/-- `Hₖ(U ∩ A) ≅ Hₖ(S³)`. -/
private theorem vkA_homologyIso (k : ℕ) :
    Nonempty ((singularChains ℤ (TopCat.of ↥vkA)).homology k ≅
      (singularChains ℤ (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))).homology
        k) := by
  obtain ⟨e⟩ := homologyIso_of_homotopyEquiv vkAHomotopyEquiv k
  exact ⟨e⟩

/-- `Hₖ(U ∩ A) = 0` for `k ∉ {0,3}`. -/
private theorem vkA_homologyIsZero (k : ℕ) (hk0 : k ≠ 0) (hk3 : k ≠ 3) :
    IsZero ((singularChains ℤ (TopCat.of ↥vkA)).homology k) := by
  obtain ⟨e⟩ := vkA_homologyIso k
  exact IsZero.of_iso (sphereVanishing 3 k (by norm_num) hk0 hk3) e

/-- `H₃(U ∩ A) ≅ ℤ ≅ Fin 1 → ℤ`. -/
private theorem vkA_iso3 :
    Nonempty ((singularChains ℤ (TopCat.of ↥vkA)).homology 3 ≅
      ModuleCat.of ℤ (Fin 1 → ℤ)) := by
  obtain ⟨e1⟩ := vkA_homologyIso 3
  obtain ⟨e2⟩ := sphereHomologyTop 3 (by norm_num)
  obtain ⟨e3⟩ := int_fin_one_iso
  exact ⟨e1 ≪≫ e2 ≪≫ e3⟩

/-- `Hᵏ(U ∩ A) ≅ Hᵏ(S³)`. -/
private theorem vkA_cohomologyIso (k : ℕ) :
    Nonempty (singularCohomology ℤ k (TopCat.of ↥vkA) ≅
      singularCohomology ℤ k (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))) := by
  obtain ⟨e⟩ := cohomologyIso_of_homotopyEquiv vkAHomotopyEquiv k
  exact ⟨e⟩

/-- `Hᵏ(U ∩ A) = 0` for `k ∉ {0,3}`. -/
private theorem vkA_cohomologyIsZero (k : ℕ) (hk0 : k ≠ 0) (hk3 : k ≠ 3) :
    IsZero (singularCohomology ℤ k (TopCat.of ↥vkA)) := by
  obtain ⟨e⟩ := vkA_cohomologyIso k
  exact IsZero.of_iso (sphereCohomologyZero 3 k (by norm_num) hk0 hk3) e

/-- `H³(U ∩ A) ≅ ℤ ≅ Fin 1 → ℤ`. -/
private theorem vkA_cohomologyIso3 :
    Nonempty (singularCohomology ℤ 3 (TopCat.of ↥vkA) ≅ ModuleCat.of ℤ (Fin 1 → ℤ)) := by
  obtain ⟨e1⟩ := vkA_cohomologyIso 3
  obtain ⟨e2⟩ := sphereCohomologyTop 3 (by norm_num)
  obtain ⟨e3⟩ := int_fin_one_iso
  exact ⟨e1 ≪≫ e2 ≪≫ e3⟩

/-! ## The degree-`0` inclusion `H₀(U ∩ A) ⟶ H₀(U)` -/

/-- The map `H₀(U ∩ A) ⟶ H₀(U)` is an isomorphism: both spaces are path connected, so the natural
augmentation is an isomorphism on each and the map agrees with the identity of `ℤ` through it. -/
private theorem vkA_h0_incl_isIso :
    IsIso (HomologicalComplex.homologyMap (inclChains vkX vkA) 0) := by
  haveI : ContractibleSpace vkU := vkX_contractible
  haveI : PathConnectedSpace (TopCat.of ↥vkA) := vkA_pathConnected
  haveI hεX : IsIso (TopCat.singularHomology₀ε vkX (ModuleCat.of ℤ ℤ)) := inferInstance
  haveI hεA : IsIso (TopCat.singularHomology₀ε (TopCat.of ↥vkA) (ModuleCat.of ℤ ℤ)) :=
    inferInstance
  have hnat := epsilonNaturality (TopCat.of ↥vkA) vkX (subtypeIncl vkX vkA)
  have hα : HomologicalComplex.homologyMap (inclChains vkX vkA) 0
      = TopCat.singularHomology₀ε (TopCat.of ↥vkA) (ModuleCat.of ℤ ℤ)
        ≫ inv (TopCat.singularHomology₀ε vkX (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hα]
  infer_instance

/-- The map `H₀(U ∩ A) ⟶ H₀(U)` is surjective, hence `H₀(U, U ∩ A) = 0`. -/
private theorem vkA_h0_incl_epi :
    Epi (HomologicalComplex.homologyMap (inclChains vkX vkA) 0) := by
  haveI := vkA_h0_incl_isIso
  infer_instance

/-! ## The relative homology -/

private theorem vkRelHomology (n : ℕ) :
    Nonempty ((relChains vkX vkA).homology n ≅
      ModuleCat.of ℤ (Fin (if n = 4 then 1 else 0) → ℤ)) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · -- degree `0`
    have hidx : (if (0 : ℕ) = 4 then 1 else 0) = 0 := by norm_num
    rw [hidx]
    have hz : IsZero ((relChains vkX vkA).homology 0) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      refine (hPairShort_shortExact vkX vkA).exactAt_X₃ 0 vkA_h0_incl_epi ?_
      intro j hj
      simp [ComplexShape.down] at hj
    exact ⟨IsZero.iso hz isZero_fin_zero⟩
  rcases eq_or_ne n 1 with rfl | hn1
  · -- degree `1`
    have hidx : (if (1 : ℕ) = 4 then 1 else 0) = 0 := by norm_num
    rw [hidx]
    haveI hδmono : Mono (hPairδ vkX vkA 0) := by
      have hX1 : IsZero ((singularChains ℤ vkX).homology 1) :=
        vkX_homologyIsZero 1 (by norm_num)
      have hf : HomologicalComplex.homologyMap (cokernel.π (inclChains vkX vkA)) 1 = 0 :=
        hX1.eq_of_src _ 0
      exact (ShortComplex.exact_iff_mono _ hf).mp (hPair_exact₃ vkX vkA 0)
    have hδ0 : hPairδ vkX vkA 0 = 0 := by
      haveI : IsIso (HomologicalComplex.homologyMap (inclChains vkX vkA) 0) :=
        vkA_h0_incl_isIso
      have hEx := hPair_exact₁ vkX vkA 0
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
      have hker : (ModuleCat.Hom.hom
          (HomologicalComplex.homologyMap (inclChains vkX vkA) 0)).ker = ⊥ := by
        rw [LinearMap.ker_eq_bot]
        exact (ModuleCat.mono_iff_injective _).mp inferInstance
      rw [hker] at hEx
      exact ModuleCat.hom_ext (LinearMap.range_eq_bot.mp hEx)
    have hz1 : IsZero ((relChains vkX vkA).homology 1) := by
      refine IsZero.iff_id_eq_zero _ |>.mpr ?_
      have h : (𝟙 _) ≫ hPairδ vkX vkA 0 = 0 ≫ hPairδ vkX vkA 0 := by
        rw [Category.id_comp, hδ0, zero_comp]
      exact (cancel_mono (hPairδ vkX vkA 0)).mp h
    exact ⟨IsZero.iso hz1 isZero_fin_zero⟩
  · -- degrees `n ≥ 2`
    have hn2 : 2 ≤ n := by omega
    rcases eq_or_ne n 4 with rfl | hn4
    · -- degree `4`
      have hidx : (if (4 : ℕ) = 4 then 1 else 0) = 1 := by norm_num
      rw [hidx]
      haveI : IsIso (hPairδ vkX vkA 3) :=
        hPairδ_isIso vkX vkA 3 (vkX_homologyIsZero 4 (by norm_num))
          (vkX_homologyIsZero 3 (by norm_num))
      exact ⟨asIso (hPairδ vkX vkA 3) ≪≫ vkA_iso3.some⟩
    · -- degrees `n ≥ 2`, `n ≠ 4`
      have hidx : (if n = 4 then 1 else 0) = 0 := by rw [if_neg hn4]
      rw [hidx]
      have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      haveI : IsIso (hPairδ vkX vkA (n - 1)) :=
        hPairδ_isIso vkX vkA (n - 1)
          (vkX_homologyIsZero (n - 1 + 1) (by omega))
          (vkX_homologyIsZero (n - 1) (by omega))
      have hzA : IsZero ((singularChains ℤ (TopCat.of ↥vkA)).homology (n - 1)) :=
        vkA_homologyIsZero (n - 1) (by omega) (by omega)
      rw [← hsub]
      exact ⟨asIso (hPairδ vkX vkA (n - 1)) ≪≫ IsZero.iso hzA isZero_fin_zero⟩

/-! ## The relative cohomology -/

private theorem vkRelCohomology (n : ℕ) :
    Nonempty (relCohomology ℤ vkX vkA n ≅
      ModuleCat.of ℤ (Fin (if n = 4 then 1 else 0) → ℤ)) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · -- degree `0`
    have hidx : (if (0 : ℕ) = 4 then 1 else 0) = 0 := by norm_num
    rw [hidx]
    haveI : PathConnectedSpace vkX := vkX_pathConnected
    exact ⟨IsZero.iso (isZeroRelCohomologyZero vkX vkA vkA_nonempty) isZero_fin_zero⟩
  rcases eq_or_ne n 1 with rfl | hn1
  · -- degree `1`
    have hidx : (if (1 : ℕ) = 4 then 1 else 0) = 0 := by norm_num
    rw [hidx]
    haveI : PathConnectedSpace vkX := vkX_pathConnected
    haveI : PathConnectedSpace ↥(TopCat.of ↥vkA) := vkA_pathConnected
    haveI hEpi : Epi (HomologicalComplex.homologyMap (restr ℤ vkX vkA) 0) :=
      epi_singularCohomologyMap_zero (subtypeIncl vkX vkA)
    have hδepi : Epi (pairδ ℤ vkX vkA 0) :=
      epi_of_exact_of_isZero_tgt (pair_exact₁ ℤ vkX vkA 0)
        (vkX_cohomologyIsZero 1 (by norm_num))
    have hkerδ : (ModuleCat.Hom.hom (pairδ ℤ vkX vkA 0)).ker = ⊤ := by
      rw [← exact_range_eq_ker (pair_exact₃ ℤ vkX vkA 0)]
      exact LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp hEpi)
    have hδ0 : (ModuleCat.Hom.hom (pairδ ℤ vkX vkA 0)) = 0 := LinearMap.ker_eq_top.mp hkerδ
    have hsurjδ : Function.Surjective (ModuleCat.Hom.hom (pairδ ℤ vkX vkA 0)) :=
      (ModuleCat.epi_iff_surjective _).mp hδepi
    have hz1 : IsZero (relCohomology ℤ vkX vkA 1) := by
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
      haveI : IsIso (pairδ ℤ vkX vkA 3) :=
        pairδ_isIso vkX vkA 3 (vkX_cohomologyIsZero 4 (by norm_num))
          (vkX_cohomologyIsZero 3 (by norm_num))
      exact ⟨(asIso (pairδ ℤ vkX vkA 3)).symm ≪≫ vkA_cohomologyIso3.some⟩
    · -- degrees `n ≥ 2`, `n ≠ 4`
      have hidx : (if n = 4 then 1 else 0) = 0 := by rw [if_neg hn4]
      rw [hidx]
      have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      haveI : IsIso (pairδ ℤ vkX vkA (n - 1)) :=
        pairδ_isIso vkX vkA (n - 1)
          (vkX_cohomologyIsZero (n - 1 + 1) (by omega))
          (vkX_cohomologyIsZero (n - 1) (by omega))
      have hzA : IsZero (singularCohomology ℤ (n - 1) (TopCat.of ↥vkA)) :=
        vkA_cohomologyIsZero (n - 1) (by omega) (by omega)
      rw [← hsub]
      exact ⟨(asIso (pairδ ℤ vkX vkA (n - 1))).symm ≪≫ IsZero.iso hzA isZero_fin_zero⟩

/-- **The relative (co)homology of the pair (chart, sphere bundle) of `Vk (-2)`.**  For the
first chart `U` of `Vk (-2)` and `A` the unit sphere bundle, the pair `(U, U ∩ A)` is (up to
homotopy of pairs) the trivial rank-4 disc bundle over a contractible base, so its relative
homology and cohomology are `ℤ` in degree `4` and `0` in every other degree. -/
theorem vk_chartPair_group (n : ℕ) :
    (Nonempty ((Work.Cohomology.relChains (TopCat.of ↥(Set.range (Submission.Milnor.vData (-2)).ιX))
        {y : ↥(Set.range (Submission.Milnor.vData (-2)).ιX) | (y : Submission.Milnor.Vk (-2)) ∈
          Set.range (Work.Milnor.mkToVkFun (-2))}).homology n ≅
      ModuleCat.of ℤ (Fin (if n = 4 then 1 else 0) → ℤ))) ∧
    (Nonempty (Work.Cohomology.relCohomology ℤ
        (TopCat.of ↥(Set.range (Submission.Milnor.vData (-2)).ιX))
        {y : ↥(Set.range (Submission.Milnor.vData (-2)).ιX) | (y : Submission.Milnor.Vk (-2)) ∈
          Set.range (Work.Milnor.mkToVkFun (-2))} n ≅
      ModuleCat.of ℤ (Fin (if n = 4 then 1 else 0) → ℤ))) :=
  ⟨vkRelHomology n, vkRelCohomology n⟩

end

end Work.Cohomology.Crux
