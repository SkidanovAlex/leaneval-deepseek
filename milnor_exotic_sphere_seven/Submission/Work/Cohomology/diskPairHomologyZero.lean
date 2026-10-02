import Mathlib
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.sphereInUnitHomologyIso
import Submission.Work.Cohomology.sphereInUnitOneHomologyZero
import Submission.Work.Cohomology.epsilonNaturality

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of the lower relative homology of the disk pair `(Dⁿ, Sⁿ⁻¹)`

We prove that `H_k(Dⁿ, Sⁿ⁻¹; ℤ) = 0` for every `k ≠ n`, the companion of
`Work.Cohomology.diskPairHomologyTop` (`Hₙ(Dⁿ, Sⁿ⁻¹) ≅ ℤ`).  Together they compute the local
homology of an `n`-manifold.

The argument is the long exact sequence of the pair `(Dⁿ, Sⁿ⁻¹)`

`H_k(Dⁿ) ⟶ H_k(Dⁿ, Sⁿ⁻¹) --δ--> H_{k-1}(Sⁿ⁻¹) ⟶ H_{k-1}(Dⁿ)`

together with `H_j(Dⁿ) = 0` for `j ≥ 1` (`Work.Cohomology.homologyContractible`) and the
computation of the homology of the sphere:

* `k ≥ 2`: the connecting map `δ` is an isomorphism onto `H_{k-1}(Sⁿ⁻¹)`
  (`Work.Cohomology.hPairδ_isIso`), which vanishes by `Work.Cohomology.sphereVanishing`
  (`n ≥ 2`) or `Work.Cohomology.sphereInUnitOneHomologyZero` (`n = 1`);
* `k = 1`: `δ = hPairδ (Dⁿ) (Sⁿ⁻¹) 0` is injective (its source `H₁(Dⁿ)` is zero `H₁`) and zero
  because `H₀(Sⁿ⁻¹) → H₀(Dⁿ)` is an isomorphism (`n ≥ 2`, both spaces connected);
* `k = 0`: the exactness `H₀(Dⁿ) ⟶ H₀(Dⁿ, Sⁿ⁻¹) ⟶ 0` exhibits `H₀(Dⁿ, Sⁿ⁻¹)` as a zero object
  because `H₀(Sⁿ⁻¹) → H₀(Dⁿ)` is onto.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Metric

namespace Work.Cohomology

noncomputable section

/-! ## Two elementary facts about the disk pair (local copies, to avoid a heavy import) -/

/-- The closed unit ball `Dⁿ` is contractible (it is a nonempty convex subset of `ℝⁿ`). -/
theorem diskUnit_contractible' (n : ℕ) : ContractibleSpace (diskUnit n) :=
  Convex.contractibleSpace (convex_closedBall 0 1) ⟨0, by simp [Metric.mem_closedBall]⟩

/-- If `H_{m+1}(X) = 0` and `H_m(X) = 0`, then the connecting map
`hPairδ X A m : H_{m+1}(X,A) ⟶ H_m(A)` of the pair `(X,A)` is an isomorphism. -/
theorem hPairδ_isIso' (X : TopCat) (A : Set X) (m : ℕ)
    (h1 : CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ X).homology (m + 1)))
    (h2 : CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ X).homology m)) :
    IsIso (hPairδ X A m) := by
  have hf : (ShortComplex.mk
      (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) (m + 1))
      (hPairδ X A m) (hPair_comp_δ X A m)).f = 0 :=
    h1.eq_of_src _ 0
  have hmono : Mono (hPairδ X A m) :=
    (ShortComplex.exact_iff_mono _ hf).1 (hPair_exact₃ X A m)
  have hg : (ShortComplex.mk (hPairδ X A m)
      (HomologicalComplex.homologyMap (inclChains X A) m)
      (hPairδ_comp X A m)).g = 0 := h2.eq_of_tgt _ 0
  have hepi : Epi (hPairδ X A m) :=
    (ShortComplex.exact_iff_epi _ hg).1 (hPair_exact₁ X A m)
  exact isIso_of_mono_of_epi _

/-! ## Preparatory facts about `sphereInUnit n` -/

/-- `sphereInUnit n` is nonempty for `n ≥ 1` (it contains a unit coordinate vector). -/
theorem sphereInUnit_nonempty (n : ℕ) (hn : 1 ≤ n) : (sphereInUnit n).Nonempty := by
  haveI : NeZero n := ⟨by omega⟩
  let x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (0 : Fin n) 1
  have hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_single]; norm_num
  exact ⟨⟨x, Metric.sphere_subset_closedBall hx⟩, hx⟩

/-- For `n ≥ 2` the sphere `Sⁿ⁻¹ = sphereInUnit n` is path connected. -/
theorem sphereInUnit_pathConnected (n : ℕ) (hn : 2 ≤ n) :
    PathConnectedSpace (TopCat.of (sphereInUnit n)) := by
  have hY : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [← isPathConnected_iff_pathConnectedSpace]
    refine isPathConnected_sphere ?_ 0 (by norm_num)
    rw [show Module.rank ℝ (EuclideanSpace ℝ (Fin n)) = (n : Cardinal) from by
      have h2 := LinearEquiv.rank_eq (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv
      rw [h2]; exact rank_fin_fun n]
    norm_num; omega
  haveI := hY
  rw [pathConnectedSpace_iff_univ]
  exact ((sphereInUnitHomeomorph n).isPathConnected_preimage (s := Set.univ)).mpr
    isPathConnected_univ

/-! ## The degree-`0` map `H₀(Sⁿ⁻¹) ⟶ H₀(Dⁿ)` -/

/-- **The map `H₀(sphereInUnit n) ⟶ H₀(diskUnit n)` is onto.**  The augmentation
`H₀(-;ℤ) ⟶ ℤ` is natural (`Work.Cohomology.epsilonNaturality`) and an isomorphism for the
path-connected ball `Dⁿ`; its surjectivity on `Sⁿ⁻¹` follows from the nonemptiness of `Sⁿ⁻¹`
(send a point to `1`). -/
theorem h0_inclChains_epi (n : ℕ) (hn : 1 ≤ n) :
    Epi (HomologicalComplex.homologyMap (inclChains (diskUnit n) (sphereInUnit n)) 0) := by
  haveI hcontr : ContractibleSpace (diskUnit n) := diskUnit_contractible' n
  haveI hεX : IsIso (TopCat.singularHomology₀ε (diskUnit n) (ModuleCat.of ℤ ℤ)) := inferInstance
  have hεA : Epi (TopCat.singularHomology₀ε (TopCat.of (sphereInUnit n)) (ModuleCat.of ℤ ℤ)) := by
    obtain ⟨a, ha⟩ := sphereInUnit_nonempty n hn
    let p : TopCat.of PUnit ⟶ TopCat.of (sphereInUnit n) :=
      TopCat.ofHom (ContinuousMap.const PUnit ⟨a, ha⟩)
    have hnat2 := epsilonNaturality (TopCat.of PUnit) (TopCat.of (sphereInUnit n)) p
    haveI : IsIso (TopCat.singularHomology₀ε (TopCat.of PUnit) (ModuleCat.of ℤ ℤ)) :=
      inferInstance
    haveI : Epi (HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of PUnit) (TopCat.of (sphereInUnit n)) p) 0
        ≫ TopCat.singularHomology₀ε (TopCat.of (sphereInUnit n)) (ModuleCat.of ℤ ℤ)) := by
      rw [hnat2]; infer_instance
    exact epi_of_epi
      (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of PUnit)
        (TopCat.of (sphereInUnit n)) p) 0)
      (TopCat.singularHomology₀ε (TopCat.of (sphereInUnit n)) (ModuleCat.of ℤ ℤ))
  have hnat := epsilonNaturality (TopCat.of (sphereInUnit n)) (diskUnit n)
    (subtypeIncl (diskUnit n) (sphereInUnit n))
  have hα : HomologicalComplex.homologyMap (inclChains (diskUnit n) (sphereInUnit n)) 0
      = TopCat.singularHomology₀ε (TopCat.of (sphereInUnit n)) (ModuleCat.of ℤ ℤ)
        ≫ inv (TopCat.singularHomology₀ε (diskUnit n) (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hα]
  exact epi_comp _ _

/-- **For `n ≥ 2` the map `H₀(Sⁿ⁻¹) ⟶ H₀(Dⁿ)` is an isomorphism.**  Both spaces are
path connected, so the natural augmentation is an isomorphism on each, and the map agrees with
the identity of `ℤ` through it. -/
theorem h0_inclChains_isIso (n : ℕ) (hn : 2 ≤ n) :
    IsIso (HomologicalComplex.homologyMap (inclChains (diskUnit n) (sphereInUnit n)) 0) := by
  haveI hcontr : ContractibleSpace (diskUnit n) := diskUnit_contractible' n
  haveI hpcA : PathConnectedSpace (TopCat.of (sphereInUnit n)) := sphereInUnit_pathConnected n hn
  haveI hεX : IsIso (TopCat.singularHomology₀ε (diskUnit n) (ModuleCat.of ℤ ℤ)) := inferInstance
  haveI hεA : IsIso (TopCat.singularHomology₀ε (TopCat.of (sphereInUnit n))
    (ModuleCat.of ℤ ℤ)) := inferInstance
  have hnat := epsilonNaturality (TopCat.of (sphereInUnit n)) (diskUnit n)
    (subtypeIncl (diskUnit n) (sphereInUnit n))
  have hα : HomologicalComplex.homologyMap (inclChains (diskUnit n) (sphereInUnit n)) 0
      = TopCat.singularHomology₀ε (TopCat.of (sphereInUnit n)) (ModuleCat.of ℤ ℤ)
        ≫ inv (TopCat.singularHomology₀ε (diskUnit n) (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hα]
  infer_instance

/-! ## Vanishing of the homology of `Sⁿ⁻¹` below the top degree -/

/-- **`H_j(Sⁿ⁻¹) = 0` for `1 ≤ j` and `j ≠ n - 1`, when `n ≥ 2`**: the sphere
`sphereInUnit n ⊆ Dⁿ` is homeomorphic to the standard sphere `Sⁿ⁻¹ ⊆ ℝⁿ`
(`Work.Cohomology.sphereInUnitHomologyIso`), whose homology is computed by
`Work.Cohomology.sphereVanishing`. -/
theorem sphereInUnit_homology_zero_of_two_le (n j : ℕ) (hn : 2 ≤ n) (hj : 1 ≤ j)
    (hjn : j ≠ n - 1) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.Cohomology.sphereInUnit n))).homology j) := by
  obtain ⟨e⟩ := sphereInUnitHomologyIso n j
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hY := sphereVanishing (n - 1) j (by omega) (by omega) hjn
  rw [hsub] at hY
  exact IsZero.of_iso hY e

/-! ## The main theorem -/

theorem diskPairHomologyZero (n k : ℕ) (hn : 1 ≤ n) (hk : k ≠ n) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (Work.Cohomology.diskUnit n)
        (Work.Cohomology.sphereInUnit n)).homology k) := by
  haveI hcontr : ContractibleSpace (diskUnit n) := diskUnit_contractible' n
  rcases k with _ | _ | k
  · -- `k = 0`: `H₀(Sⁿ⁻¹) → H₀(Dⁿ)` is onto, so `H₀(Dⁿ, Sⁿ⁻¹) = 0`.
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    refine (hPairShort_shortExact (diskUnit n) (sphereInUnit n)).exactAt_X₃ 0
      (h0_inclChains_epi n hn) ?_
    intro j hj
    simp [ComplexShape.down] at hj
  · -- `k = 1`: `h ≠ n`, so `n ≥ 2` and `H₀(Sⁿ⁻¹) → H₀(Dⁿ)` is an isomorphism.
    have hn2 : 2 ≤ n := by omega
    haveI hδmono : Mono (hPairδ (diskUnit n) (sphereInUnit n) 0) := by
      have hX1 : CategoryTheory.Limits.IsZero
          ((Work.Cohomology.singularChains ℤ (Work.Cohomology.diskUnit n)).homology 1) :=
        homologyContractible 1 (by omega)
      have hf : HomologicalComplex.homologyMap
          (cokernel.π (inclChains (diskUnit n) (sphereInUnit n))) 1 = 0 :=
        hX1.eq_of_src _ 0
      exact (ShortComplex.exact_iff_mono _ hf).mp (hPair_exact₃ (diskUnit n) (sphereInUnit n) 0)
    have hδ0 : hPairδ (diskUnit n) (sphereInUnit n) 0 = 0 := by
      haveI : IsIso (HomologicalComplex.homologyMap
          (inclChains (diskUnit n) (sphereInUnit n)) 0) := h0_inclChains_isIso n hn2
      have hEx := hPair_exact₁ (diskUnit n) (sphereInUnit n) 0
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
      have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (inclChains (diskUnit n) (sphereInUnit n)) 0)).ker = ⊥ := by
        rw [LinearMap.ker_eq_bot]
        exact (ModuleCat.mono_iff_injective _).mp inferInstance
      rw [hker] at hEx
      exact ModuleCat.hom_ext (LinearMap.range_eq_bot.mp hEx)
    refine IsZero.iff_id_eq_zero _ |>.mpr ?_
    have h : (𝟙 _) ≫ hPairδ (diskUnit n) (sphereInUnit n) 0
        = 0 ≫ hPairδ (diskUnit n) (sphereInUnit n) 0 := by
      rw [Category.id_comp, hδ0, zero_comp]
    exact (cancel_mono (hPairδ (diskUnit n) (sphereInUnit n) 0)).mp h
  · -- `k = k + 2 ≥ 2`: `δ` is an isomorphism onto `H_{k+1}(Sⁿ⁻¹) = 0`.
    have h1 : CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℤ (Work.Cohomology.diskUnit n)).homology ((k+1)+1)) :=
      homologyContractible ((k+1)+1) (by omega)
    have h2 : CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℤ (Work.Cohomology.diskUnit n)).homology (k+1)) :=
      homologyContractible (k+1) (by omega)
    have hiso : IsIso (hPairδ (diskUnit n) (sphereInUnit n) (k+1)) :=
      hPairδ_isIso' (diskUnit n) (sphereInUnit n) (k+1) h1 h2
    have hSph : CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℤ
          (TopCat.of (Work.Cohomology.sphereInUnit n))).homology (k+1)) := by
      by_cases hn1 : n = 1
      · subst hn1
        exact sphereInUnitOneHomologyZero (k+1) (by omega)
      · exact sphereInUnit_homology_zero_of_two_le n (k+1) (by omega) (by omega) (by omega)
    exact IsZero.of_iso hSph (asIso (hPairδ (diskUnit n) (sphereInUnit n) (k+1)))

end

end Work.Cohomology
