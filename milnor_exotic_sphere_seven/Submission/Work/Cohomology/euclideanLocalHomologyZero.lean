import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.diskPairHomologyZero
import Submission.Work.Cohomology.punctured_homotopyEquiv_sphere
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.sphereInUnitOneHomologyZero
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv
import Submission.Work.Cohomology.epsilonNaturality
import Submission.Work.Cohomology.homologyContractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of the lower local homology of `ℝⁿ` at the origin

For `n ≥ 1` the relative singular homology (with `ℤ` coefficients) of the pair
`(ℝⁿ, ℝⁿ ∖ {0})` vanishes in every degree `k ≠ n`:

`H_k(ℝⁿ, ℝⁿ ∖ {0}; ℤ) = 0`  for `k ≠ n`.

This is the companion of `Work.Cohomology.euclideanLocalHomologyTop`
(`Hₙ(ℝⁿ, ℝⁿ ∖ {0}) ≅ ℤ`) and the flat model of `Work.Cohomology.localHomology`.

The proof follows the pattern of `Work.Cohomology.diskPairHomologyZero` for the pair
`(Dⁿ, Sⁿ⁻¹)`, with the punctured Euclidean space in place of the sphere, using that
`ℝⁿ ∖ {0}` is homotopy equivalent to `Sⁿ⁻¹`
(`Work.Cohomology.punctured_homotopyEquiv_sphere`) and that `ℝⁿ` is contractible
(`Work.Cohomology.homologyContractible`):

* `k ≥ 2`: the connecting map `δ` of the long exact sequence of the pair is an isomorphism
  (`Work.Cohomology.hPairδ_isIso'`) onto `H_{k-1}(ℝⁿ ∖ {0}) ≅ H_{k-1}(Sⁿ⁻¹)`, which vanishes
  for `k - 1 ≥ 1`, `k ≠ n` by `Work.Cohomology.sphereVanishing`;
* `k = 1`: `δ : H₁(ℝⁿ, ℝⁿ ∖ {0}) ⟶ H₀(ℝⁿ ∖ {0})` is injective (its source `H₁(ℝⁿ)` is zero)
  and zero because `H₀(ℝⁿ ∖ {0}) ⟶ H₀(ℝⁿ)` is an isomorphism for `n ≥ 2`;
* `k = 0`: the exactness `H₀(ℝⁿ) ⟶ H₀(ℝⁿ, ℝⁿ ∖ {0}) ⟶ 0` exhibits `H₀(ℝⁿ, ℝⁿ ∖ {0})` as a
  zero object because `H₀(ℝⁿ ∖ {0}) ⟶ H₀(ℝⁿ)` is onto.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Metric

namespace Work.Cohomology

noncomputable section

/-- The punctured Euclidean space `ℝⁿ ∖ {0}`, as a subset of `ℝⁿ`. -/
abbrev punctEuc (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {v | v ≠ 0}

/-! ## Elementary geometry of the punctured Euclidean space -/

/-- The punctured Euclidean space is nonempty as soon as `n ≥ 1`. -/
theorem punctEuc_nonempty (n : ℕ) (hn : 1 ≤ n) : (punctEuc n).Nonempty := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨EuclideanSpace.single i (1 : ℝ), ?_⟩
  simp only [punctEuc, Set.mem_ofPred_eq]
  intro hzero
  have hnorm : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
    rw [PiLp.norm_single]; norm_num
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- For `n ≥ 2` the punctured Euclidean space is path connected: it is the complement of a
singleton in a real normed space of real rank `> 1`. -/
theorem punctEuc_pathConnected (n : ℕ) (hn : 2 ≤ n) :
    PathConnectedSpace (TopCat.of (punctEuc n)) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [show Module.rank ℝ (EuclideanSpace ℝ (Fin n)) = (n : Cardinal) from by
      have h2 := LinearEquiv.rank_eq (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv
      rw [h2]; exact rank_fin_fun n]
    norm_num
    omega
  have h : IsPathConnected (punctEuc n : Set (EuclideanSpace ℝ (Fin n))) := by
    convert isPathConnected_compl_singleton_of_one_lt_rank hrank
      (0 : EuclideanSpace ℝ (Fin n)) using 1
    ext x
    simp [punctEuc]
  exact isPathConnected_iff_pathConnectedSpace.mp h

/-! ## Vanishing of the homology of the standard model of `Sⁿ⁻¹` -/

/-- **`H_j(Sⁿ⁻¹) = 0` for `j ≥ 1`, `j ≠ n - 1`**, for the standard model
`Sⁿ⁻¹ = Metric.sphere (0 : ℝⁿ) 1` of the unit sphere. -/
theorem sphereModelHomologyZero (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≠ n - 1) :
    IsZero ((singularChains ℤ
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))).homology j) := by
  rcases n with _ | n'
  · omega
  rcases n' with _ | n''
  · -- `n = 1`: `S⁰` is a finite discrete space
    haveI : Fintype ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
      finite_metricSphere_fin_one.fintype
    haveI : TotallyDisconnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
      inferInstance
    exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) j (ModuleCat.of ℤ ℤ)
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) (by omega)
  · -- `n ≥ 2`
    have h := sphereVanishing (n'' + 1) j (by omega) (by omega) (by omega)
    simpa using h

/-! ## Vanishing of the homology of the punctured Euclidean space -/

/-- **`H_j(ℝⁿ ∖ {0}) = 0` for `j ≥ 1`, `j ≠ n - 1`.**  The punctured space is homotopy
equivalent to `Sⁿ⁻¹`, and vanishing of homology is a homotopy invariant. -/
theorem punctEuc_homology_zero (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≠ n - 1) :
    IsZero ((singularChains ℤ (TopCat.of (punctEuc n))).homology j) := by
  obtain ⟨e⟩ := punctured_homotopyEquiv_sphere (EuclideanSpace ℝ (Fin n))
  exact isZero_homology_of_homotopyEquiv e j (sphereModelHomologyZero n j hn hj hjn)

/-! ## The degree-`0` map `H₀(ℝⁿ ∖ {0}) ⟶ H₀(ℝⁿ)` -/

/-- **The map `H₀(ℝⁿ ∖ {0}) ⟶ H₀(ℝⁿ)` is onto** (for `n ≥ 1`): the augmentation
`H₀(-;ℤ) ⟶ ℤ` is natural and an isomorphism for the contractible `ℝⁿ`, while it is onto for the
nonempty punctured space. -/
theorem h0_punctEuc_inclChains_epi (n : ℕ) (hn : 1 ≤ n) :
    Epi (HomologicalComplex.homologyMap
      (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n)) 0) := by
  haveI hcontr : ContractibleSpace (TopCat.of (EuclideanSpace ℝ (Fin n))) := inferInstance
  haveI hεX : IsIso (TopCat.singularHomology₀ε (TopCat.of (EuclideanSpace ℝ (Fin n)))
    (ModuleCat.of ℤ ℤ)) := inferInstance
  have hεA : Epi (TopCat.singularHomology₀ε (TopCat.of (punctEuc n)) (ModuleCat.of ℤ ℤ)) := by
    obtain ⟨a, ha⟩ := punctEuc_nonempty n hn
    let p : TopCat.of PUnit ⟶ TopCat.of (punctEuc n) :=
      TopCat.ofHom (ContinuousMap.const PUnit ⟨a, ha⟩)
    have hnat2 := epsilonNaturality (TopCat.of PUnit) (TopCat.of (punctEuc n)) p
    haveI : IsIso (TopCat.singularHomology₀ε (TopCat.of PUnit) (ModuleCat.of ℤ ℤ)) :=
      inferInstance
    haveI : Epi (HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of PUnit) (TopCat.of (punctEuc n)) p) 0
        ≫ TopCat.singularHomology₀ε (TopCat.of (punctEuc n)) (ModuleCat.of ℤ ℤ)) := by
      rw [hnat2]; infer_instance
    exact epi_of_epi
      (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of PUnit)
        (TopCat.of (punctEuc n)) p) 0)
      (TopCat.singularHomology₀ε (TopCat.of (punctEuc n)) (ModuleCat.of ℤ ℤ))
  have hnat := epsilonNaturality (TopCat.of (punctEuc n))
    (TopCat.of (EuclideanSpace ℝ (Fin n)))
    (subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n))
  have hα : HomologicalComplex.homologyMap
        (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n)) 0
      = TopCat.singularHomology₀ε (TopCat.of (punctEuc n)) (ModuleCat.of ℤ ℤ)
        ≫ inv (TopCat.singularHomology₀ε (TopCat.of (EuclideanSpace ℝ (Fin n)))
            (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hα]
  exact epi_comp _ _

/-- **For `n ≥ 2` the map `H₀(ℝⁿ ∖ {0}) ⟶ H₀(ℝⁿ)` is an isomorphism.**  Both spaces are path
connected, so the natural augmentation is an isomorphism on each, and the map agrees with the
identity of `ℤ` through it. -/
theorem h0_punctEuc_inclChains_isIso (n : ℕ) (hn : 2 ≤ n) :
    IsIso (HomologicalComplex.homologyMap
      (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n)) 0) := by
  haveI hcontr : ContractibleSpace (TopCat.of (EuclideanSpace ℝ (Fin n))) := inferInstance
  haveI hpcA : PathConnectedSpace (TopCat.of (punctEuc n)) := punctEuc_pathConnected n hn
  haveI hεX : IsIso (TopCat.singularHomology₀ε (TopCat.of (EuclideanSpace ℝ (Fin n)))
    (ModuleCat.of ℤ ℤ)) := inferInstance
  haveI hεA : IsIso (TopCat.singularHomology₀ε (TopCat.of (punctEuc n))
    (ModuleCat.of ℤ ℤ)) := inferInstance
  have hnat := epsilonNaturality (TopCat.of (punctEuc n))
    (TopCat.of (EuclideanSpace ℝ (Fin n)))
    (subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n))
  have hα : HomologicalComplex.homologyMap
        (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n)) 0
      = TopCat.singularHomology₀ε (TopCat.of (punctEuc n)) (ModuleCat.of ℤ ℤ)
        ≫ inv (TopCat.singularHomology₀ε (TopCat.of (EuclideanSpace ℝ (Fin n)))
            (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hα]
  infer_instance

/-! ## The main theorem -/

theorem euclideanLocalHomologyZero (n k : ℕ) (hn : 1 ≤ n) (hk : k ≠ n) :
    CategoryTheory.Limits.IsZero (((relChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
      {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}).homology k)) := by
  rcases k with _ | _ | k
  · -- `k = 0`: `H₀(ℝⁿ ∖ {0}) → H₀(ℝⁿ)` is onto, so `H₀(ℝⁿ, ℝⁿ ∖ {0}) = 0`.
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    refine (hPairShort_shortExact (TopCat.of (EuclideanSpace ℝ (Fin n)))
      (punctEuc n)).exactAt_X₃ 0 (h0_punctEuc_inclChains_epi n hn) ?_
    intro j hj
    simp [ComplexShape.down] at hj
  · -- `k = 1`: `1 ≠ n`, so `n ≥ 2` and `H₀(ℝⁿ ∖ {0}) ⟶ H₀(ℝⁿ)` is an isomorphism.
    have hn2 : 2 ≤ n := by omega
    haveI hδmono : Mono (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n) 0) := by
      have hX1 : CategoryTheory.Limits.IsZero
          ((singularChains ℤ (TopCat.of (EuclideanSpace ℝ (Fin n)))).homology 1) :=
        homologyContractible 1 (by norm_num)
      have hf : HomologicalComplex.homologyMap
          (cokernel.π (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n))) 1 = 0 :=
        hX1.eq_of_src _ 0
      exact (ShortComplex.exact_iff_mono _ hf).mp
        (hPair_exact₃ (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n) 0)
    have hδ0 : hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n) 0 = 0 := by
      haveI : IsIso (HomologicalComplex.homologyMap
          (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n)) 0) :=
        h0_punctEuc_inclChains_isIso n hn2
      have hEx := hPair_exact₁ (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n) 0
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
      have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n)) 0)).ker = ⊥ := by
        rw [LinearMap.ker_eq_bot]
        exact (ModuleCat.mono_iff_injective _).mp inferInstance
      rw [hker] at hEx
      exact ModuleCat.hom_ext (LinearMap.range_eq_bot.mp hEx)
    refine IsZero.iff_id_eq_zero _ |>.mpr ?_
    have h : (𝟙 _) ≫ hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n) 0
        = 0 ≫ hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n) 0 := by
      rw [Category.id_comp, hδ0, zero_comp]
    exact (cancel_mono (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n) 0)).mp h
  · -- `k = k + 2 ≥ 2`: `δ` is an isomorphism onto `H_{k+1}(ℝⁿ ∖ {0}) = 0`.
    have h1 : CategoryTheory.Limits.IsZero
        ((singularChains ℤ (TopCat.of (EuclideanSpace ℝ (Fin n)))).homology ((k+1)+1)) :=
      homologyContractible ((k+1)+1) (by omega)
    have h2 : CategoryTheory.Limits.IsZero
        ((singularChains ℤ (TopCat.of (EuclideanSpace ℝ (Fin n)))).homology (k+1)) :=
      homologyContractible (k+1) (by omega)
    have hiso : IsIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n) (k+1)) :=
      hPairδ_isIso' (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n) (k+1) h1 h2
    have hA : CategoryTheory.Limits.IsZero
        ((singularChains ℤ (TopCat.of (punctEuc n))).homology (k+1)) :=
      punctEuc_homology_zero n (k+1) hn (by omega) (by omega)
    exact IsZero.of_iso hA
      (asIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n))) (punctEuc n) (k+1)))

end

end Work.Cohomology
