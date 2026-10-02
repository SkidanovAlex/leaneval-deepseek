import Mathlib
import Submission.Work.Cohomology.Duality.convex_compl_sphere
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.diskPairHomologyTop
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.euclideanLocalHomologyZero
import Submission.Work.Cohomology.euclideanLocalHomologyTop
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Local homology of `ℝⁿ` at a compact convex set

For a nonempty compact convex set `K ⊆ ℝⁿ` (`n ≥ 1`) the relative singular homology (with `ℤ`
coefficients) of the pair `(ℝⁿ, ℝⁿ ∖ K)` is that of a "local pair": it vanishes in all degrees
`i ≠ n` and is `ℤ` in degree `n`:

`Hᵢ(ℝⁿ, ℝⁿ ∖ K; ℤ) = 0` (`i ≠ n`),  `Hₙ(ℝⁿ, ℝⁿ ∖ K; ℤ) ≅ ℤ`.

This is the base case of the local theory of `H_*(M | A)` (Hatcher, Lemma 3.27) for the standard
`n`-manifold `ℝⁿ`: for `K = {0}` it is `Work.Cohomology.euclideanLocalHomologyZero` /
`Work.Cohomology.euclideanLocalHomologyTop`.

The proof is the long exact sequence of the pair `(X, A)`, `X = ℝⁿ`, `A = ℝⁿ ∖ K`:

* `X` is contractible, hence `H_j(X) = 0` for `j ≥ 1`
  (`Work.Cohomology.homologyContractible`);
* `A` is homotopy equivalent to the unit sphere `S^{n-1}`
  (`Work.Cohomology.Duality.convex_compl_homotopyEquiv_sphere`), which supplies both the vanishing
  `H_j(A) = 0` for `j ≥ 1`, `j ≠ n - 1` and the top computation `H_{n-1}(A) ≅ ℤ`;
* degree by degree the connecting map `δ` of the pair then exhibits `Hᵢ(X, A)` either as `0` or as
  `H_{n-1}(A) ≅ ℤ` (`Work.Cohomology.hPairδ_isIso`, `Work.Cohomology.hPair_exact₁/₃`), with the
  degrees `0` and `1` handled by the connectivity of `A`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology.Duality

noncomputable section

/-! ## Elementary facts about the complement of a compact set -/

/-- **The complement of a compact set in `ℝⁿ` is nonempty** (`n ≥ 1`): a compact set is bounded,
whereas `ℝⁿ` is not. -/
theorem compl_nonempty (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKc : IsCompact K) : {y : EuclideanSpace ℝ (Fin n) | y ∉ K}.Nonempty := by
  obtain ⟨R, _hR, hsub⟩ := hKc.isBounded.subset_ball_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  refine ⟨EuclideanSpace.single ⟨0, hn⟩ (R + 1), ?_⟩
  intro hmem
  have hb : dist (EuclideanSpace.single (⟨0, hn⟩ : Fin n) (R + 1)) 0 < R :=
    Metric.mem_ball.mp (hsub hmem)
  rw [dist_zero_right] at hb
  have hnorm : ‖(EuclideanSpace.single (⟨0, hn⟩ : Fin n) (R + 1) :
      EuclideanSpace ℝ (Fin n))‖ = R + 1 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hnorm] at hb
  linarith

/-! ## The homology of the complement -/

/-- **`H_j(ℝⁿ ∖ K) = 0` for `j ≥ 1`, `j ≠ n - 1`** (`K` nonempty compact convex in `ℝⁿ`).

The complement is homotopy equivalent to `S^{n-1}`
(`Work.Cohomology.Duality.convex_compl_homotopyEquiv_sphere`), and vanishing of homology is a
homotopy invariant (`Work.Cohomology.isZero_homology_of_homotopyEquiv`). -/
theorem complHomologyZero (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKc : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j ≠ n - 1) :
    IsZero ((singularChains ℤ
      (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K})).homology j) := by
  obtain ⟨e⟩ := convex_compl_homotopyEquiv_sphere K hKc hconv hne
  exact isZero_homology_of_homotopyEquiv e j (sphereModelHomologyZero n j hn hj hjn)

/-- **`H_{n-1}(ℝⁿ ∖ K) ≅ ℤ`** (`K` nonempty compact convex in `ℝⁿ`, `n ≥ 2`), because the
complement is homotopy equivalent to `S^{n-1}` and `H_{n-1}(S^{n-1}) ≅ ℤ`
(`Work.Cohomology.sphereHomologyTop`). -/
theorem complHomologyTop (n : ℕ) (hn : 2 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKc : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    Nonempty ((singularChains ℤ
      (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K})).homology (n - 1) ≅
      ModuleCat.of ℤ ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨e⟩ := convex_compl_homotopyEquiv_sphere K hKc hconv hne
  obtain ⟨e1⟩ := homologyIso_of_homotopyEquiv e (k + 1)
  refine ⟨e1 ≪≫ ?_⟩
  exact Classical.choice (sphereHomologyTop (k + 1) (by omega))

/-! ## The augmentation of the complement -/

/-- The model sphere `{x : ℝⁿ // ‖x‖ = 1}` is path connected for `n ≥ 2`. -/
theorem pathConnectedSpace_sphereModel (n : ℕ) (hn : 2 ≤ n) :
    PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have h : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    refine isPathConnected_sphere ?_ 0 (by norm_num)
    rw [show Module.rank ℝ (EuclideanSpace ℝ (Fin n)) = (n : Cardinal) from by
      have h2 := LinearEquiv.rank_eq (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv
      rw [h2]; exact rank_fin_fun n]
    norm_num
    omega
  exact isPathConnected_iff_pathConnectedSpace.mp h

/-- **The augmentation `H₀(ℝⁿ ∖ K) ⟶ ℤ` is an isomorphism** for `n ≥ 2`.  The complement is
homotopy equivalent to the path connected space `S^{n-1}`, along which the augmentation is
natural. -/
theorem isIso_eps_compl (n : ℕ) (hn : 2 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKc : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    IsIso (TopCat.singularHomology₀ε
      (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) (ModuleCat.of ℤ ℤ)) := by
  obtain ⟨e⟩ := convex_compl_homotopyEquiv_sphere K hKc hconv hne
  let f : TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K} ⟶
      TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := TopCat.ofHom e.toFun
  let g : TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ⟶
      TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K} := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g)
      (𝟙 (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K})) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f)
      (𝟙 (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))) := e.right_inv.some
  haveI hiso : IsIso (HomologicalComplex.homologyMap (chainMap ℤ _ _ f) 0) :=
    homologyEquiv ℤ _ _ f g h1 h2 0
  haveI hpc : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    pathConnectedSpace_sphereModel n hn
  haveI : IsIso (TopCat.singularHomology₀ε
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) (ModuleCat.of ℤ ℤ)) :=
    inferInstance
  have hnat := epsilonNaturality (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K})
    (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) f
  rw [← hnat]
  infer_instance

/-! ## The degree-`0` map induced by the inclusion of the complement -/

/-- **The map `H₀(ℝⁿ ∖ K) ⟶ H₀(ℝⁿ)` is an isomorphism** for `n ≥ 2`: it is the augmentation of
the complement followed by the inverse of the (invertible) augmentation of the contractible
`ℝⁿ`. -/
theorem h0_compl_inclChains_isIso (n : ℕ) (hn : 2 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKc : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    IsIso (HomologicalComplex.homologyMap
      (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
        {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) 0) := by
  haveI hcontr : ContractibleSpace (TopCat.of (EuclideanSpace ℝ (Fin n))) := inferInstance
  haveI hεX : IsIso (TopCat.singularHomology₀ε
      (TopCat.of (EuclideanSpace ℝ (Fin n))) (ModuleCat.of ℤ ℤ)) := inferInstance
  haveI hεA : IsIso (TopCat.singularHomology₀ε
      (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) (ModuleCat.of ℤ ℤ)) :=
    isIso_eps_compl n hn K hKc hconv hne
  have hnat := epsilonNaturality (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K})
    (TopCat.of (EuclideanSpace ℝ (Fin n)))
    (subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin n))) {y : EuclideanSpace ℝ (Fin n) | y ∉ K})
  have hα : HomologicalComplex.homologyMap
        (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
          {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) 0
      = TopCat.singularHomology₀ε
          (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) (ModuleCat.of ℤ ℤ)
        ≫ inv (TopCat.singularHomology₀ε
          (TopCat.of (EuclideanSpace ℝ (Fin n))) (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hα]
  infer_instance

/-- **The map `H₀(ℝⁿ ∖ K) ⟶ H₀(ℝⁿ)` is onto** for `n ≥ 1`.  The augmentation of a nonempty space
is onto; here the complement is nonempty because `K` is compact. -/
theorem h0_compl_inclChains_epi (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKc : IsCompact K) :
    Epi (HomologicalComplex.homologyMap
      (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
        {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) 0) := by
  haveI hcontr : ContractibleSpace (TopCat.of (EuclideanSpace ℝ (Fin n))) := inferInstance
  haveI hεX : IsIso (TopCat.singularHomology₀ε
      (TopCat.of (EuclideanSpace ℝ (Fin n))) (ModuleCat.of ℤ ℤ)) := inferInstance
  have hεA : Epi (TopCat.singularHomology₀ε
      (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) (ModuleCat.of ℤ ℤ)) := by
    obtain ⟨a, ha⟩ := compl_nonempty n hn K hKc
    let p : TopCat.of PUnit ⟶ TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K} :=
      TopCat.ofHom (ContinuousMap.const PUnit ⟨a, ha⟩)
    have hnat2 := epsilonNaturality (TopCat.of PUnit)
      (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) p
    haveI : IsIso (TopCat.singularHomology₀ε (TopCat.of PUnit) (ModuleCat.of ℤ ℤ)) :=
      inferInstance
    haveI : Epi (HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of PUnit)
          (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) p) 0
        ≫ TopCat.singularHomology₀ε
          (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) (ModuleCat.of ℤ ℤ)) := by
      rw [hnat2]; infer_instance
    exact epi_of_epi
      (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of PUnit)
        (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) p) 0)
      (TopCat.singularHomology₀ε
        (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) (ModuleCat.of ℤ ℤ))
  have hnat := epsilonNaturality (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K})
    (TopCat.of (EuclideanSpace ℝ (Fin n)))
    (subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin n))) {y : EuclideanSpace ℝ (Fin n) | y ∉ K})
  have hα : HomologicalComplex.homologyMap
        (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
          {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) 0
      = TopCat.singularHomology₀ε
          (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) (ModuleCat.of ℤ ℤ)
        ≫ inv (TopCat.singularHomology₀ε
          (TopCat.of (EuclideanSpace ℝ (Fin n))) (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hα]
  exact epi_comp _ _

/-! ## Vanishing of the relative homology in all degrees `≠ n` -/

theorem relChains_compl_homology_zero (n : ℕ) (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKc : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (i : ℕ) (hi : i ≠ n) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
      {y : EuclideanSpace ℝ (Fin n) | y ∉ K}).homology i) := by
  rcases i with _ | _ | i
  · -- `i = 0`: `H₀(ℝⁿ ∖ K) ⟶ H₀(ℝⁿ)` is onto, so `H₀(ℝⁿ, ℝⁿ ∖ K) = 0`.
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    refine (hPairShort_shortExact (TopCat.of (EuclideanSpace ℝ (Fin n)))
      {y : EuclideanSpace ℝ (Fin n) | y ∉ K}).exactAt_X₃ 0
      (h0_compl_inclChains_epi n hn K hKc) ?_
    intro j hj
    simp [ComplexShape.down] at hj
  · -- `i = 1`: `1 ≠ n`, so `n ≥ 2` and `H₀(ℝⁿ ∖ K) ⟶ H₀(ℝⁿ)` is an isomorphism.
    have hn2 : 2 ≤ n := by omega
    haveI hδmono : Mono (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n)))
        {y : EuclideanSpace ℝ (Fin n) | y ∉ K} 0) := by
      have hX1 : IsZero ((singularChains ℤ
          (TopCat.of (EuclideanSpace ℝ (Fin n)))).homology 1) :=
        homologyContractible 1 (by norm_num)
      have hf : HomologicalComplex.homologyMap
          (cokernel.π (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
            {y : EuclideanSpace ℝ (Fin n) | y ∉ K})) 1 = 0 :=
        hX1.eq_of_src _ 0
      exact (ShortComplex.exact_iff_mono _ hf).mp
        (hPair_exact₃ (TopCat.of (EuclideanSpace ℝ (Fin n)))
          {y : EuclideanSpace ℝ (Fin n) | y ∉ K} 0)
    have hδ0 : hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n)))
        {y : EuclideanSpace ℝ (Fin n) | y ∉ K} 0 = 0 := by
      haveI : IsIso (HomologicalComplex.homologyMap
          (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
            {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) 0) :=
        h0_compl_inclChains_isIso n hn2 K hKc hconv hne
      have hEx := hPair_exact₁ (TopCat.of (EuclideanSpace ℝ (Fin n)))
        {y : EuclideanSpace ℝ (Fin n) | y ∉ K} 0
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
      have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (inclChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
            {y : EuclideanSpace ℝ (Fin n) | y ∉ K}) 0)).ker = ⊥ := by
        rw [LinearMap.ker_eq_bot]
        exact (ModuleCat.mono_iff_injective _).mp inferInstance
      rw [hker] at hEx
      exact ModuleCat.hom_ext (LinearMap.range_eq_bot.mp hEx)
    refine IsZero.iff_id_eq_zero _ |>.mpr ?_
    have h : (𝟙 _) ≫ hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n)))
          {y : EuclideanSpace ℝ (Fin n) | y ∉ K} 0
        = 0 ≫ hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n)))
          {y : EuclideanSpace ℝ (Fin n) | y ∉ K} 0 := by
      rw [Category.id_comp, hδ0, zero_comp]
    exact (cancel_mono (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n)))
      {y : EuclideanSpace ℝ (Fin n) | y ∉ K} 0)).mp h
  · -- `i = i + 2 ≥ 2`: `δ` is an isomorphism onto `H_{i+1}(ℝⁿ ∖ K) = 0`.
    have h1 : IsZero ((singularChains ℤ
        (TopCat.of (EuclideanSpace ℝ (Fin n)))).homology ((i + 1) + 1)) :=
      homologyContractible ((i + 1) + 1) (by omega)
    have h2 : IsZero ((singularChains ℤ
        (TopCat.of (EuclideanSpace ℝ (Fin n)))).homology (i + 1)) :=
      homologyContractible (i + 1) (by omega)
    have hiso : IsIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n)))
        {y : EuclideanSpace ℝ (Fin n) | y ∉ K} (i + 1)) :=
      hPairδ_isIso (TopCat.of (EuclideanSpace ℝ (Fin n)))
        {y : EuclideanSpace ℝ (Fin n) | y ∉ K} (i + 1) h1 h2
    have hA : IsZero ((singularChains ℤ
        (TopCat.of {y : EuclideanSpace ℝ (Fin n) | y ∉ K})).homology (i + 1)) :=
      complHomologyZero n hn K hKc hconv hne (i + 1) (by omega) (by omega)
    exact IsZero.of_iso hA (asIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin n)))
      {y : EuclideanSpace ℝ (Fin n) | y ∉ K} (i + 1)))

/-! ## The top relative homology -/

theorem relChains_compl_homology_top (n : ℕ) (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKc : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
      {y : EuclideanSpace ℝ (Fin n) | y ∉ K}).homology n ≅ ModuleCat.of ℤ ℤ) := by
  by_cases h1 : n = 1
  · -- `n = 1`: the sequence stops at `H₀`, and `H₁(ℝ, ℝ ∖ K)` is the reduced `H₀` of a two point
    -- space.
    subst h1
    have h1z : IsZero ((singularChains ℤ
        (TopCat.of (EuclideanSpace ℝ (Fin 1)))).homology 1) :=
      homologyContractible 1 (by norm_num)
    refine relH1OfPairAux (TopCat.of (EuclideanSpace ℝ (Fin 1)))
      {y : EuclideanSpace ℝ (Fin 1) | y ∉ K} h1z inferInstance ?_
    obtain ⟨eH⟩ := ker_eps_homotopyEquiv
      (Classical.choice (convex_compl_homotopyEquiv_sphere K hKc hconv hne))
    obtain ⟨eS⟩ := ker_eps_homotopyEquiv (sphereInUnitHomeomorph 1).toHomotopyEquiv
    obtain ⟨e4⟩ := reducedH0SphereInUnitOne
    exact ⟨eH ≪≫ eS.symm ≪≫ moduleCatOfIsoOfEq ≪≫ e4⟩
  · -- `n ≥ 2`: write `n = k + 2`, so that `n - 1` computes to `k + 1`; then the connecting map
    -- is an isomorphism onto `H_{k+1}(S^{k+1}) ≅ ℤ`.
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    haveI hiso : IsIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin (k + 2))))
        {y : EuclideanSpace ℝ (Fin (k + 2)) | y ∉ K} (k + 1)) :=
      hPairδ_isIso (TopCat.of (EuclideanSpace ℝ (Fin (k + 2))))
        {y : EuclideanSpace ℝ (Fin (k + 2)) | y ∉ K} (k + 1)
        (homologyContractible ((k + 1) + 1) (by omega))
        (homologyContractible (k + 1) (by omega))
    obtain ⟨e⟩ := convex_compl_homotopyEquiv_sphere K hKc hconv hne
    refine ⟨asIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin (k + 2))))
        {y : EuclideanSpace ℝ (Fin (k + 2)) | y ∉ K} (k + 1))
      ≪≫ Classical.choice (homologyIso_of_homotopyEquiv e (k + 1)) ≪≫ ?_⟩
    exact Classical.choice (sphereHomologyTop (k + 1) (by omega))

/-! ## The main statement -/

theorem ball_local_homology (n : ℕ) (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKc : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    (∀ i : ℕ, i ≠ n → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
        {y : EuclideanSpace ℝ (Fin n) | y ∉ K}).homology i)) ∧
    Nonempty (((Work.Cohomology.relChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
        {y : EuclideanSpace ℝ (Fin n) | y ∉ K}).homology n) ≅ ModuleCat.of ℤ ℤ) := by
  refine ⟨fun i hi => relChains_compl_homology_zero n hn K hKc hconv hne i hi, ?_⟩
  exact relChains_compl_homology_top n hn K hKc hconv hne

end

end Work.Cohomology.Duality
