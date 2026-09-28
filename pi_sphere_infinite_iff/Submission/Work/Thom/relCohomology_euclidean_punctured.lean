import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.diskPairCohomologyTop
import Submission.Work.Cohomology.punctured_homotopyEquiv_sphere
import Submission.Work.Cohomology.isZeroRelCohomologyZero
import Submission.Work.Cohomology.twoComponentCokernel
import Submission.Work.Cohomology.epi_singularCohomologyMap_zero
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Thom.twoComponents_puncturedOne

set_option synthInstance.maxHeartbeats 400000

/-!
# The cohomology of the Thom pair of the trivial bundle over a point

This file computes the relative cohomology `H^k(ℝⁿ, ℝⁿ∖0; ℤ)` of Euclidean `n`-space with the
origin removed: it is `ℤ` in degree `n` and `0` in every other degree.  This is the base case of
the Thom isomorphism theorem.

The strategy is the long exact sequence of the pair `(X, A)` with `X = ℝⁿ` and `A = ℝⁿ ∖ {0}`:

* degree `0` vanishes because `X` is path connected and `A` is nonempty
  (`Work.Cohomology.isZeroRelCohomologyZero`);
* in degree `1`, `H¹(X,A)` is the cokernel of the restriction `H⁰(X) ⟶ H⁰(A)`, which is `ℤ` for
  `n = 1` (the punctured line has exactly two path components, `twoComponents_puncturedOne`, and
  `Work.Cohomology.twoComponentCokernel`) and `0` for `n ≥ 2` (both spaces are path connected, so
  the restriction is onto, `Work.Cohomology.epi_singularCohomologyMap_zero`);
* in degrees `k ≥ 2`, `X` is contractible, so the connecting map
  `pairδ : H^{k-1}(A) ⟶ H^k(X,A)` is an isomorphism (`Work.Cohomology.pairδ_isIso`), and
  `A ≃ S^{n-1}` by radial normalization (`Work.Cohomology.punctured_homotopyEquiv_sphere`), whose
  cohomology is known (`Work.Cohomology.sphereCohomology_aux`,
  `Work.Cohomology.sphereCohomologyZero`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped unitInterval

namespace Work.Thom

/-! ## Elementary facts about the punctured Euclidean space -/

/-- A homotopy equivalence transports path connectedness. -/
private lemma pathConnectedSpace_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) [PathConnectedSpace Y] :
    PathConnectedSpace X := by
  obtain ⟨H⟩ := e.left_inv
  refine ⟨⟨e.invFun (Classical.choice (PathConnectedSpace.nonempty (X := Y)))⟩, fun x y => ?_⟩
  have h2 : Joined (e.invFun (e.toFun x)) (e.invFun (e.toFun y)) :=
    (PathConnectedSpace.joined (e.toFun x) (e.toFun y)).map e.invFun.continuous
  have hx : Joined (e.invFun (e.toFun x)) x :=
    ⟨⟨⟨fun t : I => H (t, x), by fun_prop⟩,
      H.map_zero_left x, H.map_one_left x⟩⟩
  have hy : Joined (e.invFun (e.toFun y)) y :=
    ⟨⟨⟨fun t : I => H (t, y), by fun_prop⟩,
      H.map_zero_left y, H.map_one_left y⟩⟩
  exact (hx.symm.trans h2).trans hy

/-- The unit sphere `S^{n-1} ⊆ ℝⁿ` is path connected for `n ≥ 2`. -/
private lemma pathConnectedSpace_metricSphere (n : ℕ) (hn : 2 ≤ n) :
    PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  haveI : PathConnectedSpace ↥(Work.Cohomology.sphSet n) :=
    Work.Cohomology.pathConnected_sphSet n hn
  exact (Homeomorph.setCongr (Work.Cohomology.sphereSet_eq n)).symm.surjective.pathConnectedSpace
    (Homeomorph.setCongr (Work.Cohomology.sphereSet_eq n)).symm.continuous

/-- The punctured Euclidean space `ℝⁿ ∖ {0}` is path connected for `n ≥ 2`. -/
private theorem pathConnected_punctured (n : ℕ) (hn : 2 ≤ n) :
    PathConnectedSpace {v : EuclideanSpace ℝ (Fin n) // v ≠ 0} := by
  haveI : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    pathConnectedSpace_metricSphere n hn
  obtain ⟨e⟩ := Work.Cohomology.punctured_homotopyEquiv_sphere (EuclideanSpace ℝ (Fin n))
  exact pathConnectedSpace_of_homotopyEquiv e

/-- There is a nonzero vector in `ℝⁿ` when `n ≥ 1`. -/
private lemma punctured_nonempty (n : ℕ) (hn : 1 ≤ n) :
    ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}).Nonempty :=
  ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by
    intro h
    have hh := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hn⟩) h
    simp at hh⟩

/-- The cohomology of the punctured Euclidean space `ℝⁿ ∖ {0}` agrees with that of the sphere
`S^{n-1} = sphTop n`, in every degree: radial normalization is a homotopy equivalence
(`Work.Cohomology.punctured_homotopyEquiv_sphere`). -/
private theorem puncturedCohomologyIso_sphTop (n m : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ m
        (TopCat.of {v : EuclideanSpace ℝ (Fin n) // v ≠ 0}) ≅
      Work.Cohomology.singularCohomology ℤ m (Work.Cohomology.sphTop n)) := by
  obtain ⟨e⟩ := Work.Cohomology.punctured_homotopyEquiv_sphere (EuclideanSpace ℝ (Fin n))
  exact Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (e.trans (Homeomorph.setCongr (Work.Cohomology.sphereSet_eq n)).toHomotopyEquiv) m

/-! ## The three degree ranges -/

/-- **Degree zero**: `H⁰(ℝⁿ, ℝⁿ∖0; ℤ) = 0`. -/
private theorem relCoh_zero (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (RelCoh ℤ 0 (EuclideanSpace ℝ (Fin n)) {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} ≅
      ModuleCat.of ℤ (Fin (if 0 = n then 1 else 0) → ℤ)) := by
  have hz : IsZero (RelCoh ℤ 0 (EuclideanSpace ℝ (Fin n))
      {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) :=
    Work.Cohomology.isZeroRelCohomologyZero (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) (punctured_nonempty n hn)
  rw [if_neg (show ¬ (0 = n) by omega)]
  exact ⟨IsZero.iso hz (ModuleCat.isZero_of_subsingleton _)⟩

/-- **Degree one**: `H¹(ℝⁿ, ℝⁿ∖0; ℤ) = ℤ` for `n = 1` and `0` for `n ≥ 2`. -/
private theorem relCoh_one (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (RelCoh ℤ 1 (EuclideanSpace ℝ (Fin n)) {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} ≅
      ModuleCat.of ℤ (Fin (if 1 = n then 1 else 0) → ℤ)) := by
  have hz1 : IsZero (Work.Cohomology.singularCohomology ℤ 1
      (TopCat.of (EuclideanSpace ℝ (Fin n)))) := by
    simpa using Work.Cohomology.contractible ℤ (TopCat.of (EuclideanSpace ℝ (Fin n))) 0
  obtain ⟨e1⟩ := Work.Cohomology.relCohomologyOne_iso_coker (TopCat.of (EuclideanSpace ℝ (Fin n)))
    ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hz1
  by_cases h1 : 1 = n
  · -- `n = 1`: the punctured line has two path components, so the cokernel is `ℤ`
    rw [if_pos h1]
    obtain ⟨e2⟩ := Work.Cohomology.twoComponentCokernel
      (Y := TopCat.of (EuclideanSpace ℝ (Fin n)))
      (Z := TopCat.of {v : EuclideanSpace ℝ (Fin n) // v ≠ 0})
      (Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin n)))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}))
      (by
        rw [← h1]
        exact twoComponents_puncturedOne)
    exact ⟨e1 ≪≫ e2 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · -- `n ≥ 2`: both spaces are path connected, so the restriction is onto and the cokernel is `0`
    rw [if_neg h1]
    have hn2 : 2 ≤ n := by omega
    haveI : PathConnectedSpace ↥(TopCat.of {v : EuclideanSpace ℝ (Fin n) // v ≠ 0}) :=
      pathConnected_punctured n hn2
    haveI : Epi (Work.Cohomology.singularCohomologyMap ℤ
        (TopCat.of {v : EuclideanSpace ℝ (Fin n) // v ≠ 0})
        (TopCat.of (EuclideanSpace ℝ (Fin n)))
        (Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin n)))
          ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})) 0) :=
      Work.Cohomology.epi_singularCohomologyMap_zero _
    have hz2 : IsZero (cokernel (Work.Cohomology.singularCohomologyMap ℤ
        (TopCat.of {v : EuclideanSpace ℝ (Fin n) // v ≠ 0})
        (TopCat.of (EuclideanSpace ℝ (Fin n)))
        (Work.Cohomology.subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin n)))
          ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})) 0)) :=
      isZero_cokernel_of_epi _
    exact ⟨e1 ≪≫ IsZero.iso hz2 (ModuleCat.isZero_of_subsingleton _)⟩

/-- **Degrees `k = m + 1 ≥ 2`**: `H^{m+1}(ℝⁿ, ℝⁿ∖0; ℤ) = ℤ` when `m + 1 = n` and `0` otherwise. -/
private theorem relCoh_high (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Nonempty (RelCoh ℤ (m + 1) (EuclideanSpace ℝ (Fin n))
        {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} ≅
      ModuleCat.of ℤ (Fin (if m + 1 = n then 1 else 0) → ℤ)) := by
  have hz1 : IsZero (Work.Cohomology.singularCohomology ℤ (m + 1)
      (TopCat.of (EuclideanSpace ℝ (Fin n)))) :=
    Work.Cohomology.contractible ℤ (TopCat.of (EuclideanSpace ℝ (Fin n))) m
  have hz2 : IsZero (Work.Cohomology.singularCohomology ℤ m
      (TopCat.of (EuclideanSpace ℝ (Fin n)))) := by
    have h := Work.Cohomology.contractible ℤ (TopCat.of (EuclideanSpace ℝ (Fin n))) (m - 1)
    rwa [Nat.sub_add_cancel hm] at h
  haveI hd : IsIso (Work.Cohomology.pairδ ℤ (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) m) :=
    Work.Cohomology.pairδ_isIso _ _ m hz1 hz2
  obtain ⟨e2⟩ := puncturedCohomologyIso_sphTop n m
  by_cases h : m + 1 = n
  · -- top degree: `H^{n-1}(S^{n-1}) = ℤ`
    rw [if_pos h]
    obtain ⟨e3⟩ := Work.Cohomology.sphereCohomology_aux m hm
    rw [h] at e3
    exact ⟨(asIso (Work.Cohomology.pairδ ℤ (TopCat.of (EuclideanSpace ℝ (Fin n)))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) m)).symm ≪≫ e2 ≪≫ e3 ≪≫
      (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · -- all other degrees: `H^m(S^{n-1}) = 0`
    rw [if_neg h]
    have hzero : IsZero (Work.Cohomology.singularCohomology ℤ m (Work.Cohomology.sphTop n)) := by
      rcases eq_or_lt_of_le hn with hn1 | hn2
      · -- `n = 1`: `S⁰`
        subst hn1
        have h3 := Work.Cohomology.sphereCohomologyZero_Sph1 (m - 1)
        rwa [Nat.sub_add_cancel hm] at h3
      · -- `n ≥ 2`: the sphere `S^{n-1}`
        have h3 := Work.Cohomology.sphereCohomologyZero (n - 1) m (by omega) (by omega) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h3
        obtain ⟨e⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
          (Homeomorph.setCongr (Work.Cohomology.sphereSet_eq n)).toHomotopyEquiv m
        exact IsZero.of_iso h3 e.symm
    exact ⟨(asIso (Work.Cohomology.pairδ ℤ (TopCat.of (EuclideanSpace ℝ (Fin n)))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) m)).symm ≪≫ e2 ≪≫
      IsZero.iso hzero (ModuleCat.isZero_of_subsingleton _)⟩

/-- The **cohomology of the Thom pair of the trivial bundle over a point**: for `n ≥ 1` the
relative cohomology `H^k(ℝⁿ, ℝⁿ∖0; ℤ)` of Euclidean `n`-space with the origin removed is `ℤ` in
degree `n` and `0` in every other degree.  This is the base case of the Thom isomorphism
theorem (`Work.Thom.ThomClassExists`): the Thom pair of the trivial rank-`n` bundle over a point.

Suggested route: `pairδ : H^{k-1}(ℝⁿ∖0) → H^k(ℝⁿ,ℝⁿ∖0)` is an isomorphism for `k ≥ 2` because
`ℝⁿ` is contractible (`Work.Cohomology.contractible`); `ℝⁿ∖0` is homotopy equivalent to `S^{n-1}`
(`Work.Cohomology.punctured_homotopyEquiv_sphere` + `Work.Cohomology.homotopyEquiv`), whose
cohomology is known (`Work.Cohomology.sphereCohomology_aux`, `Work.Cohomology.sphereCohomologyZero`);
degree `0` vanishes by `Work.Cohomology.isZeroRelCohomologyZero`, degree `1` by the cokernel
argument of `Work.Cohomology.diskPairCohomologyOne_aux`.  Alternatively transport
`Work.Cohomology.diskPairCohomologyTop` along the pair homeomorphism
`(ℝⁿ,ℝⁿ∖0) ≅ (Dⁿ, S^{n-1})` up to the deformation retraction of the punctured disc. -/
theorem relCohomology_euclidean_punctured (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    Nonempty (Work.Thom.RelCoh ℤ k (EuclideanSpace ℝ (Fin n))
      {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} ≅
      ModuleCat.of ℤ (Fin (if k = n then 1 else 0) → ℤ)) := by
  rcases k with _ | m
  · exact relCoh_zero n hn
  · rcases m with _ | m
    · exact relCoh_one n hn
    · exact relCoh_high n (m + 1) hn (by omega)

end Work.Thom
