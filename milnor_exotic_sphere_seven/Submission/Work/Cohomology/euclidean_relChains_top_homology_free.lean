import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.diskPairHomologyZero
import Submission.Work.Cohomology.euclidean_compl_top_homology_free
import Submission.Work.Cohomology.relChains_top_homology_free_dim_one

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The top relative homology of the complement of a compact set in `ℝ^N` is free

For `N ≥ 1` and a compact set `C ⊆ ℝ^N`, the `N`-th singular homology of the pair
`(ℝ^N, ℝ^N∖C)` is a free `ℤ`-module.

## Definitions used below

* `relChainsInclSet X h` — the map of relative chain complexes `C_*(X,A) ⟶ C_*(X,B)` induced by
  an inclusion `A ⊆ B` of the *excluded* sets;
* `localDegreeMap C x hx n` — the localization `H_n(X, X∖C) ⟶ H_n(X, X∖{x})` for `x ∈ C`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The map of relative chain complexes `C_*(X,A) ⟶ C_*(X,B)` induced by an inclusion `A ⊆ B` of
the excluded sets. -/
def relChainsInclSet (X : TopCat) {A B : Set X} (h : A ⊆ B) :
    relChains X A ⟶ relChains X B :=
  relChainsMapOf X X A B (𝟙 X)
    (TopCat.ofHom ⟨fun a => ⟨a.1, h a.2⟩,
      Continuous.subtype_mk continuous_subtype_val (fun a => h a.2)⟩)
    (by apply TopCat.ext; intro a; rfl)

/-- The localization map `H_n(X, X∖C) ⟶ H_n(X, X∖{x})` of relative homology, for `x ∈ C`. -/
def localDegreeMap {N : ℕ} (C : Set (EuclideanSpace ℝ (Fin N)))
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ C) (n : ℕ) :
    ((relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) {y | y ∉ C}).homology n) →ₗ[ℤ]
      ((relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
        {y | y ∉ ({x} : Set (EuclideanSpace ℝ (Fin N)))}).homology n) :=
  (HomologicalComplex.homologyMap
    (relChainsInclSet _ (fun y hy => by
      simp only [Set.mem_ofPred_eq] at hy ⊢
      rintro rfl
      exact hy hx)) n).hom

theorem euclidean_relChains_top_homology_free {N : ℕ} (hN : 1 ≤ N)
    (C : Set (EuclideanSpace ℝ (Fin N))) (hC : IsCompact C) :
    Module.Free ℤ ↥((Work.Cohomology.relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
      {y : EuclideanSpace ℝ (Fin N) | y ∉ C}).homology N) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hU : IsOpen {y : EuclideanSpace ℝ (Fin (n + 1)) | y ∉ C} := hC.isClosed.isOpen_compl
  cases n with
  | zero =>
      -- `N = 1`: this is the separately proved case `Work.Cohomology.relChains_top_homology_free_dim_one`
      exact relChains_top_homology_free_dim_one C hC
  | succ k =>
      -- `N = k + 2`: the connecting map of the pair `(ℝ^{k+2}, ℝ^{k+2}∖C)` is an isomorphism
      -- onto `H_{k+1}(ℝ^{k+2}∖C)`
      haveI hcontr : ContractibleSpace (EuclideanSpace ℝ (Fin (k + 2))) := inferInstance
      haveI hiso : IsIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin (k + 2))))
          {y : EuclideanSpace ℝ (Fin (k + 2)) | y ∉ C} (k + 1)) :=
        hPairδ_isIso' _ _ (k + 1)
          (homologyContractible (X := TopCat.of (EuclideanSpace ℝ (Fin (k + 2))))
            (k + 2) (by omega))
          (homologyContractible (X := TopCat.of (EuclideanSpace ℝ (Fin (k + 2))))
            (k + 1) (by omega))
      have hfree : Module.Free ℤ
          ↥((singularChains ℤ
            (TopCat.of ↥{y : EuclideanSpace ℝ (Fin (k + 2)) | y ∉ C})).homology (k + 1)) :=
        euclidean_compl_top_homology_free (N := k + 2) (by omega) C hC
      exact Module.Free.of_equiv' hfree
        (asIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin (k + 2))))
          {y : EuclideanSpace ℝ (Fin (k + 2)) | y ∉ C} (k + 1))).toLinearEquiv.symm

end

end Work.Cohomology
