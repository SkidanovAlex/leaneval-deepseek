import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.diskPairHomologyTop
import Submission.Work.Cohomology.punctured_homotopyEquiv_sphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The top local homology of `ℝⁿ` at the origin

For `n ≥ 1` the `n`-th relative singular homology (with `ℤ` coefficients) of the pair
`(ℝⁿ, ℝⁿ ∖ {0})` is `ℤ`:

`Hₙ(ℝⁿ, ℝⁿ ∖ {0}; ℤ) ≅ ℤ`.

This is the flat case of the local homology `Hₙ(M, M ∖ {x}) ≅ ℤ` of an `n`-manifold at a point
(`Work.Cohomology.localHomology` of `Submission/Work/Cohomology/localHomology.lean`) at `M = ℝⁿ`,
`x = 0`.

## Structure of the proof

The long exact sequence of the pair `(X, A)`, `X = ℝⁿ`, `A = ℝⁿ ∖ {0}`,

`Hₙ(X) ⟶ Hₙ(X,A) --δ--> Hₙ₋₁(A) ⟶ Hₙ₋₁(X)`

computes the group: `X` is convex, hence contractible (`Work.Cohomology.homologyContractible`),
so for `n ≥ 2` the connecting map `hPairδ` is an isomorphism (`Work.Cohomology.hPairδ_isIso`,
the trick of `Submission/Work/Cohomology/diskPairHomologyTop.lean`) onto
`Hₙ₋₁(A) ≅ Hₙ₋₁(Sⁿ⁻¹) ≅ ℤ`, using that the punctured space is homotopy equivalent to the unit
sphere (`Work.Cohomology.punctured_homotopyEquiv_sphere`,
`Work.Cohomology.homologyIso_of_homotopyEquiv`) and `Work.Cohomology.sphereHomologyTop`.

For `n = 1` the sequence stops at `H₀`, and the same argument exhibits `H₁(X,A)` as the reduced
zeroth homology of `A`, which is a two point space: `relH1OfPairAux` performs this reduction and
`Work.Cohomology.ker_eps_homotopyEquiv` together with
`Work.Cohomology.reducedH0SphereInUnitOne` computes the reduced `H₀` of `S⁰` as `ℤ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **A pair with vanishing `H₁` and reduced `H₀` of the subspace equal to `ℤ` has `H₁(X,A) = ℤ`.**

If `H₁(X) = 0` and the augmentation `ε_X : H₀(X) ⟶ ℤ` is invertible (as for a contractible `X`),
then the connecting map of the pair identifies `H₁(X,A)` with `ker ε_A`, the reduced zeroth
homology of `A`.

This is the argument of `Work.Cohomology.ballPairHomologyTopOne` (`Work.Cohomology.relH1OfPair`),
reproduced here so that this file does not import the (still incomplete)
`Submission/Work/Cohomology/localHomology.lean`. -/
theorem relH1OfPairAux (X : TopCat) (A : Set X)
    (h1 : IsZero ((singularChains ℤ X).homology 1))
    (hε : IsIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)))
    (hA : Nonempty (kerMod (ModuleCat.Hom.hom
      (TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ))) ≅ ModuleCat.of ℤ ℤ)) :
    Nonempty ((relChains X A).homology 1 ≅ ModuleCat.of ℤ ℤ) := by
  haveI := hε
  -- `H₁(X,A)` is the kernel of the map induced by the inclusion on `H₀`
  obtain ⟨e1⟩ := relHomologyOne_iso_kernel X A h1
  -- that map is `ε_A` followed by the inverse of `ε_X`, hence has the kernel of `ε_A`
  have hcomp : HomologicalComplex.homologyMap (inclChains X A) 0 ≫
      (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)) =
      TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ) :=
    epsilonNaturality (TopCat.of A) X (subtypeIncl X A)
  have e2 : kernel (HomologicalComplex.homologyMap (inclChains X A) 0) ≅
      kernel (TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ)) :=
    (IsLimit.conePointUniqueUpToIso
      (kernel.ofCompIso (f := TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ))
        (HomologicalComplex.homologyMap (inclChains X A) 0)
        (asIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ))) hcomp)
      (limit.isLimit _)).symm
  obtain ⟨hA⟩ := hA
  exact ⟨e1 ≪≫ e2 ≪≫ ModuleCat.kernelIsoKer
      (TopCat.singularHomology₀ε (TopCat.of A) (ModuleCat.of ℤ ℤ)) ≪≫
    moduleCatOfIsoOfEq ≪≫ hA⟩

/-- **The top local homology of `ℝⁿ` at the origin is `ℤ`** (`n ≥ 1`). -/
theorem euclideanLocalHomologyTop (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (((relChains (TopCat.of (EuclideanSpace ℝ (Fin n)))
      {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}).homology n) ≅ ModuleCat.of ℤ ℤ) := by
  rcases n with _ | n'
  · omega
  rcases n' with _ | k
  · -- `n = 1`: `H₁` of the pair is the reduced `H₀` of the two point space `ℝ ∖ {0}`
    have h1z : IsZero
        ((singularChains ℤ (TopCat.of (EuclideanSpace ℝ (Fin 1)))).homology 1) :=
      homologyContractible 1 (by norm_num)
    refine relH1OfPairAux (TopCat.of (EuclideanSpace ℝ (Fin 1)))
      {v : EuclideanSpace ℝ (Fin 1) | v ≠ 0} h1z inferInstance ?_
    -- the punctured space is homotopy equivalent to `S⁰`, whose reduced `H₀` is `ℤ`
    obtain ⟨eH⟩ := ker_eps_homotopyEquiv
      (Classical.choice (punctured_homotopyEquiv_sphere (EuclideanSpace ℝ (Fin 1))))
    obtain ⟨eS⟩ := ker_eps_homotopyEquiv (sphereInUnitHomeomorph 1).toHomotopyEquiv
    obtain ⟨e4⟩ := reducedH0SphereInUnitOne
    exact ⟨eH ≪≫ eS.symm ≪≫ moduleCatOfIsoOfEq ≪≫ e4⟩
  · -- `n = k + 2 ≥ 2`: the connecting map is an isomorphism onto `H_{k+1}(S^{k+1}) ≅ ℤ`
    haveI : ContractibleSpace (TopCat.of (EuclideanSpace ℝ (Fin (k + 1 + 1)))) := inferInstance
    have hz1 : IsZero ((singularChains ℤ
        (TopCat.of (EuclideanSpace ℝ (Fin (k + 1 + 1))))).homology (k + 1 + 1)) :=
      homologyContractible (k + 1 + 1) (by omega)
    have hz0 : IsZero ((singularChains ℤ
        (TopCat.of (EuclideanSpace ℝ (Fin (k + 1 + 1))))).homology (k + 1)) :=
      homologyContractible (k + 1) (by omega)
    have hδ : IsZero ((singularChains ℤ
        (TopCat.of (EuclideanSpace ℝ (Fin (k + 1 + 1))))).homology ((k + 1) + 1)) := hz1
    haveI hiso : IsIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin (k + 1 + 1))))
        {v : EuclideanSpace ℝ (Fin (k + 1 + 1)) | v ≠ 0} (k + 1)) :=
      hPairδ_isIso _ _ _ hδ hz0
    have he := Classical.choice (punctured_homotopyEquiv_sphere
      (EuclideanSpace ℝ (Fin (k + 1 + 1))))
    refine ⟨asIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin (k + 1 + 1))))
        {v : EuclideanSpace ℝ (Fin (k + 1 + 1)) | v ≠ 0} (k + 1))
      ≪≫ Classical.choice (homologyIso_of_homotopyEquiv he (k + 1)) ≪≫ ?_⟩
    -- and `H_{k+1}(S^{k+1}) ≅ ℤ`
    exact Classical.choice (sphereHomologyTop (k + 1) (by omega))

end

end Work.Cohomology
