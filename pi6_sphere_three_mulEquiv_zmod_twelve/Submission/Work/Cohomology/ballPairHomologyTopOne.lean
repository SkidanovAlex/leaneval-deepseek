import Mathlib
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.diskPairHomologyTopOne

set_option synthInstance.maxHeartbeats 400000

/-!
# The top relative homology of a punctured open interval

Let `y : ℝ¹`, `r > 0`, `X = B(y,r) ⊆ ℝ¹` the open ball (an open interval, hence contractible) and
`A = X ∖ {y} ⊆ X`, a two point space.  The first relative singular homology of the pair `(X,A)` is
`ℤ`: it is the `n = 1` instance of the classical computation `Hₙ(Dⁿ, Sⁿ⁻¹) ≅ ℤ`.

The proof is the one of `Submission/Work/Cohomology/diskPairHomologyTopOne.lean`, with the closed
unit ball replaced by the open ball `B(y,r)` and the unit sphere by the two point space
`S⁰ = Metric.sphere (0 : ℝ¹) 1`:

* `X` is a nonempty convex subset of `ℝ¹`, hence contractible, so `H₁(X) = 0`
  (`Work.Cohomology.homologyContractible`) and the augmentation `ε_X` is invertible;
* consequently the long exact sequence of the pair exhibits `H₁(X,A)` as the kernel of
  `H₀(A) ⟶ H₀(X)` (`Work.Cohomology.relHomologyOne_iso_kernel`);
* by naturality of the augmentation (`Work.Cohomology.epsilonNaturality`) that map is
  `ε_A ≫ ε_X⁻¹`, so its kernel is the kernel of `ε_A`, i.e. the reduced `H₀` of `A`;
* `A` is homotopy equivalent to `S⁰` (`e`), the reduced `H₀` is a homotopy invariant
  (`Work.Cohomology.ker_eps_homotopyEquiv`), and the reduced `H₀` of `S⁰` is `ℤ`
  (`Work.Cohomology.reducedH0SphereInUnitOne`, transported along `sphereInUnitHomeomorph`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **A pair with vanishing `H₁` and reduced `H₀` of the subspace equal to `ℤ` has `H₁(X,A) = ℤ`.**

If `H₁(X) = 0` and the augmentation `ε_X : H₀(X) ⟶ ℤ` is invertible (as for a contractible `X`),
then the connecting map of the pair identifies `H₁(X,A)` with `ker ε_A`, the reduced zeroth
homology of `A`. -/
theorem relH1OfPair (X : TopCat) (A : Set X)
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

/-- **The top relative homology of a punctured open interval is `ℤ`.**

Let `y : EuclideanSpace ℝ (Fin 1)`, `r > 0`, `X = TopCat.of (Metric.ball y r)` (an open interval,
hence contractible) and `A = {z : Metric.ball y r | (z : ℝ¹) ≠ y} ⊆ X`.  Given a homotopy
equivalence of `A` with the two point space `S⁰ = Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1`
(for instance the `n = 1` case of `Work.Cohomology.puncturedBallSphere`, to be proved in
`Submission/Work/Cohomology/puncturedBallSphere.lean`), the first relative singular homology of
the pair is `ℤ`.

Suggested route: `H₁(X) = 0` because `X` is contractible (`Work.Cohomology.homologyContractible`),
so `Work.Cohomology.relHomologyOne_iso_kernel` identifies `H₁(X,A)` with the kernel of
`H₀(A) ⟶ H₀(X)` (see `Submission/Work/Cohomology/diskPairHomologyTopOne.lean` for exactly this
style of argument); by naturality of the augmentation (`Work.Cohomology.epsilonNaturality`) and
invertibility of `ε_X` (contractible `X`) this kernel is the kernel of the augmentation of `A`,
i.e. the reduced `H₀` of a two point space.  For the latter use
`Work.Cohomology.ker_eps_homotopyEquiv` together with
`Work.Cohomology.reducedH0SphereInUnitOne` (the reduced `H₀` of `sphereInUnit 1`) and
`Work.Cohomology.sphereInUnitHomeomorph`, converting between `kerMod` and
`ModuleCat.of ℤ ↥(LinearMap.ker ·)` via `Work.Cohomology.ofKerIsoKerMod`.
(Do NOT import `Submission.Work.Cohomology.reducedH0SphereOne`: its helper names clash with
`reducedH0SphereInUnitOne`, which is already pulled in through `localHomology`.) -/
theorem ballPairHomologyTopOne (y : EuclideanSpace ℝ (Fin 1)) (r : ℝ) (hr : 0 < r)
    (e : ContinuousMap.HomotopyEquiv
      {z : Metric.ball y r // (z : EuclideanSpace ℝ (Fin 1)) ≠ y}
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) :
    Nonempty ((relChains (TopCat.of (Metric.ball y r))
      {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin 1)) ≠ y}).homology 1
        ≅ ModuleCat.of ℤ ℤ) := by
  -- the open ball is a nonempty convex subset of `ℝ¹`, hence contractible
  haveI hc : ContractibleSpace (TopCat.of (Metric.ball y r)) :=
    Convex.contractibleSpace (convex_ball y r) ⟨y, Metric.mem_ball_self hr⟩
  refine relH1OfPair (TopCat.of (Metric.ball y r))
    {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin 1)) ≠ y}
    (homologyContractible 1 (by norm_num)) inferInstance ?_
  -- the punctured ball is homotopy equivalent to `S⁰`, and the reduced `H₀` of `S⁰` is `ℤ`
  obtain ⟨eH⟩ := ker_eps_homotopyEquiv e
  obtain ⟨eS⟩ := ker_eps_homotopyEquiv (sphereInUnitHomeomorph 1).toHomotopyEquiv
  obtain ⟨e4⟩ := reducedH0SphereInUnitOne
  exact ⟨eH ≪≫ eS.symm ≪≫ moduleCatOfIsoOfEq ≪≫ e4⟩

end

end Work.Cohomology
